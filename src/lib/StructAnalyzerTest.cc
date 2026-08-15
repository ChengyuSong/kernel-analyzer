/*
 * Unit tests for StructAnalyzer.
 *
 * Builds struct types directly against a fixed DataLayout and checks the
 * expansion invariants, including regressions for the 2026-07-03 fixes:
 *   1. elementType indexing for nested structs
 *   2. fieldRealSize one-entry-per-expanded-slot (incl. unions)
 *   3. fieldOffset alignment with zero-size and empty members
 *   4. container map (direct + transitive) and getContainer semantics
 *
 * Run: release/lib/StructAnalyzerTest ; exit code = number of failures.
 */

#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/Constants.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/raw_ostream.h>

#include "StructAnalyzer.h"
#include "Annotation.h"

using namespace llvm;

// Satisfy the extern in Flags.h (KA_LOG); tests run silently.
cl::opt<unsigned> VerboseLevel("verbose", cl::init(0));
cl::opt<bool> LogTimestamps("log-timestamps", cl::init(false));

static int failures = 0;
#define CHECK(cond)                                                          \
  do {                                                                       \
    if (!(cond)) {                                                           \
      errs() << "FAIL @" << __LINE__ << ": " #cond "\n";                     \
      failures++;                                                            \
    }                                                                        \
  } while (0)

static GlobalVariable *anchor(Module &M, StructType *ST, const char *name) {
  // TypeFinder only visits used types; anchor each struct with a global.
  return new GlobalVariable(M, ST, false, GlobalValue::ExternalLinkage,
                            ConstantAggregateZero::get(ST), name);
}

// Every per-expanded-slot vector must have exactly expandedSize entries and
// offsets must be non-decreasing.
static void checkSlotInvariants(const StructInfo *SI, const char *what) {
  CHECK(SI != nullptr);
  if (!SI)
    return;
  unsigned n = SI->getExpandedSize();
  if (SI->getNumFieldOffsets() != n)
    errs() << "FAIL(" << what << "): fieldOffset size "
           << SI->getNumFieldOffsets() << " != expanded " << n << "\n",
        failures++;
  if (SI->getNumFieldRealSizes() != n)
    errs() << "FAIL(" << what << "): fieldRealSize size "
           << SI->getNumFieldRealSizes() << " != expanded " << n << "\n",
        failures++;
  for (unsigned i = 0; i + 1 < n && i + 1 < SI->getNumFieldOffsets(); i++)
    CHECK(SI->getFieldOffset(i) <= SI->getFieldOffset(i + 1));
}

int main() {
  LLVMContext Ctx;
  Module M("sa_test", Ctx);
  M.setDataLayout("e-m:e-p:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128");
  const DataLayout &DL = M.getDataLayout();

  Type *I8 = Type::getInt8Ty(Ctx);
  Type *I32 = Type::getInt32Ty(Ctx);
  Type *I64 = Type::getInt64Ty(Ctx);
  Type *Ptr = PointerType::get(Ctx, 0);

  // -- simple: { i32, ptr, [4 x ptr] }
  auto *Simple =
      StructType::create(Ctx, {I32, Ptr, ArrayType::get(Ptr, 4)},
                         "struct.sa_simple");
  // -- nested: inner { ptr, i32 }, outer { i32, inner, ptr }
  auto *Inner = StructType::create(Ctx, {Ptr, I32}, "struct.sa_inner");
  auto *Outer = StructType::create(Ctx, {I32, Inner, Ptr}, "struct.sa_outer");
  // -- zero-size member: zs { [0 x i8], i64, ptr }, zouter { zs, ptr }
  auto *ZS = StructType::create(Ctx, {ArrayType::get(I8, 0), I64, Ptr},
                                "struct.sa_zs");
  auto *ZOuter = StructType::create(Ctx, {ZS, Ptr}, "struct.sa_zouter");
  // -- empty member: empty {}, eouter { empty, ptr }
  auto *Empty = StructType::create(Ctx, {}, "struct.sa_empty");
  auto *EOuter = StructType::create(Ctx, {Empty, Ptr}, "struct.sa_eouter");
  // -- union (clang-style representative member): union.u { ptr }
  auto *U = StructType::create(Ctx, {Ptr}, "union.sa_u");
  auto *UOuter = StructType::create(Ctx, {I32, U}, "struct.sa_uouter");
  // -- transitive containers: mid { i32, inner }, top { i64, mid }
  auto *Mid = StructType::create(Ctx, {I32, Inner}, "struct.sa_mid");
  auto *Top = StructType::create(Ctx, {I64, Mid}, "struct.sa_top");

  for (auto *ST : {Simple, Outer, ZOuter, EOuter, UOuter, Top})
    anchor(M, ST, ("g_" + ST->getName().str()).c_str());

  StructAnalyzer SA;
  SA.run(&M, &DL);

  const StructInfo *SSimple = SA.getStructInfo(Simple, &M);
  const StructInfo *SInner = SA.getStructInfo(Inner, &M);
  const StructInfo *SOuter = SA.getStructInfo(Outer, &M);
  const StructInfo *SZS = SA.getStructInfo(ZS, &M);
  const StructInfo *SZOuter = SA.getStructInfo(ZOuter, &M);
  const StructInfo *SEOuter = SA.getStructInfo(EOuter, &M);
  const StructInfo *SU = SA.getStructInfo(U, &M);
  const StructInfo *STop = SA.getStructInfo(Top, &M);

  for (auto p : {std::make_pair(SSimple, "simple"), {SInner, "inner"},
                 {SOuter, "outer"}, {SZS, "zs"}, {SZOuter, "zouter"},
                 {SEOuter, "eouter"}, {SU, "union"}, {STop, "top"}})
    checkSlotInvariants(p.first, p.second);

  // simple: layout i32@0, ptr@8, [4 x ptr]@16
  CHECK(SSimple->getExpandedSize() == 3);
  CHECK(SSimple->getSize() == 3);
  CHECK(SSimple->getOffset(0) == 0 && SSimple->getOffset(1) == 1 &&
        SSimple->getOffset(2) == 2);
  CHECK(!SSimple->isFieldPointer(0) && SSimple->isFieldPointer(1));
  CHECK(SSimple->isFieldArray(2) && SSimple->isFieldPointer(2));
  CHECK(SSimple->getFieldOffset(1) == 8 && SSimple->getFieldOffset(2) == 16);
  CHECK(SSimple->getFieldRealSize(2) == 32); // 4 * 8

  // outer: slots 0:i32@0  1:inner.ptr@8  2:inner.i32@16  3:ptr@24
  CHECK(SOuter->getExpandedSize() == 4);
  CHECK(SOuter->getOffset(0) == 0 && SOuter->getOffset(1) == 1 &&
        SOuter->getOffset(2) == 3);
  CHECK(SOuter->getFieldOffset(0) == 0 && SOuter->getFieldOffset(1) == 8 &&
        SOuter->getFieldOffset(2) == 16 && SOuter->getFieldOffset(3) == 24);
  CHECK(SOuter->getFieldRealSize(1) == 8 && SOuter->getFieldRealSize(2) == 4);
  CHECK(SOuter->isFieldPointer(1) && !SOuter->isFieldPointer(2) &&
        SOuter->isFieldPointer(3));
  // regression (fix 1): nested element types at the right expanded slots
  CHECK(SOuter->getElementType(1).count(Inner) == 1); // struct itself at slot 1
  CHECK(SOuter->getElementType(2).count(I32) == 1);   // inner.i32 at slot 2
  CHECK(SOuter->getElementType(3).count(Ptr) == 1);

  // zouter: zs expands to 3 slots with offsets [0,0,8]; zouter adds ptr@16
  // regression (fix 3): index-based skip keeps both zero-offset entries
  CHECK(SZS->getExpandedSize() == 3);
  CHECK(SZS->getFieldOffset(0) == 0 && SZS->getFieldOffset(1) == 0 &&
        SZS->getFieldOffset(2) == 8);
  CHECK(SZOuter->getExpandedSize() == 4);
  CHECK(SZOuter->getFieldOffset(1) == 0 && SZOuter->getFieldOffset(2) == 8 &&
        SZOuter->getFieldOffset(3) == 16);

  // eouter: empty member contributes no expanded slot and no offset entry
  CHECK(SEOuter->getExpandedSize() == 1);
  CHECK(SEOuter->getFieldOffset(0) == 0 && SEOuter->isFieldPointer(0));
  CHECK(SEOuter->getOffset(0) == 0 && SEOuter->getOffset(1) == 0);

  // union: one collapsed slot with a real size (fix 2)
  CHECK(SU->getExpandedSize() == 1 && SU->isFieldUnion(0));
  CHECK(SU->getFieldRealSize(0) == DL.getTypeAllocSize(U));

  // containers: direct and transitive (inner in mid@8, mid in top@8 =>
  // inner in top@16); union member registration
  CHECK(SInner->getContainer(Outer, 8) == Outer);
  CHECK(SInner->getContainer(Outer, 0) == nullptr);
  CHECK(SInner->getContainer(Mid, 8) == Mid);
  CHECK(SInner->getContainer(Top, 16) == Top);
  CHECK(SU->getContainer(UOuter, 8) == UOuter);

  // StructAnalyzer::getContainer by scope name; false + empty out when the
  // struct has no containers (fix 4)
  std::set<std::string> out;
  CHECK(SA.getContainer(getScopeName(Inner, &M), &M, out));
  CHECK(out.count("struct.sa_outer") && out.count("struct.sa_mid") &&
        out.count("struct.sa_top"));
  out.clear();
  CHECK(!SA.getContainer(getScopeName(Top, &M), &M, out));
  CHECK(out.empty());

  if (failures == 0)
    outs() << "StructAnalyzerTest: all checks passed\n";
  else
    outs() << "StructAnalyzerTest: " << failures << " failure(s)\n";
  return failures;
}
