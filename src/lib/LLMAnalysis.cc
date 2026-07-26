/*
 * LLM-based analysis for allocator and container function identification
 *
 * Copyright (C) 2026 Chengyu Song
 *
 * For licensing details see LICENSE
 */

#include <llvm/ADT/ArrayRef.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/ADT/StringSet.h>
#include <llvm/Support/Error.h>
#include <llvm/Support/JSON.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/raw_ostream.h>

#include <cstdio>
#include <fstream>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "LLMAnalysis.h"
#include "Global.h"
#include "Annotation.h"
#include "LLMClient.h"
#include <llvm/Support/CommandLine.h>

#define LLM_LOG(stmt) KA_LOG(2, "LLMAnalysis: " << stmt)
#define LLM_DEBUG(stmt) KA_LOG(3, "LLMAnalysis: " << stmt)

using namespace llvm;

// Process a single LLM response for allocator candidates.  Returns the
// number of newly added candidates.
static size_t processAllocatorResponse(GlobalContext *Ctx,
                                       StringRef RespText,
                                       ArrayRef<Function *> Batch) {
  size_t Added = 0;

  // Try to parse as JSON first.
  bool ParsedJSON = false;
  Expected<json::Value> Parsed =
      json::parse(LLMClient::stripMarkdownFence(RespText));
  if (Parsed) {
    const json::Array *Candidates = nullptr;
    if (const json::Object *Obj = Parsed->getAsObject()) {
      Candidates = Obj->getArray("candidates");
      if (!Candidates)
        Candidates = Obj->getArray("functions");
    } else {
      Candidates = Parsed->getAsArray();
    }
    if (Candidates) {
      ParsedJSON = true;
      for (const json::Value &V : *Candidates) {
        auto Name = V.getAsString();
        if (!Name)
          continue;
        for (Function *F : Batch) {
          if (F->getName() == *Name &&
              Ctx->AllocFuncs.count(F) == 0 &&
              Ctx->CandidateAllocFuncs.insert(F).second) {
            Added++;
          }
        }
      }
    }
  } else {
    consumeError(Parsed.takeError());
  }

  // Fallback: scan raw text for known function names from the batch.
  if (!ParsedJSON) {
    WARNING("LLM response is not valid JSON, falling back to text matching\n");
    for (Function *F : Batch) {
      StringRef Name = F->getName();
      size_t Pos = 0;
      while ((Pos = RespText.find(Name, Pos)) != StringRef::npos) {
        bool LeftOk = (Pos == 0) ||
                      (!isAlnum(RespText[Pos - 1]) && RespText[Pos - 1] != '_');
        size_t End = Pos + Name.size();
        bool RightOk = (End >= RespText.size()) ||
                       (!isAlnum(RespText[End]) && RespText[End] != '_');
        if (LeftOk && RightOk) {
          if (Ctx->AllocFuncs.count(F) == 0 &&
              Ctx->CandidateAllocFuncs.insert(F).second) {
            Added++;
          }
          break;
        }
        Pos = End;
      }
    }
  }
  return Added;
}

// Try to repair truncated JSON by closing open brackets/braces.
// LLM responses often get cut off when the token limit is too small.
static std::string repairTruncatedJSON(StringRef Text) {
  std::string S = Text.str();

  // Strip trailing partial tokens: find the last complete JSON element
  // by looking for the last '}' or ']' that could end an entry.
  // Then close any remaining open brackets/braces.
  int openBraces = 0, openBrackets = 0;
  bool inString = false;
  char prev = 0;
  for (char c : S) {
    if (inString) {
      if (c == '"' && prev != '\\')
        inString = false;
    } else {
      switch (c) {
        case '"': inString = true; break;
        case '{': openBraces++; break;
        case '}': openBraces--; break;
        case '[': openBrackets++; break;
        case ']': openBrackets--; break;
      }
    }
    prev = c;
  }

  // If we're inside a string, close it
  if (inString)
    S += '"';

  // Close open braces/brackets in LIFO order by scanning again
  // Simple approach: just append the needed closers
  // First close any open brace (partial object), then brackets, then remaining braces
  // We re-count after possible string close
  openBraces = 0; openBrackets = 0; inString = false; prev = 0;
  for (char c : S) {
    if (inString) {
      if (c == '"' && prev != '\\') inString = false;
    } else {
      switch (c) {
        case '"': inString = true; break;
        case '{': openBraces++; break;
        case '}': openBraces--; break;
        case '[': openBrackets++; break;
        case ']': openBrackets--; break;
      }
    }
    prev = c;
  }

  // Close in reverse nesting order (inner to outer)
  // Typical truncated pattern: {"containers":[{...},{...  or {"containers":[{...},
  // We need to close: any open object, then the array, then the outer object
  while (openBraces > 0) { S += '}'; openBraces--; }
  while (openBrackets > 0) { S += ']'; openBrackets--; }

  return S;
}

static size_t processContainerResponse(GlobalContext *Ctx,
                                       StringRef RespText,
                                       ArrayRef<Function *> Batch) {
  size_t Added = 0;

  std::string Stripped = LLMClient::stripMarkdownFence(RespText);
  Expected<json::Value> Parsed = json::parse(Stripped);
  if (!Parsed) {
    consumeError(Parsed.takeError());
    // Try to repair truncated JSON (common when MaxTok is too small)
    std::string Repaired = repairTruncatedJSON(Stripped);
    Parsed = json::parse(Repaired);
    if (!Parsed) {
      consumeError(Parsed.takeError());
      WARNING("LLM container response is not valid JSON (even after repair), skipping\n");
      return 0;
    }
    WARNING("LLM container response was truncated, repaired JSON for partial results\n");
  }

  const json::Object *Obj = Parsed->getAsObject();
  if (!Obj)
    return 0;
  const json::Array *Containers = Obj->getArray("containers");
  if (!Containers)
    return 0;

  for (const json::Value &V : *Containers) {
    const json::Object *Entry = V.getAsObject();
    if (!Entry)
      continue;

    auto NameVal = Entry->getString("name");
    if (!NameVal)
      continue;
    StringRef Name = *NameVal;

    // Find the matching function in this batch
    Function *MatchF = nullptr;
    for (Function *F : Batch) {
      if (F->getName() == Name) {
        MatchF = F;
        break;
      }
    }
    if (!MatchF || Ctx->ContainerFuncs.count(MatchF))
      continue;

    auto ContainerArgVal = Entry->getInteger("container_arg");
    if (!ContainerArgVal)
      continue;
    int containerArg = (int)*ContainerArgVal;

    // Validate container_arg index and pointer type
    if (containerArg < 0 || (unsigned)containerArg >= MatchF->arg_size())
      continue;
    if (!MatchF->getArg(containerArg)->getType()->isPointerTy())
      continue;

    // Parse store_args
    std::vector<int> storeArgs;
    if (const json::Array *SA = Entry->getArray("store_args")) {
      for (const json::Value &SV : *SA) {
        auto idx = SV.getAsInteger();
        if (!idx)
          continue;
        int si = (int)*idx;
        if (si < 0 || (unsigned)si >= MatchF->arg_size())
          continue;
        if (!MatchF->getArg(si)->getType()->isPointerTy())
          continue;
        storeArgs.push_back(si);
      }
    }

    // Parse load_return
    bool loadReturn = false;
    if (auto LR = Entry->getBoolean("load_return"))
      loadReturn = *LR;

    // Validate: if load_return is true, function must return a pointer
    if (loadReturn && !MatchF->getReturnType()->isPointerTy())
      loadReturn = false;

    // Must have at least one store_arg or load_return to be useful
    if (storeArgs.empty() && !loadReturn)
      continue;

    GlobalContext::ContainerFuncInfo Info;
    Info.containerArg = containerArg;
    Info.storeArgs = std::move(storeArgs);
    Info.loadReturn = loadReturn;
    Ctx->ContainerFuncs[MatchF] = std::move(Info);
    Added++;

    LLM_LOG("Container function: " << Name
           << " container_arg=" << containerArg
           << " store_args=[");
    for (size_t i = 0; i < Ctx->ContainerFuncs[MatchF].storeArgs.size(); i++) {
      if (i > 0) LLM_LOG(",");
      LLM_LOG(Ctx->ContainerFuncs[MatchF].storeArgs[i]);
    }
    LLM_LOG("] load_return=" << (Ctx->ContainerFuncs[MatchF].loadReturn ? "true" : "false") << "\n");
  }

  return Added;
}

void queryAllocatorCandidates(GlobalContext *Ctx, LLMClient *LLM, Module *M) {
  if (!LLM)
    return;

  // Collect pointer-returning functions from this module
  std::vector<Function *> PtrReturnFuncs;
  for (Function &F : *M) {
    if (F.isDeclaration() || F.isIntrinsic() || F.empty())
      continue;
    int size = 0, flag = 0;
    if (isAllocFn(F.getName(), &size, &flag))
      continue;
    if (Ctx->AllocFuncs.count(&F))
      continue;
    if (F.getReturnType()->isPointerTy())
      PtrReturnFuncs.push_back(&F);
  }

  if (PtrReturnFuncs.empty())
    return;

  const StringRef SystemPrompt =
      "You classify allocator-like functions conservatively.";

  // Process PtrReturnFuncs in batches to stay within the LLM context window.
  const unsigned BatchSize = 100;
  size_t TotalAdded = 0;
  unsigned NumBatches =
      (PtrReturnFuncs.size() + BatchSize - 1) / BatchSize;

  for (unsigned B = 0; B < NumBatches; ++B) {
    unsigned Begin = B * BatchSize;
    unsigned End = std::min(Begin + BatchSize, (unsigned)PtrReturnFuncs.size());
    ArrayRef<Function *> Batch(&PtrReturnFuncs[Begin], End - Begin);

    std::string UserPrompt;
    raw_string_ostream PromptOS(UserPrompt);
    PromptOS << "Given function declarations only (no bodies), identify likely "
                "custom allocator functions.\n";
    PromptOS << "Return strict JSON only in this format: "
                "{\"candidates\":[\"func_name1\",\"func_name2\"]}\n";
    PromptOS << "Only include names from the provided list.\n\n";
    PromptOS << "Declarations:\n";
    for (const Function *F : Batch) {
      std::string FuncTy;
      raw_string_ostream FOS(FuncTy);
      FOS << *F->getFunctionType();
      FOS.flush();
      PromptOS << "- " << F->getName() << " : " << FuncTy << "\n";
    }
    PromptOS.flush();

    LLM_DEBUG("LLM allocator query batch " << B + 1 << "/" << NumBatches
             << " (" << Batch.size() << " functions)\n");
    LLM_DEBUG("LLM allocator query user prompt:\n" << UserPrompt << "\n");

    // Estimate token budget for the response.
    unsigned MaxTok = std::max(512u, (unsigned)Batch.size() * 5 + 50);
    // Scale timeout: ~1 second per 10 tokens, minimum 30s.
    unsigned Timeout = std::max(30u, MaxTok / 10);
    auto RespText = LLM->requestText(SystemPrompt, UserPrompt, MaxTok, Timeout);
    if (!RespText) {
      WARNING("LLM allocator candidate query batch " << B + 1
              << " failed: " << toString(RespText.takeError()) << "\n");
      continue;
    }
    LLM_DEBUG("LLM allocator response (batch " << B + 1 << "):\n"
             << *RespText << "\n");

    TotalAdded += processAllocatorResponse(Ctx, *RespText, Batch);
  }
  LLM_LOG("LLM added " << TotalAdded << " candidate allocator(s) ("
         << NumBatches << " batch(es))\n");
}

void queryContainerCandidates(GlobalContext *Ctx, LLMClient *LLM, Module *M) {
  if (!LLM)
    return;

  // Collect container function candidates from this module
  std::vector<Function *> ContainerCandidateFuncs;
  for (Function &F : *M) {
    if (F.isDeclaration() || F.isIntrinsic() || F.empty())
      continue;
    int size = 0, flag = 0;
    if (isAllocFn(F.getName(), &size, &flag))
      continue;
    if (Ctx->AllocFuncs.count(&F))
      continue;

    unsigned ptrParams = 0;
    for (auto &arg : F.args())
      if (arg.getType()->isPointerTy())
        ptrParams++;
    bool ptrReturn = F.getReturnType()->isPointerTy();
    if (ptrParams >= 2 || (ptrParams >= 1 && ptrReturn))
      ContainerCandidateFuncs.push_back(&F);
  }

  if (ContainerCandidateFuncs.empty())
    return;

  const StringRef SystemPrompt =
      "You identify container/collection functions that store and retrieve "
      "pointer values. Examples: hash table insert/find, list add/remove, "
      "tree insert/search, map put/get, queue push/pop, cache store/fetch.";

  const unsigned BatchSize = 50;
  size_t TotalAdded = 0;
  unsigned NumBatches =
      (ContainerCandidateFuncs.size() + BatchSize - 1) / BatchSize;

  for (unsigned B = 0; B < NumBatches; ++B) {
    unsigned Begin = B * BatchSize;
    unsigned End = std::min(Begin + BatchSize,
                            (unsigned)ContainerCandidateFuncs.size());
    ArrayRef<Function *> Batch(&ContainerCandidateFuncs[Begin], End - Begin);

    std::string UserPrompt;
    raw_string_ostream PromptOS(UserPrompt);
    PromptOS << "Given function declarations, identify container/collection "
                "functions that store or retrieve pointer values (hash tables, "
                "linked lists, trees, maps, caches, queues, etc.).\n\n";
    PromptOS << "For each container function, specify:\n";
    PromptOS << "- name: function name\n";
    PromptOS << "- container_arg: 0-based index of the container object parameter\n";
    PromptOS << "- store_args: list of 0-based indices of value parameters stored INTO the container\n";
    PromptOS << "- load_return: true if the return value is loaded FROM the container\n\n";
    PromptOS << "Return strict JSON only:\n";
    PromptOS << "{\"containers\":[\n";
    PromptOS << "  {\"name\":\"func\",\"container_arg\":0,\"store_args\":[2],\"load_return\":false}\n";
    PromptOS << "]}\n";
    PromptOS << "If no container functions are found, return {\"containers\":[]}.\n";
    PromptOS << "ONLY return possible container functions from the provided list.\n";
    PromptOS << "Do NOT hallucinate functions that are not in the list.\n";
    PromptOS << "Do NOT return non container functions.\n\n";
    PromptOS << "Declarations:\n";
    for (const Function *F : Batch) {
      std::string FuncTy;
      raw_string_ostream FOS(FuncTy);
      FOS << *F->getFunctionType();
      FOS.flush();
      PromptOS << "- " << F->getName() << " : " << FuncTy << "\n";
    }
    PromptOS.flush();

    LLM_DEBUG("LLM container query batch " << B + 1 << "/" << NumBatches
             << " (" << Batch.size() << " functions)\n");

    // Each container entry is ~80-100 tokens of JSON, so budget generously
    unsigned MaxTok = std::max(2048u, (unsigned)Batch.size() * 100 + 200);
    unsigned Timeout = std::max(60u, MaxTok / 10);
    auto RespText = LLM->requestText(SystemPrompt, UserPrompt, MaxTok, Timeout);
    if (!RespText) {
      WARNING("LLM container candidate query batch " << B + 1
              << " failed: " << toString(RespText.takeError()) << "\n");
      continue;
    }
    LLM_DEBUG("LLM container response (batch " << B + 1 << "):\n"
             << *RespText << "\n");

    TotalAdded += processContainerResponse(Ctx, *RespText, Batch);
  }
  LLM_LOG("LLM added " << TotalAdded << " container function(s) ("
         << NumBatches << " batch(es))\n");
}

bool saveAllocatorResults(GlobalContext *Ctx, StringRef Path) {
  std::error_code EC;
  raw_fd_ostream OS(Path, EC);
  if (EC) {
    WARNING("Failed to open allocator file for writing: " << Path << ": " << EC.message() << "\n");
    return false;
  }

  StringSet<> Seen;
  json::Array Candidates;
  for (const Function *F : Ctx->CandidateAllocFuncs)
    if (Seen.insert(F->getName()).second)
      Candidates.push_back(F->getName().str());

  Seen.clear();
  json::Array Confirmed;
  for (const Function *F : Ctx->AllocFuncs)
    if (Seen.insert(F->getName()).second)
      Confirmed.push_back(F->getName().str());

  json::Object Root;
  Root["candidates"] = std::move(Candidates);
  Root["confirmed"] = std::move(Confirmed);
  OS << json::Value(std::move(Root)) << "\n";
  LLM_LOG("Saved " << Ctx->CandidateAllocFuncs.size()
         << " allocator candidate(s) and " << Ctx->AllocFuncs.size()
         << " confirmed allocator(s) to " << Path << "\n");
  return true;
}

bool saveContainerResults(GlobalContext *Ctx, StringRef Path) {
  std::error_code EC;
  raw_fd_ostream OS(Path, EC);
  if (EC) {
    WARNING("Failed to open container file for writing: " << Path << ": " << EC.message() << "\n");
    return false;
  }

  json::Array Containers;
  for (auto &[F, Info] : Ctx->ContainerFuncs) {
    json::Object Entry;
    Entry["name"] = F->getName().str();
    Entry["container_arg"] = Info.containerArg;
    json::Array SA;
    for (int idx : Info.storeArgs)
      SA.push_back(idx);
    Entry["store_args"] = std::move(SA);
    Entry["load_return"] = Info.loadReturn;
    Containers.push_back(std::move(Entry));
  }

  json::Object Root;
  Root["containers"] = std::move(Containers);
  OS << json::Value(std::move(Root)) << "\n";
  LLM_LOG("Saved " << Ctx->ContainerFuncs.size()
         << " container function(s) to " << Path << "\n");
  return true;
}

int loadAllocatorFile(GlobalContext *Ctx, StringRef Path) {
  auto BufOrErr = MemoryBuffer::getFile(Path);
  if (!BufOrErr) {
    LLM_LOG("Allocator file not available: " << Path << ": "
            << BufOrErr.getError().message() << "\n");
    return 0;
  }

  if ((*BufOrErr)->getBufferSize() == 0) {
    LLM_LOG("Allocator file is empty: " << Path << "\n");
    return 0;
  }

  Expected<json::Value> Parsed = json::parse((*BufOrErr)->getBuffer());
  if (!Parsed) {
    WARNING("Failed to parse allocator JSON: " << toString(Parsed.takeError()) << "\n");
    return -1;
  }

  // Build name -> Function* map for lookup
  std::unordered_map<std::string, Function*> NameToFunc;
  for (auto &[id, F] : Ctx->Funcs)
    NameToFunc[F->getName().str()] = F;

  const json::Object *Obj = Parsed->getAsObject();
  if (!Obj) return -1;

  size_t LoadedCandidates = 0;
  if (const json::Array *Candidates = Obj->getArray("candidates")) {
    for (const json::Value &V : *Candidates) {
      auto Name = V.getAsString();
      if (!Name) continue;
      auto it = NameToFunc.find(Name->str());
      if (it == NameToFunc.end()) {
        LLM_DEBUG("Allocator candidate not found in module: " << *Name << "\n");
        continue;
      }
      if (Ctx->AllocFuncs.count(it->second) == 0 &&
          Ctx->CandidateAllocFuncs.insert(it->second).second)
        LoadedCandidates++;
    }
  }

  size_t LoadedConfirmed = 0;
  if (const json::Array *Confirmed = Obj->getArray("confirmed")) {
    for (const json::Value &V : *Confirmed) {
      auto Name = V.getAsString();
      if (!Name) continue;
      auto it = NameToFunc.find(Name->str());
      if (it == NameToFunc.end()) {
        LLM_DEBUG("Confirmed allocator not found in module: " << *Name << "\n");
        continue;
      }
      if (Ctx->AllocFuncs.insert(it->second).second)
        LoadedConfirmed++;
    }
  }

  LLM_LOG("Loaded " << LoadedCandidates << " allocator candidate(s) and "
         << LoadedConfirmed << " confirmed allocator(s) from " << Path << "\n");
  return 1;
}

int loadContainerFile(GlobalContext *Ctx, StringRef Path) {
  auto BufOrErr = MemoryBuffer::getFile(Path);
  if (!BufOrErr) {
    LLM_LOG("Container file not available: " << Path << ": "
            << BufOrErr.getError().message() << "\n");
    return 0;
  }

  if ((*BufOrErr)->getBufferSize() == 0) {
    LLM_LOG("Container file is empty: " << Path << "\n");
    return 0;
  }

  Expected<json::Value> Parsed = json::parse((*BufOrErr)->getBuffer());
  if (!Parsed) {
    WARNING("Failed to parse container JSON: " << toString(Parsed.takeError()) << "\n");
    return -1;
  }

  // Build name -> Function* map for lookup
  std::unordered_map<std::string, Function*> NameToFunc;
  for (auto &[id, F] : Ctx->Funcs)
    NameToFunc[F->getName().str()] = F;

  // Reuse processContainerResponse by constructing a batch from matched names
  const json::Object *Obj = Parsed->getAsObject();
  if (!Obj) return -1;
  const json::Array *Containers = Obj->getArray("containers");
  if (!Containers) return -1;

  // Collect matching functions for the batch
  std::vector<Function*> Batch;
  for (const json::Value &V : *Containers) {
    const json::Object *Entry = V.getAsObject();
    if (!Entry) continue;
    auto NameVal = Entry->getString("name");
    if (!NameVal) continue;
    auto it = NameToFunc.find(NameVal->str());
    if (it != NameToFunc.end())
      Batch.push_back(it->second);
  }

  // Re-serialize and process through existing handler
  std::string JsonStr;
  raw_string_ostream JsonOS(JsonStr);
  JsonOS << json::Value(std::move(*Parsed));
  JsonOS.flush();

  size_t Added = processContainerResponse(Ctx, JsonStr, Batch);
  LLM_LOG("Loaded " << Added << " container function(s) from " << Path << "\n");
  return 1;
}

// ---------------------------------------------------------------------------
// Kerneldoc-driven INVOKE mining (task #28 tier 3)
// ---------------------------------------------------------------------------

namespace {
struct KdocBlock {
  std::string File;
  unsigned Line = 0;
  std::vector<std::pair<std::string, std::string>> Params; // ordered
  std::string Text; // full block text
};
} // namespace

// Read the kerneldoc block around File:Line (the " * name - " header).
static bool readKdocBlock(StringRef Path, unsigned Line, KdocBlock &Out) {
  auto Buf = MemoryBuffer::getFile(Path);
  if (!Buf)
    return false;
  SmallVector<StringRef, 0> Lines;
  (*Buf)->getBuffer().split(Lines, '\n');
  if (Line == 0 || Line > Lines.size())
    return false;
  size_t I = Line - 1, Start = I, End = I;
  while (Start > 0 && !Lines[Start].contains("/**"))
    Start--;
  while (End < Lines.size() && !Lines[End].contains("*/"))
    End++;
  std::pair<std::string, std::string> *Cur = nullptr;
  for (size_t L = Start; L < End && L < Lines.size(); L++) {
    StringRef S = Lines[L].trim();
    Out.Text += S.str();
    Out.Text += "\n";
    if (!S.consume_front("*"))
      continue;
    S = S.ltrim();
    if (S.consume_front("@")) {
      auto [Name, Rest] = S.split(':');
      std::string N = Name.trim().str();
      std::string LowerN = StringRef(N).lower();
      if (LowerN == "return" || LowerN == "returns" || LowerN == "note" ||
          LowerN == "context") {
        Cur = nullptr;
        continue;
      }
      Out.Params.emplace_back(N, Rest.trim().str());
      Cur = &Out.Params.back();
    } else if (Cur && !S.empty()) {
      Cur->second += " ";
      Cur->second += S.str();
    } else {
      Cur = nullptr;
    }
  }
  return !Out.Params.empty();
}

static bool kdocHasCallbackIdiom(const KdocBlock &B) {
  static const char *Idioms[] = {
      "callback", "handler",   "called",      "invoked",  "cookie",
      "argument to", "passed to", "data passed", "private data", "opaque"};
  std::string Lower = StringRef(B.Text).lower();
  for (const char *I : Idioms)
    if (Lower.find(I) != std::string::npos)
      return true;
  return false;
}

void queryInvokeCandidates(GlobalContext *Ctx, LLMClient *LLM,
                           StringRef KernelSrc, StringRef OutPath,
                           bool DryRun) {
  if (!DryRun && !LLM) {
    WARNING("InvokeMine: no LLM client (use --llm-server-host/port, or "
            "--invoke-mine-dry)\n");
    return;
  }
  // Names already summarized: mining runs pre-pass, so read the
  // authoritative file directly (first token per non-comment line).
  std::unordered_set<std::string> Summarized;
  {
    extern cl::opt<std::string> FuncSummaryFile;
    std::ifstream In(FuncSummaryFile);
    std::string Line;
    while (std::getline(In, Line)) {
      StringRef L = StringRef(Line).trim();
      if (L.empty() || L.starts_with("#")) continue;
      StringRef Name = L.split(' ').first.rtrim("*");
      Summarized.insert(Name.str());
    }
  }
  // Corpus-defined functions eligible for a registration contract.
  std::unordered_map<std::string, Function *> Defined;
  for (auto &mp : Ctx->Modules)
    for (Function &F : *mp.first) {
      if (F.isDeclaration() || F.isIntrinsic() || F.empty())
        continue;
      if (F.arg_size() < 2)
        continue;
      bool HasPtr = false;
      for (auto &A : F.args())
        HasPtr |= A.getType()->isPointerTy();
      if (HasPtr)
        Defined.emplace(F.getName().str(), &F);
    }
  LLM_LOG("InvokeMine: " << Defined.size()
          << " defined candidate functions in corpus\n");

  // One grep pass over the kernel tree for kerneldoc headers.
  std::string Cmd =
      "grep -rnE --include=*.c --include=*.h "
      "'^[[:space:]]*\\*[[:space:]]*[a-zA-Z_][a-zA-Z0-9_]*[[:space:]]+-"
      "[[:space:]]' " +
      KernelSrc.str() + " 2>/dev/null";
  FILE *P = popen(Cmd.c_str(), "r");
  if (!P) {
    WARNING("InvokeMine: grep over kernel tree failed\n");
    return;
  }
  std::unordered_map<std::string, std::pair<std::string, unsigned>> Hits;
  {
    char *LinePtr = nullptr;
    size_t Cap = 0;
    ssize_t N;
    while ((N = getline(&LinePtr, &Cap, P)) > 0) {
      StringRef L(LinePtr, N);
      auto [FileName, Rest1] = L.split(':');
      auto [LineNo, Rest2] = Rest1.split(':');
      unsigned LN = 0;
      if (LineNo.getAsInteger(10, LN))
        continue;
      StringRef S = Rest2.trim();
      if (!S.consume_front("*"))
        continue;
      S = S.ltrim();
      auto NameEnd = S.find_first_not_of(
          "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_");
      std::string Name = S.substr(0, NameEnd).str();
      if (Name.empty() || !Defined.count(Name))
        continue;
      Hits.emplace(Name, std::make_pair(FileName.str(), LN)); // first wins
    }
    free(LinePtr);
  }
  pclose(P);
  LLM_LOG("InvokeMine: kerneldoc headers matched for " << Hits.size()
          << " corpus functions\n");

  // Extract blocks; keep callback-idiom candidates the file hasn't
  // already summarized.
  struct Cand {
    Function *F;
    KdocBlock B;
  };
  std::vector<Cand> Cands;
  for (auto &[Name, Loc] : Hits) {
    Function *F = Defined[Name];
    if (Summarized.count(Name))
      continue;
    KdocBlock B;
    B.File = Loc.first;
    B.Line = Loc.second;
    if (!readKdocBlock(Loc.first, Loc.second, B))
      continue;
    if (B.Params.size() < 2 || !kdocHasCallbackIdiom(B))
      continue;
    Cands.push_back({F, std::move(B)});
  }
  std::sort(Cands.begin(), Cands.end(),
            [](const Cand &A, const Cand &B) {
              return A.F->getName() < B.F->getName();
            });
  LLM_LOG("InvokeMine: " << Cands.size()
          << " candidates pass the callback-idiom prefilter\n");
  if (Cands.empty())
    return;

  std::error_code EC;
  raw_fd_ostream Out(OutPath, EC);
  if (EC) {
    WARNING("InvokeMine: cannot write " << OutPath << ": " << EC.message()
            << "\n");
    return;
  }
  Out << "# INVOKE proposals mined from kerneldoc (LLM tier-3; REVIEW "
         "REQUIRED)\n"
      << "# Docs describe intent — confirm via --cfl-confirm-invoke / "
         "census evidence\n"
      << "# before adopting lines into func_summaries.txt.\n";

  const StringRef SystemPrompt =
      "You extract callback-registration contracts from Linux kernel "
      "kerneldoc. Answer with strict JSON only, no prose.";
  const unsigned BatchSize = 6;
  size_t Proposed = 0, Queried = 0;
  for (size_t Begin = 0; Begin < Cands.size(); Begin += BatchSize) {
    size_t End = std::min(Begin + BatchSize, Cands.size());
    std::string UserPrompt;
    raw_string_ostream OS(UserPrompt);
    OS << "For each function, decide from its kerneldoc whether calling it "
          "registers or performs a callback: a function-pointer parameter "
          "invoked later or during the call, with another parameter passed "
          "to it. Use 0-based parameter indices in kerneldoc order. Report "
          "fn_arg (the function-pointer parameter), data_arg (the parameter "
          "passed to the callback), callee_formal (0-based position of the "
          "callback's own parameter receiving data_arg, or null if the doc "
          "does not say), and evidence (the exact doc sentence). Skip "
          "functions without such a contract.\n"
          "Return strict JSON: {\"proposals\":[{\"name\":\"...\",\"fn_arg\":"
          "0,\"data_arg\":0,\"callee_formal\":null,\"evidence\":\"...\"}]}\n";
    for (size_t I = Begin; I < End; I++) {
      const Cand &C = Cands[I];
      OS << "\n=== " << C.F->getName() << " (params in kerneldoc order:";
      for (size_t Pi = 0; Pi < C.B.Params.size(); Pi++)
        OS << (Pi ? ", " : " ") << C.B.Params[Pi].first;
      OS << ")\nsignature: " << *C.F->getFunctionType() << "\n"
         << C.B.Text;
    }
    OS.flush();
    if (DryRun) {
      Out << "\n# ---- DRY-RUN batch at " << Begin << " ("
          << UserPrompt.size() << " prompt bytes):";
      for (size_t I = Begin; I < End; I++)
        Out << " " << Cands[I].F->getName();
      Out << "\n";
      if (Begin == 0)
        LLM_LOG("InvokeMine: first dry-run prompt:\n" << UserPrompt << "\n");
      continue;
    }
    Queried++;
    unsigned MaxTok = 220 * (End - Begin) + 120;
    auto Resp = LLM->requestText(SystemPrompt, UserPrompt, MaxTok,
                                 std::max(240u, MaxTok / 4));
    if (!Resp) {
      WARNING("InvokeMine: batch at " << Begin
              << " failed: " << toString(Resp.takeError()) << "\n");
      continue;
    }
    Expected<json::Value> Parsed =
        json::parse(LLMClient::stripMarkdownFence(*Resp));
    if (!Parsed) {
      consumeError(Parsed.takeError());
      std::string Repaired =
          repairTruncatedJSON(LLMClient::stripMarkdownFence(*Resp));
      Parsed = json::parse(Repaired);
      if (!Parsed) {
        consumeError(Parsed.takeError());
        WARNING("InvokeMine: unparseable JSON for batch at " << Begin << "\n");
        continue;
      }
    }
    const json::Object *Obj = Parsed->getAsObject();
    const json::Array *Props = Obj ? Obj->getArray("proposals") : nullptr;
    if (!Props)
      continue;
    for (const json::Value &V : *Props) {
      const json::Object *E = V.getAsObject();
      if (!E)
        continue;
      auto Name = E->getString("name");
      auto FnA = E->getInteger("fn_arg");
      auto DataA = E->getInteger("data_arg");
      auto Ev = E->getString("evidence");
      if (!Name || !FnA || !DataA)
        continue;
      // Validate against the batch and the IR arity.
      const Cand *C = nullptr;
      for (size_t I = Begin; I < End; I++)
        if (Cands[I].F->getName() == *Name)
          C = &Cands[I];
      if (!C || *FnA == *DataA || *FnA < 0 || *DataA < 0 ||
          (unsigned)*FnA >= C->F->arg_size() ||
          (unsigned)*DataA >= C->F->arg_size())
        continue;
      auto KF = E->getInteger("callee_formal");
      Out << "\n# doc[" << C->B.File << ":" << C->B.Line << "] "
          << (Ev ? *Ev : StringRef("(no evidence quoted)")) << "\n";
      Out << "# PROPOSAL: " << *Name << " INVOKE(arg" << *FnA << ":f"
          << (KF ? std::to_string(*KF) : std::string("?")) << "<-arg"
          << *DataA << ")";
      if (!KF)
        Out << "   # fK: review the callback typedef";
      Out << "\n";
      Proposed++;
    }
  }
  LLM_LOG("InvokeMine: " << Proposed << " proposals from " << Queried
          << " LLM batches -> " << OutPath << "\n");
  Out << "\n# == " << Cands.size() << " candidates, " << Proposed
      << " proposals\n";
}
