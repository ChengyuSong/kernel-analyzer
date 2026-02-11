/*
 * LLM-based analysis for allocator and container function identification
 *
 * Copyright (C) 2026 Chengyu Song
 *
 * For licensing details see LICENSE
 */

#include <llvm/ADT/ArrayRef.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/Support/Error.h>
#include <llvm/Support/JSON.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/raw_ostream.h>

#include <fstream>
#include <unordered_map>
#include <vector>

#include "LLMAnalysis.h"
#include "Global.h"
#include "Annotation.h"
#include "LLMClient.h"

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
        std::optional<StringRef> Name = V.getAsString();
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

  json::Array Candidates;
  for (const Function *F : Ctx->CandidateAllocFuncs)
    Candidates.push_back(F->getName().str());

  json::Object Root;
  Root["candidates"] = std::move(Candidates);
  OS << json::Value(std::move(Root)) << "\n";
  LLM_LOG("Saved " << Ctx->CandidateAllocFuncs.size()
         << " allocator candidate(s) to " << Path << "\n");
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

bool loadAllocatorFile(GlobalContext *Ctx, StringRef Path) {
  auto BufOrErr = MemoryBuffer::getFile(Path);
  if (!BufOrErr) {
    WARNING("Failed to open allocator file: " << Path << ": "
            << BufOrErr.getError().message() << "\n");
    return false;
  }

  Expected<json::Value> Parsed = json::parse((*BufOrErr)->getBuffer());
  if (!Parsed) {
    WARNING("Failed to parse allocator JSON: " << toString(Parsed.takeError()) << "\n");
    return false;
  }

  // Build name -> Function* map for lookup
  std::unordered_map<std::string, Function*> NameToFunc;
  for (auto &[id, F] : Ctx->Funcs)
    NameToFunc[F->getName().str()] = F;

  const json::Object *Obj = Parsed->getAsObject();
  if (!Obj) return false;
  const json::Array *Candidates = Obj->getArray("candidates");
  if (!Candidates) return false;

  size_t Loaded = 0;
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
      Loaded++;
  }
  LLM_LOG("Loaded " << Loaded << " allocator candidate(s) from " << Path << "\n");
  return true;
}

bool loadContainerFile(GlobalContext *Ctx, StringRef Path) {
  auto BufOrErr = MemoryBuffer::getFile(Path);
  if (!BufOrErr) {
    WARNING("Failed to open container file: " << Path << ": "
            << BufOrErr.getError().message() << "\n");
    return false;
  }

  Expected<json::Value> Parsed = json::parse((*BufOrErr)->getBuffer());
  if (!Parsed) {
    WARNING("Failed to parse container JSON: " << toString(Parsed.takeError()) << "\n");
    return false;
  }

  // Build name -> Function* map for lookup
  std::unordered_map<std::string, Function*> NameToFunc;
  for (auto &[id, F] : Ctx->Funcs)
    NameToFunc[F->getName().str()] = F;

  // Reuse processContainerResponse by constructing a batch from matched names
  const json::Object *Obj = Parsed->getAsObject();
  if (!Obj) return false;
  const json::Array *Containers = Obj->getArray("containers");
  if (!Containers) return false;

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
  return true;
}
