#include "LLMClient.h"
#include "Common.h"

#include <llvm/Support/FileSystem.h>
#include <llvm/Support/FormatVariadic.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/Path.h>
#include <llvm/Support/Program.h>
#include <llvm/Support/raw_ostream.h>

#include <system_error>
#include <unistd.h>
#include <vector>

using namespace llvm;

LLMClient::LLMClient(LLMClientConfig Config) : Cfg(std::move(Config)) {}

Expected<std::string> LLMClient::runCurl(StringRef RequestBody,
                                         unsigned TimeoutOverride) const {
  if (!Cfg.Enabled) {
    return createStringError(inconvertibleErrorCode(),
                             "LLM client is disabled");
  }

  ErrorOr<std::string> CurlPath = sys::findProgramByName("curl");
  if (!CurlPath) {
    return createStringError(inconvertibleErrorCode(),
                             "curl not found in PATH");
  }

  int ReqFD = -1;
  SmallString<128> ReqPath;
  if (std::error_code EC = sys::fs::createTemporaryFile("ka-llm-req", "json", ReqFD, ReqPath)) {
    return createStringError(EC, "failed to create request temp file");
  }
  close(ReqFD);

  int RespFD = -1;
  SmallString<128> RespPath;
  if (std::error_code EC = sys::fs::createTemporaryFile("ka-llm-resp", "json", RespFD, RespPath)) {
    sys::fs::remove(ReqPath);
    return createStringError(EC, "failed to create response temp file");
  }
  close(RespFD);

  std::error_code WriteEC;
  raw_fd_ostream ReqOS(ReqPath, WriteEC, sys::fs::OF_Text);
  if (WriteEC) {
    sys::fs::remove(ReqPath);
    sys::fs::remove(RespPath);
    return createStringError(WriteEC, "failed to open request temp file");
  }
  ReqOS << RequestBody;
  ReqOS.close();
  if (ReqOS.has_error()) {
    sys::fs::remove(ReqPath);
    sys::fs::remove(RespPath);
    return createStringError(inconvertibleErrorCode(),
                             "failed to write request body");
  }

  std::vector<std::string> ArgStorage;
  ArgStorage.emplace_back(CurlPath.get());
  ArgStorage.emplace_back("-sS");
  ArgStorage.emplace_back("--fail-with-body");
  ArgStorage.emplace_back("-X");
  ArgStorage.emplace_back("POST");
  ArgStorage.emplace_back(Cfg.Endpoint);
  ArgStorage.emplace_back("-H");
  ArgStorage.emplace_back("Content-Type: application/json");
  if (!Cfg.ApiKey.empty()) {
    ArgStorage.emplace_back("-H");
    ArgStorage.emplace_back("Authorization: Bearer " + Cfg.ApiKey);
  }
  unsigned Timeout = TimeoutOverride ? TimeoutOverride : Cfg.TimeoutSeconds;
  ArgStorage.emplace_back("--max-time");
  ArgStorage.emplace_back(std::to_string(Timeout));
  ArgStorage.emplace_back("--data-binary");
  ArgStorage.emplace_back("@" + ReqPath.str().str());
  ArgStorage.emplace_back("-o");
  ArgStorage.emplace_back(RespPath.str().str());

  SmallVector<StringRef, 16> Args;
  Args.reserve(ArgStorage.size());
  for (const std::string &A : ArgStorage) {
    Args.push_back(A);
  }

  std::string ErrMsg;
  bool ExecutionFailed = false;
#if LLVM_VERSION_MAJOR >= 15
  int RC = sys::ExecuteAndWait(CurlPath.get(), Args, /*Env=*/std::nullopt, /*Redirects=*/{}, 0, 0,
#else
  int RC = sys::ExecuteAndWait(CurlPath.get(), Args, /*Env=*/None, /*Redirects=*/{}, 0, 0,
#endif
                               &ErrMsg, &ExecutionFailed);
  if (RC != 0 || ExecutionFailed) {
    ErrorOr<std::unique_ptr<MemoryBuffer>> RespFile = MemoryBuffer::getFile(RespPath);
    std::string Body = RespFile ? RespFile.get()->getBuffer().str() : "";
    sys::fs::remove(ReqPath);
    sys::fs::remove(RespPath);
    return createStringError(inconvertibleErrorCode(),
                             formatv("curl request failed (rc={0}, exec_failed={1}): {2}{3}",
                                     RC, ExecutionFailed, ErrMsg, Body.empty() ? "" : "\n" + Body)
                                 .str());
  }

  ErrorOr<std::unique_ptr<MemoryBuffer>> RespFile = MemoryBuffer::getFile(RespPath);
  if (!RespFile) {
    sys::fs::remove(ReqPath);
    sys::fs::remove(RespPath);
    return createStringError(RespFile.getError(),
                             "failed to read response body");
  }

  std::string Response = RespFile.get()->getBuffer().str();
  sys::fs::remove(ReqPath);
  sys::fs::remove(RespPath);
  return Response;
}

Expected<std::string> LLMClient::extractMessageContent(StringRef ResponseBody) const {
  Expected<json::Value> Parsed = json::parse(ResponseBody);
  if (!Parsed) {
    return createStringError(inconvertibleErrorCode(),
                             "failed to parse llama.cpp JSON response");
  }

  json::Object *Obj = Parsed->getAsObject();
  if (!Obj) {
    return createStringError(inconvertibleErrorCode(),
                             "llama.cpp response is not a JSON object");
  }

  // OpenAI-compatible chat endpoint: choices[0].message.content
  if (json::Array *Choices = Obj->getArray("choices")) {
    if (!Choices->empty()) {
      if (json::Object *Choice0 = (*Choices)[0].getAsObject()) {
        if (json::Object *Msg = Choice0->getObject("message")) {
          if (auto Content = Msg->getString("content")) {
            return Content->str();
          }
        }
      }
    }
  }

  // Fallback for legacy /completion endpoint: {"content":"..."}
  if (auto Content = Obj->getString("content")) {
    return Content->str();
  }

  return createStringError(inconvertibleErrorCode(),
                           "cannot find completion text in llama.cpp response");
}

Expected<std::string> LLMClient::requestText(StringRef SystemPrompt,
                                             StringRef UserPrompt,
                                             unsigned MaxTokensOverride,
                                             unsigned TimeoutOverride) const {
  json::Array Messages;
  if (!SystemPrompt.empty()) {
    Messages.emplace_back(json::Object{
        {"role", "system"},
        {"content", SystemPrompt.str()},
    });
  }
  Messages.emplace_back(json::Object{
      {"role", "user"},
      {"content", UserPrompt.str()},
  });

  json::Object Req{
      {"messages", std::move(Messages)},
      {"stream", false},
      {"temperature", Cfg.Temperature},
      {"max_tokens", static_cast<int64_t>(MaxTokensOverride ? MaxTokensOverride : Cfg.MaxTokens)},
  };
  if (!Cfg.Model.empty()) {
    Req["model"] = Cfg.Model;
  }
  if (Cfg.Seed >= 0) {
    Req["seed"] = Cfg.Seed;
  }

  std::string ReqBody;
  raw_string_ostream OS(ReqBody);
  OS << formatv("{0}", json::Value(std::move(Req)));
  OS.flush();

  Expected<std::string> Resp = runCurl(ReqBody, TimeoutOverride);
  if (!Resp) {
    return Resp.takeError();
  }
  return extractMessageContent(*Resp);
}

std::string LLMClient::stripMarkdownFence(StringRef Text) {
  StringRef Trimmed = Text.trim();
  if (!LLVM_STRING_STARTS_WITH(Trimmed, "```")) {
    return Trimmed.str();
  }

  size_t FirstNL = Trimmed.find('\n');
  if (FirstNL == StringRef::npos) {
    return Trimmed.str();
  }

  StringRef Body = Trimmed.drop_front(FirstNL + 1);
  size_t LastFence = Body.rfind("```");
  if (LastFence == StringRef::npos) {
    return Trimmed.str();
  }
  return Body.take_front(LastFence).trim().str();
}

Expected<json::Value> LLMClient::requestJSON(StringRef SystemPrompt,
                                             StringRef UserPrompt) const {
  Expected<std::string> RespText = requestText(SystemPrompt, UserPrompt);
  if (!RespText) {
    return RespText.takeError();
  }

  std::string CandidateJSON = stripMarkdownFence(*RespText);
  Expected<json::Value> Parsed = json::parse(CandidateJSON);
  if (!Parsed) {
    return createStringError(inconvertibleErrorCode(),
                             "model response is not valid JSON");
  }
  return std::move(*Parsed);
}
