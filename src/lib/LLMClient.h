#ifndef _LLM_CLIENT_H
#define _LLM_CLIENT_H

#include <llvm/ADT/StringRef.h>
#include <llvm/Support/Error.h>
#include <llvm/Support/JSON.h>

#include <string>

struct LLMClientConfig {
  bool Enabled = false;
  std::string Endpoint = "http://127.0.0.1:8080/v1/chat/completions";
  std::string Model;
  std::string ApiKey;
  unsigned TimeoutSeconds = 30;
  unsigned MaxTokens = 512;
  double Temperature = 0.0;
  long long Seed = -1;
};

class LLMClient {
public:
  explicit LLMClient(LLMClientConfig Config);

  bool isEnabled() const { return Cfg.Enabled; }

  // Sends a chat completion request to a llama.cpp server and returns
  // choices[0].message.content.
  llvm::Expected<std::string> requestText(llvm::StringRef SystemPrompt,
                                          llvm::StringRef UserPrompt) const;

  // Same as requestText() but expects the model output to be JSON text.
  llvm::Expected<llvm::json::Value> requestJSON(llvm::StringRef SystemPrompt,
                                                llvm::StringRef UserPrompt) const;

private:
  llvm::Expected<std::string> runCurl(llvm::StringRef RequestBody) const;
  llvm::Expected<std::string> extractMessageContent(llvm::StringRef ResponseBody) const;
  static std::string stripMarkdownFence(llvm::StringRef Text);

  LLMClientConfig Cfg;
};

#endif
