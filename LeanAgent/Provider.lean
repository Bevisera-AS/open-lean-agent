module

public import LeanAgent.Util
public meta import LeanAgent.Util

namespace LeanAgent

public section

/-- Closed provider catalog. A name that is not a constructor cannot inhabit `Config`. -/
public inductive Provider where
  | ollama
  | bedrockMantle
  | openAI
  | anthropic
  | glm
  deriving Repr, BEq, DecidableEq

public inductive Protocol where
  | openAIChat
  | anthropicMessages
  deriving Repr, BEq, DecidableEq

public structure Capabilities where
  protocol : Protocol
  tools : Bool
  jsonSchema : Bool
  deriving Repr, BEq

/-- Local OpenAI-compat host. No secret environment variable inhabits this type. -/
public structure LocalSettings where
  baseUrl : String
  model : String
  maxTokens : Option Nat := some 1024
  deriving Repr, BEq

/-- Hosted provider. The API key is an environment *name*, never a secret value. -/
public structure HostedSettings where
  baseUrl : String
  model : String
  apiKeyEnv : String
  maxTokens : Option Nat := some 1024
  deriving Repr, BEq

/-- Provider-indexed settings. Ollama cannot carry an API-key env; hosted providers must. -/
public inductive Config : Provider → Type where
  | ollama : LocalSettings → Config .ollama
  | bedrockMantle : HostedSettings → Config .bedrockMantle
  | openAI : HostedSettings → Config .openAI
  | anthropic : HostedSettings → Config .anthropic
  | glm : HostedSettings → Config .glm

public structure ProviderConfig where
  provider : Provider
  config : Config provider

public def Provider.toWire : Provider → String
  | .ollama => "ollama"
  | .bedrockMantle => "bedrock-mantle"
  | .openAI => "openai"
  | .anthropic => "anthropic"
  | .glm => "glm"

public def Provider.parse (id : String) : Except String Provider :=
  match id with
  | "ollama" => .ok .ollama
  | "bedrock-mantle" | "bedrock" => .ok .bedrockMantle
  | "openai" => .ok .openAI
  | "anthropic" => .ok .anthropic
  | "glm" => .ok .glm
  | other =>
    .error s!"unknown LEAN_AGENT_PROVIDER `{other}` (want ollama, bedrock-mantle, openai, anthropic, or glm)"

public def Provider.protocol : Provider → Protocol
  | .ollama | .bedrockMantle | .openAI | .glm => .openAIChat
  | .anthropic => .anthropicMessages

public def Provider.capabilities : Provider → Capabilities
  | .ollama => { protocol := .openAIChat, tools := true, jsonSchema := true }
  | .bedrockMantle => { protocol := .openAIChat, tools := true, jsonSchema := true }
  | .openAI => { protocol := .openAIChat, tools := true, jsonSchema := true }
  | .glm => { protocol := .openAIChat, tools := true, jsonSchema := true }
  | .anthropic => { protocol := .anthropicMessages, tools := true, jsonSchema := false }

public def Config.model {p : Provider} : Config p → String
  | .ollama s => s.model
  | .bedrockMantle s => s.model
  | .openAI s => s.model
  | .anthropic s => s.model
  | .glm s => s.model

public def Config.baseUrl {p : Provider} : Config p → String
  | .ollama s => s.baseUrl
  | .bedrockMantle s => s.baseUrl
  | .openAI s => s.baseUrl
  | .anthropic s => s.baseUrl
  | .glm s => s.baseUrl

public def Config.maxTokens {p : Provider} : Config p → Option Nat
  | .ollama s => s.maxTokens
  | .bedrockMantle s => s.maxTokens
  | .openAI s => s.maxTokens
  | .anthropic s => s.maxTokens
  | .glm s => s.maxTokens

/-- Ollama is uninhabited with a key env; every hosted constructor supplies one. -/
public def Config.apiKeyEnv {p : Provider} : Config p → Option String
  | .ollama _ => none
  | .bedrockMantle s => some s.apiKeyEnv
  | .openAI s => some s.apiKeyEnv
  | .anthropic s => some s.apiKeyEnv
  | .glm s => some s.apiKeyEnv

public def pickNonempty (cur : String) : Option String → String
  | some s => if nonemptyText s then s else cur
  | none => cur

public def Config.overlay {p : Provider} (c : Config p) (model? url? : Option String) : Config p :=
  match c with
  | .ollama s =>
    .ollama { s with model := pickNonempty s.model model?, baseUrl := pickNonempty s.baseUrl url? }
  | .bedrockMantle s =>
    .bedrockMantle { s with model := pickNonempty s.model model?, baseUrl := pickNonempty s.baseUrl url? }
  | .openAI s =>
    .openAI { s with model := pickNonempty s.model model?, baseUrl := pickNonempty s.baseUrl url? }
  | .anthropic s =>
    .anthropic { s with model := pickNonempty s.model model?, baseUrl := pickNonempty s.baseUrl url? }
  | .glm s =>
    .glm { s with model := pickNonempty s.model model?, baseUrl := pickNonempty s.baseUrl url? }

public def ProviderConfig.model (c : ProviderConfig) : String :=
  Config.model c.config

public def ProviderConfig.baseUrl (c : ProviderConfig) : String :=
  Config.baseUrl c.config

public def ProviderConfig.maxTokens (c : ProviderConfig) : Option Nat :=
  Config.maxTokens c.config

public def ProviderConfig.apiKeyEnv (c : ProviderConfig) : Option String :=
  Config.apiKeyEnv c.config

public def ProviderConfig.providerId (c : ProviderConfig) : String :=
  Provider.toWire c.provider

public def ProviderConfig.protocol (c : ProviderConfig) : Protocol :=
  c.provider.protocol

public def ProviderConfig.capabilities (c : ProviderConfig) : Capabilities :=
  c.provider.capabilities

public def ProviderConfig.chatUrl (c : ProviderConfig) : String :=
  let root := (c.baseUrl.dropEndWhile (· == '/')).toString
  match c.protocol with
  | .openAIChat => root ++ "/chat/completions"
  | .anthropicMessages => root ++ "/v1/messages"

public def overlayConfig (base : ProviderConfig) (model? url? : Option String) : ProviderConfig :=
  { provider := base.provider, config := Config.overlay base.config model? url? }

public def ollama : ProviderConfig := {
  provider := .ollama
  config := .ollama {
    baseUrl := "http://127.0.0.1:11434/v1"
    model := "llama3.2"
  }
}

public def bedrockMantle : ProviderConfig := {
  provider := .bedrockMantle
  config := .bedrockMantle {
    baseUrl := "https://bedrock-mantle.eu-north-1.api.aws/v1"
    model := "placeholder-model"
    apiKeyEnv := "AWS_BEARER_TOKEN_BEDROCK"
  }
}

public def openAI : ProviderConfig := {
  provider := .openAI
  config := .openAI {
    baseUrl := "https://api.openai.com/v1"
    model := "gpt-4o-mini"
    apiKeyEnv := "OPENAI_API_KEY"
  }
}

public def anthropic : ProviderConfig := {
  provider := .anthropic
  config := .anthropic {
    baseUrl := "https://api.anthropic.com"
    model := "claude-sonnet-4-5"
    apiKeyEnv := "ANTHROPIC_API_KEY"
  }
}

public def glm : ProviderConfig := {
  provider := .glm
  config := .glm {
    baseUrl := "https://open.bigmodel.cn/api/paas/v4"
    model := "glm-4"
    apiKeyEnv := "GLM_API_KEY"
  }
}

public def namedProvider (id : String) : Except String ProviderConfig :=
  match Provider.parse id with
  | .error e => .error e
  | .ok .ollama => .ok ollama
  | .ok .bedrockMantle => .ok bedrockMantle
  | .ok .openAI => .ok openAI
  | .ok .anthropic => .ok anthropic
  | .ok .glm => .ok glm

public inductive AuthHeader where
  | none
  | bearer (envName : String)
  | anthropic (envName : String)
  deriving Repr, BEq

public def Config.authHeader {p : Provider} : Config p → AuthHeader
  | .ollama _ => .none
  | .bedrockMantle s => .bearer s.apiKeyEnv
  | .openAI s => .bearer s.apiKeyEnv
  | .glm s => .bearer s.apiKeyEnv
  | .anthropic s => .anthropic s.apiKeyEnv

public def ProviderConfig.authHeader (c : ProviderConfig) : AuthHeader :=
  Config.authHeader c.config

#guard Provider.toWire .ollama == "ollama"
#guard Provider.toWire .bedrockMantle == "bedrock-mantle"
#guard
  match Provider.parse "bedrock" with
  | .ok .bedrockMantle => true
  | _ => false
#guard
  match Provider.parse "langchain" with
  | .error d => d.contains "langchain"
  | .ok _ => false
#guard ollama.providerId == "ollama"
#guard ollama.apiKeyEnv.isNone
#guard ollama.protocol == Protocol.openAIChat
#guard ollama.chatUrl == "http://127.0.0.1:11434/v1/chat/completions"
#guard bedrockMantle.apiKeyEnv == some "AWS_BEARER_TOKEN_BEDROCK"
#guard openAI.apiKeyEnv == some "OPENAI_API_KEY"
#guard glm.apiKeyEnv == some "GLM_API_KEY"
#guard anthropic.protocol == Protocol.anthropicMessages
#guard anthropic.chatUrl == "https://api.anthropic.com/v1/messages"
#guard anthropic.capabilities.jsonSchema == false
#guard
  match namedProvider "openai" with
  | .ok c => c.providerId == "openai" && c.chatUrl.endsWith "/chat/completions"
  | .error _ => false
#guard Config.apiKeyEnv (.ollama { baseUrl := "http://127.0.0.1:11434/v1", model := "x" }) == none

end

end LeanAgent
