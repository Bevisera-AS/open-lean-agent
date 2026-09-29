module

public import LeanAgent.Curl
public import LeanAgent.Types
public meta import LeanAgent.Types

namespace LeanAgent

/-- Host supplies the HTTP result of `POST /v1/chat/completions`. Tests inject a
fixture. The typed `HttpResult` keeps the numeric HTTP status instead of
stringifying it. -/
public structure Completer where
  post : String → String → IO HttpResult

public def curlCompleter (cfg : ProviderConfig) : Completer := {
  post := fun url body => Curl.post url body cfg.authHeader
}

end LeanAgent
