import Lake
open Lake DSL

package «lean-agent» where
  precompileModules := false

@[default_target]
lean_lib LeanAgent where
  globs := #[`LeanAgent, .submodules `LeanAgent]

/- The executables are not default targets. `lake check` exports every default
target into one environment, and each executable root defines `main`, so two of
them cannot be imported together. Build them by name:
`lake build lean-agent lean-agent-tests multiagent spec-loop`. -/

lean_exe «lean-agent» where
  root := `LeanAgentQuery

lean_exe «lean-agent-tests» where
  root := `LeanAgentTests

lean_exe «multiagent» where
  root := `Multiagent
  srcDir := "examples"

lean_exe «spec-loop» where
  root := `SpecLoop
  srcDir := "examples"

@[test_driver]
script test do
  let code ← exe `«lean-agent-tests»
  if code != 0 then return code
  return 0
