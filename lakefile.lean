import Lake
open Lake DSL

package «lean-agent» where
  precompileModules := false

lean_lib LeanAgent where
  globs := #[.submodules `LeanAgent]

@[default_target]
lean_exe «lean-agent» where
  root := `LeanAgentQuery

lean_exe «lean-agent-tests» where
  root := `LeanAgentTests

lean_exe «multiagent» where
  root := `Multiagent
  srcDir := "examples"

@[test_driver]
script test do
  let code ← exe `«lean-agent-tests»
  if code != 0 then return code
  return 0
