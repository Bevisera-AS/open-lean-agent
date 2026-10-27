import Lake
open Lake DSL

/-! Fixture for the builder tools: builds, tests and kernel-checks cleanly. -/

package «build-ok»

@[default_target]
lean_lib BuildOk

lean_exe «build-ok-tests» where
  root := `BuildOkTests

@[test_driver]
script test do
  exe `«build-ok-tests»
