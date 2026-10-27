import Lake
open Lake DSL

/-! Fixture for the builder tools: `Bad.lean` has a type error on line 4. -/

package «build-fail»

@[default_target]
lean_lib Bad
