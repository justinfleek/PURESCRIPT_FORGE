import Lake
open Lake DSL

package «prism-color» where
  version := v!"0.1.0"

lean_lib «PrismColor» where
  -- add library configuration options here

@[default_target]
lean_exe «prism-color» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
