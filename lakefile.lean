import Lake
open Lake DSL

package «lean4_textbook» where
  -- add package configuration options here

lean_lib «Lean4Textbook» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_exe «lean4_textbook» where
  root := `Main
