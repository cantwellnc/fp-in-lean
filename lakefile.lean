import Lake
open Lake DSL

package "fp-in-lean" where
  version := v!"0.1.0"

lean_lib «FpInLean» where
  -- add library configuration options here

@[default_target]
lean_exe "fp-in-lean" where
  root := `Main
