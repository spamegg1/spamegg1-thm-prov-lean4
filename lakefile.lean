import Lake
open Lake DSL

package "spamegg1-thm-prov-lean4" where
  version := v!"0.1.0"

lean_lib «Spamegg1ThmProvLean4» where
  -- add library configuration options here

@[default_target]
lean_exe "spamegg1-thm-prov-lean4" where
  root := `Main

require batteries from git "https://github.com/leanprover-community/batteries" @ "main"
