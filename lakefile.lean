import Lake
open Lake DSL

package «swaps-perm» where
  -- add package configuration options here

require batteries from git "https://github.com/leanprover-community/batteries.git" @ "main"

@[default_target]
lean_lib «SwapsPerm» where
  -- add library configuration options here
