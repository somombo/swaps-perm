import Lake
open Lake DSL

package «swaps-perm» where
  -- add package configuration options here

require std from git "https://github.com/leanprover/std4.git" @ "v4.7.0"

@[default_target]
lean_lib «SwapsPerm» where
  -- add library configuration options here
