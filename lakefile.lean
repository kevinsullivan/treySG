import Lake
open Lake DSL

package «treySG» where
  -- add package configuration options here

lean_lib «TreySG» where
  -- add library configuration options here
  require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
