import Lake
open Lake DSL

package «physlib» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Physlib» {
  -- add any library configuration options here
}
