import Lake
open Lake DSL

package «lean-trying-multivariable» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «TermOrder» {
  -- add any library configuration options here
}

@[default_target]
lean_lib «Multideg» {
  -- add any library configuration options here
}

lean_lib «Basic» {
  -- add any library configuration options here
}

@[default_target]
lean_lib «Ideal» {
  -- add any library configuration options here
}
