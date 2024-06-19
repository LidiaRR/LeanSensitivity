import Lake
open Lake DSL

package «LeanSensitivity» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.5.0"

@[default_target]
lean_lib «LeanSensitivity» where
  -- add any library configuration options here
