import Lake
open Lake DSL

package "busybeaver" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here
  moreLeancArgs := #["-g"]

require "leanprover-community" / "mathlib"


@[default_target]
lean_exe beaver where
  moreLeancArgs := #["-g"]
  root := `Main

lean_lib «Busybeaver» where
  moreLeancArgs := #["-g"]
  -- add any library configuration options here
