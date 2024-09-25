import Lake
open Lake DSL

package «busybeaver» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here
  moreLeancArgs := #["-g"]

require mathlib from git "https://github.com/leanprover-community/mathlib4"

require Cli from git "https://github.com/leanprover/lean4-cli" @ "main"

@[default_target]
lean_exe «beaver» where
  moreLeancArgs := #["-g"]
  root := `Main

lean_lib «Busybeaver» where
  moreLeancArgs := #["-g"]
  -- add any library configuration options here

lean_exe «gfunc» where
  root := `bin.GFunction

private def gitConfig (opt val: String): IO Unit := do
  let _ ← IO.Process.run {
    cmd := "git",
    args := #["config", opt, val]
  }

/--
Sets up the git repository for contribution.
-/
script gitconfig do
  gitConfig "format.subjectPrefix" "PATCH busybeaver"
  gitConfig "format.signOff" "yes"
  gitConfig "format.coverLetter" "auto"

  gitConfig "sendemail.to" "~vigoux/busybeaver-devel@lists.sr.ht"
  gitConfig "sendemail.annotate" "yes"
  gitConfig "sendemail.assume8bitEncoding" "UTF-8"
  return 0
