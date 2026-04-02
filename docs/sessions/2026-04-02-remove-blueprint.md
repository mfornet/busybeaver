# Remove Unused Documentation Scaffolding

Removed an unused documentation-generation setup and its repository hooks.

## What changed

- Deleted the obsolete documentation tree.
- Deleted the dedicated CI workflow and helper script for that tooling.
- Removed related instructions and architecture references from the README.
- Removed tooling-specific ignore entries from `.gitignore`.

## Verification

- `lake build` still succeeds after the cleanup.
- Repository search confirms the removed tooling is no longer referenced in tracked source and configuration files.

## Remaining debt

- Existing proof debt in `Busybeaver/Deciders/TranslatedCyclers.lean` remains unchanged.
