import Lake
open Lake DSL

package «CoarseDeGiorgi» where

-- The public CoarseGraining library, pinned to a fixed commit.
require CoarseGraining from git
  "https://github.com/scottnarmstrong/CoarseGraining.git" @ "c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4"

@[default_target]
lean_lib «CoarseDeGiorgi» where
  globs := #[.andSubmodules `CoarseDeGiorgi]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]

-- Comparator challenges (Mathlib-only, one intentional placeholder each) and their solutions;
-- not a default target. See COMPARATORS.md.
lean_lib «CoarseDeGiorgiAudit» where
  globs := #[.submodules `CoarseDeGiorgiAudit]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
