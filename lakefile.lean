import Lake

open Lake DSL

package «elliptic_regularity» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0-rc2"

private def projectLeanOptions : Array LeanOption := #[
  ⟨`autoImplicit, false⟩,
  ⟨`relaxedAutoImplicit, false⟩,
  ⟨`linter.unusedVariables, true⟩,
  ⟨`linter.unusedSectionVars, true⟩,
  ⟨`linter.unusedSimpArgs, true⟩,
  ⟨`linter.unnecessarySimpa, true⟩,
  ⟨`linter.deprecated, true⟩
]

@[default_target]
lean_lib «PDEFoundation» where
  globs := #[.andSubmodules `PDEFoundation]
  leanOptions := projectLeanOptions

@[default_target]
lean_lib «EllipticRegularity» where
  globs := #[.andSubmodules `EllipticRegularity]
  leanOptions := projectLeanOptions

/-- Headline theorem statements, one file per statement. -/
@[default_target]
lean_lib «Ch1Statements» where
  globs := #[.submodules `Ch1Statements]
  leanOptions := projectLeanOptions

/-- Headline theorem statements, one file per statement. -/
@[default_target]
lean_lib «Ch2Statements» where
  globs := #[.submodules `Ch2Statements]
  leanOptions := projectLeanOptions

/-- Headline theorem statements, one file per statement. -/
@[default_target]
lean_lib «Ch4Statements» where
  globs := #[.submodules `Ch4Statements]
  leanOptions := projectLeanOptions

/-- Headline theorem statements, one file per statement. -/
@[default_target]
lean_lib «Ch5Statements» where
  globs := #[.submodules `Ch5Statements]
  leanOptions := projectLeanOptions

/-- Headline theorem statements, one file per statement. -/
@[default_target]
lean_lib «Ch5NashStatements» where
  globs := #[.submodules `Ch5NashStatements]
  leanOptions := projectLeanOptions

/-- Headline theorem statements, one file per statement. -/
@[default_target]
lean_lib «CZStatements» where
  globs := #[.submodules `CZStatements]
  leanOptions := projectLeanOptions

/-- Headline theorem statements, one file per statement. -/
@[default_target]
lean_lib «DGNMStatements» where
  globs := #[.submodules `DGNMStatements]
  leanOptions := projectLeanOptions

/-- Headline theorem statements, one file per statement. -/
@[default_target]
lean_lib «EulerStatements» where
  globs := #[.submodules `EulerStatements]
  leanOptions := projectLeanOptions

/-- Headline theorem statements, one file per statement. -/
@[default_target]
lean_lib «GuerraStatements» where
  globs := #[.submodules `GuerraStatements]
  leanOptions := projectLeanOptions

/-- Headline theorem statements, one file per statement. -/
@[default_target]
lean_lib «HarmonicStatements» where
  globs := #[.submodules `HarmonicStatements]
  leanOptions := projectLeanOptions

/-- Headline theorem statements, one file per statement. -/
@[default_target]
lean_lib «HoleFillingStatements» where
  globs := #[.submodules `HoleFillingStatements]
  leanOptions := projectLeanOptions

/-- Headline theorem statements, one file per statement. -/
@[default_target]
lean_lib «MeyersStatements» where
  globs := #[.submodules `MeyersStatements]
  leanOptions := projectLeanOptions

/-- Headline theorem statements, one file per statement. -/
@[default_target]
lean_lib «SchauderStatements» where
  globs := #[.submodules `SchauderStatements]
  leanOptions := projectLeanOptions

/-- Headline theorem statements, one file per statement. -/
@[default_target]
lean_lib «SobolevStatements» where
  globs := #[.submodules `SobolevStatements]
  leanOptions := projectLeanOptions

/-- Comparator challenges: one self-contained, Mathlib-only statement per headline
result (`Challenge.lean`, with one `sorry`) and its proof from this library
(`Solution.lean`). Check with `lake comparator --config Challenges/<Name>/comparator.json`. -/
lean_lib «Challenges» where
  globs := #[.submodules `Challenges]
  leanOptions := projectLeanOptions
