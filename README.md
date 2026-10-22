# EllipticRegularity

[![CI](https://github.com/scottnarmstrong/EllipticRegularityLean/actions/workflows/build.yml/badge.svg)](https://github.com/scottnarmstrong/EllipticRegularityLean/actions/workflows/build.yml)

A machine-checked **Lean 4** formalization of the manuscript
*Elliptic Regularity* by Scott Armstrong, Tuomo Kuusi and Amélie Loher
([`manuscript/ellipticregularity.pdf`](manuscript/ellipticregularity.pdf)), built on
[Mathlib](https://github.com/leanprover-community/mathlib4).

The manuscript develops the quantitative regularity theory of scalar, second-order,
divergence-form uniformly elliptic and parabolic equations `-∇·(a∇u) = 0`,
`∂ₜu - ∇·(a∇u) = 0` with measurable coefficients. The Lean libraries prove its
theorems, propositions, lemmas, corollaries and examples; the complete
correspondence between numbered results and Lean declarations is in
[`RESULTS.md`](RESULTS.md).

- Lean `v4.35.0-rc2`, Mathlib `v4.35.0-rc2` (see `lean-toolchain` and
  `lake-manifest.json`).
- No `sorry` and no custom `axiom` in the libraries `PDEFoundation`,
  `EllipticRegularity` and the statement libraries (the `Challenges` library contains
  one intentional `sorry` per challenge, see "Independent verification"); the results depend only
  on Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Contents of the manuscript

| Chapter | Sections | Summary |
|---|---|---|
| 1. Function spaces and functional inequalities | 1.1 The isoperimetric inequality · 1.2 The Sobolev inequality · 1.3 Trace inequalities | The isoperimetric inequality (via Prékopa–Leindler and Brunn–Minkowski), Sobolev, Poincaré, Nash, John–Nirenberg, Trudinger and Campanato inequalities, and the trace theorem with its Besov-space characterization. |
| 2. The Laplace equation | 2.1 Harmonic functions · 2.2 Monotonicity formulas · 2.3 The heat equation | Pointwise estimates for harmonic functions; Almgren's frequency function, the three-sphere theorem and growth estimates; the Friedland–Hayman inequality and the Alt–Caffarelli–Friedman monotonicity formula; Poon's parabolic frequency. |
| 3. Perturbative estimates | 3.1 Schauder estimates · 3.2 Calderón–Zygmund estimates | Schauder estimates for Hölder and continuous coefficients; the Calderón–Zygmund `W^{1,p}` estimate and its sharpness; application to Yudovich uniqueness for the 2d Euler equations. |
| 4. Scale-invariant estimates | 4.1 The hole-filling estimate · 4.2 Higher integrability and the Meyers estimate · 4.3 The De Giorgi–Nash Hölder estimate · 4.4 Moser iteration · 4.5 The sharp exponent in two dimensions · 4.6 Sharpness of the Hölder exponent and of the Harnack ratio for `d ≥ 3` · 4.7 Green function decay estimates | Estimates that do not depend on the regularity of the coefficients: hole-filling, Gehring and Meyers, De Giorgi–Nash–Moser and the Harnack inequality, sharp exponents, and two-sided Green function bounds. |
| 5. Parabolic equations | 5.1 Function spaces for parabolic equations · 5.2 Parabolic Caccioppoli inequality · 5.3 The Nash–Aronson estimate | The parabolic energy space and the Cauchy problem, the weak and local parabolic Harnack inequalities, and two-sided Gaussian (Nash–Aronson) bounds on the fundamental solution. |

## Repository layout

| Path | Contents |
|---|---|
| `PDEFoundation/` | Ambient Euclidean geometry, Sobolev spaces, weak formulations of divergence-form equations, and the analytic inequalities of Chapter 1. Depends on Mathlib and, in one file (the Poincaré inequality with adjusted mean), on the statement module `SobolevStatements.ConvexSobolevPoincare`. |
| `EllipticRegularity/` | The regularity theory of Chapters 2–5, built on `PDEFoundation`. |
| `Ch1Statements/`, `Ch2Statements/`, `Ch4Statements/`, `Ch5Statements/`, `Ch5NashStatements/`, `CZStatements/`, `DGNMStatements/`, `EulerStatements/`, `GuerraStatements/`, `HarmonicStatements/`, `HoleFillingStatements/`, `MeyersStatements/`, `SchauderStatements/`, `SobolevStatements/` | One file per main result. Each file states a single theorem in the form given in the manuscript, together with its proof from the libraries above (the libraries themselves import some statement modules). These are the files to read to see what is proved; [`RESULTS.md`](RESULTS.md) lists them by manuscript number, together with the supporting statements that have no number (the `Newton*` weak-type statements of `CZStatements/WeakType/` and the Cauchy-problem and kernel statements of `Ch5NashStatements/`). |
| `Challenges/` | Self-contained, Mathlib-only statements of eighteen main results, each with a proof from this repository, for checking with the Lean [comparator](https://github.com/leanprover/comparator). See "Independent verification". |
| `manuscript/ellipticregularity.pdf` | The compiled manuscript. |

## Building

From the repository root:

```
lake exe cache get
lake build
```

`lake exe cache get` downloads the prebuilt Mathlib. The default targets of
`lake build` are all libraries: `PDEFoundation`, `EllipticRegularity`, and the
statement libraries. A full build is large; building a single result is faster,
for example `lake build Ch2Statements.AlmgrenMonotonicity`.

The Lean toolchain (`leanprover/lean4:v4.35.0-rc2`) is selected automatically
by `elan` from `lean-toolchain`.

## Checking what is proved

To see the axioms a result depends on, create a file importing its statement
module and print the axioms, for example

```lean
import Ch2Statements.AlmgrenMonotonicity
#print axioms PDE.almgren_monotonicity
```

and run it with `lake env lean <file>`. The output is
`'PDE.almgren_monotonicity' depends on axioms: [propext, Classical.choice, Quot.sound]`.

### Independent verification

The directory `Challenges/` contains one subdirectory per main result:

| Directory | Result | Lean statement |
|---|---|---|
| `Isoperimetric` | Proposition 1.1, isoperimetric inequality | `PDE.isoperimetric_inequality` |
| `PrekopaLeindler` | Theorem 1.2, Prékopa–Leindler inequality | `PDE.prekopa_leindler` |
| `SobolevSharpOne` | Proposition 1.4, sharp Sobolev inequality for `p = 1` | `PDE.sobolev_inequality_sharp_p_one` |
| `Campanato` | Lemma 1.19, Campanato characterization | `PDE.exists_campanato_characterization_constant` |
| `Trace` | Theorem 1.23, trace inequality | `PDE.trace_inequality` |
| `Almgren` | Theorem 2.2, Almgren monotonicity | `PDE.almgren_monotonicity` |
| `ACF` | Theorem 2.13, Alt–Caffarelli–Friedman monotonicity formula | `PDE.alt_caffarelli_friedman` |
| `Schauder` | Proposition 3.1, Schauder estimate | `PDE.exists_schauderCalpha_constant` |
| `CalderonZygmund` | Proposition 3.4, Calderón–Zygmund estimate | `PDE.exists_calderonZygmund` |
| `Yudovich` | Proposition 3.12, Yudovich uniqueness for 2d Euler | `PDE.yudovich_uniqueness` |
| `NewtonWeakType` | Weak-type (1,1) bound for the gradient of the Newtonian potential (supporting statement for Section 3.2; not a numbered result of the manuscript) | `PDE.exists_newtonPotential_weakTypeOne` |
| `Meyers` | Theorem 4.4, Meyers estimate | `PDE.exists_meyers_constants` |
| `DeGiorgiHolder` | Theorem 4.8, De Giorgi–Nash Hölder estimate | `PDE.exists_deGiorgi_holder_constant` |
| `Harnack` | Theorem 4.18, Harnack inequality | `PDE.exists_harnack_constant` |
| `GreenFunctionExistence` | Proposition 4.40, existence of the Green function | `PDE.greenExists` |
| `GreenFunctionBounds` | Proposition 4.42, Green function bounds for `d ≥ 3` | `PDE.greenD3` |
| `ParabolicHarnack` | Corollary 5.14, parabolic Harnack inequality | `PDE.parabLocalHarnack` |
| `NashAronsonLower` | Theorem 5.15, Nash–Aronson lower bound | `PDE.nashAronsonLower` |

Each contains

- `Challenge.lean`: a Mathlib-only statement of the result, with all notions
  defined in the file and a single `sorry` in place of the proof;
- `Solution.lean`: the same statement, proved from this repository;
- `comparator.json`: the configuration for the comparator, which checks that
  the two statements agree and that the solution depends only on the permitted
  axioms (`propext`, `Quot.sound`, `Classical.choice`), replaying the proof in
  an independent kernel (nanoda).

Check one with

```
lake comparator --config Challenges/Harnack/comparator.json
```

`lake comparator` is part of the pinned toolchain's Lake. It builds and exports
the project inside a `bwrap` sandbox, so [bubblewrap](https://github.com/containers/bubblewrap)
must be installed (with unprivileged user namespaces enabled), and the project
must have a `lake-manifest.json` (it has one). The checker is the comparator
bundled with Lake, with its bundled exporter and the independent nanoda kernel
(`enable_nanoda` in `comparator.json`); nothing else needs to be installed.

## Authors and citation

The Lean development is by

- **Scott Armstrong** — CNRS and Laboratoire Jacques-Louis Lions, Sorbonne
  Université; Courant Institute of Mathematical Sciences, New York University
- **Tuomo Kuusi** — Department of Mathematics and Statistics, University of
  Helsinki
- **Amélie Loher** — All Souls College, University of Oxford

If you use this formalization, please cite it using the metadata in
[`CITATION.cff`](CITATION.cff), and the manuscript:

> S. Armstrong, T. Kuusi, A. Loher, *Elliptic Regularity*, 2026.

## Acknowledgements

Scott Armstrong and Tuomo Kuusi were supported by the European Research Council
(ERC) under the European Union's Horizon Europe research and innovation
programme, grant agreement No. 101200828.
Amélie Loher acknowledges support from the Fondation Sciences Mathématiques de Paris.

## License

The Lean code in this repository is licensed under the **Apache License 2.0**
(see [`LICENSE`](LICENSE)).
