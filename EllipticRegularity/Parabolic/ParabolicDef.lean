module

public import PDEFoundation

/-!
# Definition module for Chapter 5.1-5.2 (parabolic energy space, weak solutions)

Carrier: `Vec d × ℝ`, space first, `(x, t)`.  Measure: `volume` on the product, restricted to
`U ×ˢ I`.  Slices are `fun x => u (x, t)`.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set

/-- Time-dependent coefficient field on space-time. -/
abbrev ParCoeffField (d : ℕ) := Vec d × ℝ → Mat d

/-- Time derivative `∂ₜφ` of a space-time function (ambient derivative in direction `(0,1)`). -/
noncomputable def parTimeDeriv {d : ℕ} (φ : Vec d × ℝ → ℝ) (z : Vec d × ℝ) : ℝ :=
  fderiv ℝ φ z (0, 1)

/-- Spatial gradient `∇ₓφ` of a space-time function. -/
noncomputable def parSpaceGrad {d : ℕ} (φ : Vec d × ℝ → ℝ) (z : Vec d × ℝ) : Vec d :=
  fun i => fderiv ℝ φ z (basisVec i, 0)

/-- Spatial gradient of a function on space (`C¹` slice test functions `ζ ∈ C¹_c(U)`). -/
noncomputable def spaceGradC1 {d : ℕ} (ζ : Vec d → ℝ) (x : Vec d) : Vec d :=
  fun i => fderiv ℝ ζ x (basisVec i)

/-- The slice `x ↦ u(x,t)` of a space-time function. -/
def parSlice {d : ℕ} {β : Type*} (u : Vec d × ℝ → β) (t : ℝ) : Vec d → β := fun x => u (x, t)

/-- The parabolic coefficient hypotheses (manuscript (5.1)) on `U × I`: jointly measurable
entries, `0 < λ ≤ Λ`, and for a.e. `(x,t)` both `e·a e ≥ λ|e|²` and `e·a⁻¹e ≥ Λ⁻¹|e|²`
(this is `IsEllipticMatrix λ Λ (a z)`). -/
structure IsParabolicCoeff {d : ℕ} (lam Lam : ℝ) (a : ParCoeffField d)
    (U : Set (Vec d)) (I : Set ℝ) : Prop where
  measurable : ∀ i j : Fin d, AEMeasurable (fun z => a z i j) (volume.restrict (U ×ˢ I))
  elliptic : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), IsEllipticMatrix lam Lam (a z)

/-- `C¹` test functions with compact support in the open set `U ×ˢ J`: `C¹_c(J × U)` for open `J`
(used with `J = interior I`). -/
structure ParTestFunction {d : ℕ} (U : Set (Vec d)) (J : Set ℝ) where
  toFun : Vec d × ℝ → ℝ
  contDiff : ContDiff ℝ 1 toFun
  hasCompactSupport : HasCompactSupport toFun
  tsupport_subset : tsupport toFun ⊆ U ×ˢ J

/-- Cutoffs `C¹_c(I × U)`: `C¹` functions on space-time (a `C¹` extension across an endpoint of
`I`, so one-sided derivatives at an endpoint in `I` are the ambient ones) vanishing on `U ×ˢ I`
outside a compact subset of `U ×ˢ I`.  They need not vanish at an endpoint of `I` belonging to
`I` (e.g. `t = 0` for `I = (-1,0]`). -/
structure ParCutoff {d : ℕ} (U : Set (Vec d)) (I : Set ℝ) where
  toFun : Vec d × ℝ → ℝ
  contDiff : ContDiff ℝ 1 toFun
  compact_support : ∃ Z : Set (Vec d × ℝ), IsCompact Z ∧ Z ⊆ U ×ˢ I ∧
    ∀ z ∈ U ×ˢ I, z ∉ Z → toFun z = 0

/-- `L²_c(U)`: `L²` on `U` and vanishing outside a compact subset of `U`. -/
def IsL2c {d : ℕ} (U : Set (Vec d)) (ψ : Vec d → ℝ) : Prop :=
  MemL2On U ψ ∧ ∃ K : Set (Vec d), IsCompact K ∧ K ⊆ U ∧ ∀ x, x ∉ K → ψ x = 0

/-- The parabolic energy space `H¹_par(I × U)` (Definition 5.1), at the level of
every-time representatives: a jointly measurable `u` and spatial gradient in `L²(U ×ˢ I)`
(`MemLp` includes joint a.e.-measurability), slices in `H¹(U)` with weak gradient for a.e. `t`,
every slice in `L²_loc(U)`, and weak continuity of `t ↦ ∫ u(t,·) ψ` on `I` for `ψ ∈ L²_c(U)`. -/
structure ParH1Function {d : ℕ} (U : Set (Vec d)) (I : Set ℝ) where
  toFun : Vec d × ℝ → ℝ
  grad : Vec d × ℝ → Vec d
  memL2 : MemLp toFun 2 (volume.restrict (U ×ˢ I))
  gradMemL2 : ∀ i : Fin d, MemLp (fun z => grad z i) 2 (volume.restrict (U ×ˢ I))
  sliceWeakGradient : ∀ᵐ t ∂(volume.restrict I),
    HasWeakGradientOn U (parSlice toFun t) (parSlice grad t)
  sliceL2loc : ∀ t ∈ I, ∀ K : Set (Vec d), IsCompact K → K ⊆ U →
    MemLp (parSlice toFun t) 2 (volume.restrict K)
  weakCont : ∀ ψ : Vec d → ℝ, IsL2c U ψ →
    ContinuousOn (fun t => ∫ x in U, toFun (x, t) * ψ x) I

/-- The integrand `-u ∂ₜφ + a∇u·∇φ` of the weak formulation. -/
noncomputable def parWeakIntegrand {d : ℕ} (a : ParCoeffField d) {U : Set (Vec d)} {I : Set ℝ}
    (u : ParH1Function U I) (φ : Vec d × ℝ → ℝ) (z : Vec d × ℝ) : ℝ :=
  -(u.toFun z * parTimeDeriv φ z) + vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad φ z)

/-- Weak solution of `∂ₜu - ∇·(a∇u) = 0` in `U × I` (Definition 5.4):
integrability and equality for all `φ ∈ C¹_c(interior I × U)`. -/
def IsParabolicWeakSolution {d : ℕ} (a : ParCoeffField d) (U : Set (Vec d)) (I : Set ℝ)
    (u : ParH1Function U I) : Prop :=
  ∀ φ : ParTestFunction U (interior I),
    IntegrableOn (parWeakIntegrand a u φ.toFun) (U ×ˢ I) ∧
      ∫ z in U ×ˢ I, parWeakIntegrand a u φ.toFun z = 0

/-- Weak subsolution: `≤ 0` for every nonnegative test function. -/
def IsParabolicWeakSubsolution {d : ℕ} (a : ParCoeffField d) (U : Set (Vec d)) (I : Set ℝ)
    (u : ParH1Function U I) : Prop :=
  ∀ φ : ParTestFunction U (interior I), (∀ z, 0 ≤ φ.toFun z) →
    IntegrableOn (parWeakIntegrand a u φ.toFun) (U ×ˢ I) ∧
      ∫ z in U ×ˢ I, parWeakIntegrand a u φ.toFun z ≤ 0

/-- Weak supersolution: `≥ 0` for every nonnegative test function. -/
def IsParabolicWeakSupersolution {d : ℕ} (a : ParCoeffField d) (U : Set (Vec d)) (I : Set ℝ)
    (u : ParH1Function U I) : Prop :=
  ∀ φ : ParTestFunction U (interior I), (∀ z, 0 ≤ φ.toFun z) →
    IntegrableOn (parWeakIntegrand a u φ.toFun) (U ×ˢ I) ∧
      0 ≤ ∫ z in U ×ˢ I, parWeakIntegrand a u φ.toFun z

end PDE
