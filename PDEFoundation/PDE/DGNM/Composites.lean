module

public import PDEFoundation.PDE.DGNM.ChainRule
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The composites `log u`, `u⁻¹`, `u ^ s` used by the De Giorgi-Nash-Moser tests

For `u ∈ H¹(U)` with `u ≥ δ > 0` a.e. (and `u ≤ M` a.e. for arbitrary real
powers):

* `logOfLowerBound`: value `Real.log (u x)`, gradient `(u x)⁻¹ • ∇u x`;
* `invOfLowerBound`: value `(u x)⁻¹`, gradient `(-((u x) ^ 2)⁻¹) • ∇u x`;
* `rpowOfLowerBound` (`s ≤ 1`): value `u x ^ s`, gradient `(s * u x ^ (s - 1)) • ∇u x`;
* `rpowOfBounds` (any real `s`, `δ ≤ u ≤ M`): same formulas.
-/

@[expose] public section

namespace PDE

namespace DGNM

open MeasureTheory

variable {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)

private theorem inv_le_two_div {δ t : ℝ} (hδ : 0 < δ) (ht : δ / 2 ≤ t) :
    t⁻¹ ≤ 2 / δ := by
  have htpos : 0 < t := lt_of_lt_of_le (by positivity) ht
  rw [inv_le_comm₀ htpos (by positivity)]
  field_simp
  linarith

/-- `log u` for `u ≥ δ > 0` a.e.: value `Real.log (u x)`, gradient
`(u x)⁻¹ • ∇u x`. -/
noncomputable def logOfLowerBound (u : H1Function U) {δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x) : H1Function U :=
  compOfLowerBound hU u hδ hu Real.log (fun t => t⁻¹)
    (fun _ ht => Real.hasDerivAt_log (ne_of_gt ht))
    (continuousOn_inv₀.mono fun _ ht => ne_of_gt ht)
    (B := 2 / δ) (fun t ht => by
      have htpos : 0 < t := lt_of_lt_of_le (by positivity) ht
      rw [abs_of_pos (inv_pos.mpr htpos)]
      exact inv_le_two_div hδ ht)

@[simp]
theorem logOfLowerBound_toFun (u : H1Function U) {δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x) :
    (logOfLowerBound hU u hδ hu).toFun = fun x => Real.log (u x) :=
  rfl

@[simp]
theorem logOfLowerBound_grad (u : H1Function U) {δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x) :
    (logOfLowerBound hU u hδ hu).grad = fun x => (u x)⁻¹ • u.grad x :=
  rfl

/-- `u⁻¹` for `u ≥ δ > 0` a.e.: value `(u x)⁻¹`, gradient
`(-((u x) ^ 2)⁻¹) • ∇u x`. -/
noncomputable def invOfLowerBound (u : H1Function U) {δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x) : H1Function U :=
  compOfLowerBound hU u hδ hu (fun t => t⁻¹) (fun t => -(t ^ 2)⁻¹)
    (fun _ ht => hasDerivAt_inv (ne_of_gt ht))
    (((continuousOn_pow 2).inv₀ fun _ ht => pow_ne_zero 2 (ne_of_gt ht)).neg)
    (B := (2 / δ) ^ 2) (fun t ht => by
      have htpos : 0 < t := lt_of_lt_of_le (by positivity) ht
      rw [abs_neg, abs_of_pos (inv_pos.mpr (pow_pos htpos 2)), ← inv_pow]
      exact pow_le_pow_left₀ (inv_nonneg.mpr htpos.le) (inv_le_two_div hδ ht) 2)

@[simp]
theorem invOfLowerBound_toFun (u : H1Function U) {δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x) :
    (invOfLowerBound hU u hδ hu).toFun = fun x => (u x)⁻¹ :=
  rfl

@[simp]
theorem invOfLowerBound_grad (u : H1Function U) {δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x) :
    (invOfLowerBound hU u hδ hu).grad = fun x => (-((u x) ^ 2)⁻¹) • u.grad x :=
  rfl

theorem rpow_hasDerivAt (s t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => t ^ s) (s * t ^ (s - 1)) t :=
  Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht))

theorem rpow_deriv_continuousOn (s : ℝ) :
    ContinuousOn (fun t : ℝ => s * t ^ (s - 1)) (Set.Ioi 0) :=
  continuousOn_const.mul
    (continuousOn_id.rpow_const fun _ ht => Or.inl (ne_of_gt ht))

/-- `u ^ s` for `u ≥ δ > 0` a.e. and `s ≤ 1`: value `u x ^ s`, gradient
`(s * u x ^ (s - 1)) • ∇u x`. -/
noncomputable def rpowOfLowerBound (u : H1Function U) {δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x) (s : ℝ) (hs : s ≤ 1) : H1Function U :=
  compOfLowerBound hU u hδ hu (fun t => t ^ s) (fun t => s * t ^ (s - 1))
    (rpow_hasDerivAt s) (rpow_deriv_continuousOn s)
    (B := |s| * (δ / 2) ^ (s - 1)) (fun t ht => by
      have htpos : 0 < t := lt_of_lt_of_le (by positivity) ht
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos htpos _)]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by positivity) ht (by linarith)) (abs_nonneg s))

@[simp]
theorem rpowOfLowerBound_toFun (u : H1Function U) {δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x) (s : ℝ) (hs : s ≤ 1) :
    (rpowOfLowerBound hU u hδ hu s hs).toFun = fun x => u x ^ s :=
  rfl

@[simp]
theorem rpowOfLowerBound_grad (u : H1Function U) {δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x) (s : ℝ) (hs : s ≤ 1) :
    (rpowOfLowerBound hU u hδ hu s hs).grad =
      fun x => (s * u x ^ (s - 1)) • u.grad x :=
  rfl

/-- `u ^ s` for `δ ≤ u ≤ M` a.e. (`0 < δ ≤ M`) and any real `s`: value
`u x ^ s`, gradient `(s * u x ^ (s - 1)) • ∇u x`. -/
noncomputable def rpowOfBounds (u : H1Function U) {δ M : ℝ} (hδ : 0 < δ) (hδM : δ ≤ M)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x ∧ u x ≤ M) (s : ℝ) : H1Function U :=
  compOfBounds hU u hδ hδM hu (fun t => t ^ s) (fun t => s * t ^ (s - 1))
    (rpow_hasDerivAt s) (rpow_deriv_continuousOn s)

@[simp]
theorem rpowOfBounds_toFun (u : H1Function U) {δ M : ℝ} (hδ : 0 < δ) (hδM : δ ≤ M)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x ∧ u x ≤ M) (s : ℝ) :
    (rpowOfBounds hU u hδ hδM hu s).toFun = fun x => u x ^ s :=
  rfl

@[simp]
theorem rpowOfBounds_grad (u : H1Function U) {δ M : ℝ} (hδ : 0 < δ) (hδM : δ ≤ M)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x ∧ u x ≤ M) (s : ℝ) :
    (rpowOfBounds hU u hδ hδM hu s).grad =
      fun x => (s * u x ^ (s - 1)) • u.grad x :=
  rfl

end DGNM

end PDE
