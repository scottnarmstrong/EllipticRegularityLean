module

public import PDEFoundation.Monotonicity.ACF.WeightedWeakSq
public import PDEFoundation.Monotonicity.Poon.GaussianDeriv
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Radial integration by parts for `u ∇u`

For `u ∈ H¹(B_R)` continuous, `K` smooth with `K = 0` on `[ρ², ∞)` (`ρ < R`):

`∫_{B_R} u K(|x|²) (x · ∇u) = -½ ∫_{B_R} u² (d K(|x|²) + 2 |x|² K'(|x|²))`.

This is the weak form of `div (K(|x|²) x) = d K + 2 |x|² K'`, tested against the weak gradient
`2 u ∇u` of `u²`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

noncomputable section

variable {d : ℕ}

/-- The smooth vector-field component `K(|x|²) x_i`. -/
def radialField (K : ℝ → ℝ) (i : Fin d) (x : Vec d) : ℝ := K (vecNormSq x) * x i

theorem contDiff_radialField {K : ℝ → ℝ} (hK : ContDiff ℝ (⊤ : ℕ∞) K) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (radialField K i) :=
  (hK.comp contDiff_vecNormSq).mul (contDiff_apply ℝ ℝ i)

theorem radialField_eq_zero {K : ℝ → ℝ} {ρ : ℝ} (hK0 : ∀ s, ρ ^ 2 ≤ s → K s = 0) (i : Fin d)
    {x : Vec d} (hx : x ∉ euclideanClosedBall (0 : Vec d) ρ) : radialField K i x = 0 := by
  rw [mem_euclideanClosedBall_zero_iff, not_le] at hx
  simp [radialField, hK0 _ hx.le]

theorem hasCompactSupport_radialField {K : ℝ → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hK0 : ∀ s, ρ ^ 2 ≤ s → K s = 0) (i : Fin d) : HasCompactSupport (radialField K i) :=
  HasCompactSupport.intro (isCompact_euclideanClosedBall (0 : Vec d) hρ)
    fun _ hx => radialField_eq_zero hK0 i hx

theorem tsupport_radialField_subset {K : ℝ → ℝ} {ρ : ℝ} (hK0 : ∀ s, ρ ^ 2 ≤ s → K s = 0)
    (i : Fin d) : tsupport (radialField K i) ⊆ euclideanClosedBall (0 : Vec d) ρ := by
  refine closure_minimal ?_ ?_
  · intro x hx
    by_contra h
    exact hx (radialField_eq_zero hK0 i h)
  · have : euclideanClosedBall (0 : Vec d) ρ = {x | vecNormSq x ≤ ρ ^ 2} := by
      ext x; exact mem_euclideanClosedBall_zero_iff
    rw [this]
    exact isClosed_le continuous_vecNormSq continuous_const

theorem fderiv_radialField_basisVec {K : ℝ → ℝ} (hK : ContDiff ℝ (⊤ : ℕ∞) K) (i : Fin d)
    (x : Vec d) :
    (fderiv ℝ (radialField K i) x) (basisVec i) =
      K (vecNormSq x) + 2 * x i ^ 2 * deriv K (vecNormSq x) := by
  have hKd : HasDerivAt K (deriv K (vecNormSq x)) (vecNormSq x) :=
    ((hK.differentiable (by simp)) _).hasDerivAt
  have h1 : HasFDerivAt (fun y : Vec d => K (vecNormSq y))
      (deriv K (vecNormSq x) • vecNormSqFDeriv x) x := hKd.comp_hasFDerivAt x (hasFDerivAt_vecNormSq x)
  have h2 : HasFDerivAt (fun y : Vec d => y i)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) x :=
    hasFDerivAt_apply i x
  have h3 := h1.mul h2
  have h4 : fderiv ℝ (fun y : Vec d => K (vecNormSq y) * y i) x =
      K (vecNormSq x) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i +
        x i • deriv K (vecNormSq x) • vecNormSqFDeriv x := h3.fderiv
  rw [show radialField K i = fun y : Vec d => K (vecNormSq y) * y i from rfl, h4]
  simp only [add_apply, smul_apply, smul_eq_mul,
    vecNormSqFDeriv_basisVec, ContinuousLinearMap.proj_apply, basisVec_apply, ite_true]
  ring

theorem deriv_eq_zero_of_support {K : ℝ → ℝ} {ρ : ℝ} (hK0 : ∀ s, ρ ^ 2 ≤ s → K s = 0) {s : ℝ}
    (hs : ρ ^ 2 < s) : deriv K s = 0 := by
  have : K =ᶠ[nhds s] fun _ => 0 := by
    filter_upwards [lt_mem_nhds hs] with t ht using hK0 t ht.le
  rw [this.deriv_eq]; simp

/-- **Radial integration by parts.** -/
theorem integral_radial_ibp {R : ℝ} (u : H1Function (euclideanBall (0 : Vec d) R))
    (hcont : ContinuousOn u.toFun (euclideanBall (0 : Vec d) R)) {K : ℝ → ℝ}
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) {ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hK0 : ∀ s, ρ ^ 2 ≤ s → K s = 0) :
    ∫ x in euclideanBall (0 : Vec d) R,
        u.toFun x * (K (vecNormSq x) * vecDot x (u.grad x)) =
      -(1 / 2) * ∫ x in euclideanBall (0 : Vec d) R,
        u.toFun x ^ 2 * (d * K (vecNormSq x) + 2 * vecNormSq x * deriv K (vecNormSq x)) := by
  set ρ' : ℝ := (ρ + R) / 2 with hρ'
  have hρ'pos : 0 < ρ' := by rw [hρ']; linarith
  have hρ'R : ρ' < R := by rw [hρ']; linarith
  have hρρ' : ρ < ρ' := by rw [hρ']; linarith
  have hweak := hasWeakGradient_sq_ball u hcont hρ'pos hρ'R
  set Ub := euclideanBall (0 : Vec d) ρ' with hUb
  have hUbR : Ub ⊆ euclideanBall (0 : Vec d) R := euclideanBall_zero_subset hρ'R.le hρ'pos.le
  have hUbMeas : MeasurableSet Ub := (isOpen_euclideanBall (0 : Vec d) ρ').measurableSet
  have hRMeas : MeasurableSet (euclideanBall (0 : Vec d) R) :=
    (isOpen_euclideanBall (0 : Vec d) R).measurableSet
  -- the vanishing region
  have hclosedUb : euclideanClosedBall (0 : Vec d) ρ ⊆ Ub := by
    intro x hx
    rw [mem_euclideanClosedBall_zero_iff] at hx
    rw [hUb, mem_euclideanBall_zero_iff]
    nlinarith
  -- integrability facts
  have hu2 : IntegrableOn (fun x => u.toFun x ^ 2) Ub := by
    have h := (show MemLp u.toFun 2 (volume.restrict (euclideanBall (0 : Vec d) R)) from
      u.memL2).integrable_sq
    exact (h.mono_measure (Measure.restrict_mono hUbR le_rfl))
  have hDcont (i : Fin d) : Continuous (fun x : Vec d =>
      K (vecNormSq x) + 2 * x i ^ 2 * deriv K (vecNormSq x)) :=
    (hK.continuous.comp continuous_vecNormSq).add
      ((continuous_const.mul ((continuous_apply i).pow 2)).mul
        ((hK.continuous_deriv (by simp)).comp continuous_vecNormSq))
  have hDcs (i : Fin d) : HasCompactSupport (fun x : Vec d =>
      K (vecNormSq x) + 2 * x i ^ 2 * deriv K (vecNormSq x)) := by
    refine HasCompactSupport.intro (isCompact_euclideanClosedBall (0 : Vec d) hρ.le) ?_
    intro x hx
    rw [mem_euclideanClosedBall_zero_iff, not_le] at hx
    simp [hK0 _ hx.le, deriv_eq_zero_of_support hK0 hx]
  have hInt1 (i : Fin d) : IntegrableOn (fun x => u.toFun x ^ 2 *
      (K (vecNormSq x) + 2 * x i ^ 2 * deriv K (vecNormSq x))) Ub := by
    obtain ⟨C, hC⟩ := (hDcont i).bounded_above_of_compact_support (hDcs i)
    refine Integrable.mul_bdd (c := C) hu2 (hDcont i).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => by simpa using hC x
  have hφcont (i : Fin d) : Continuous (radialField K i) := (contDiff_radialField hK i).continuous
  have hInt2 (i : Fin d) : IntegrableOn (fun x => (2 * u.toFun x * u.grad x i) *
      radialField K i x) Ub := by
    obtain ⟨C, hC⟩ := (hφcont i).bounded_above_of_compact_support
      (hasCompactSupport_radialField hρ.le hK0 i)
    have hprod : Integrable (fun x => u.toFun x * u.grad x i) (volume.restrict Ub) := by
      have h1 : MemLp u.toFun 2 (volume.restrict (euclideanBall (0 : Vec d) R)) := u.memL2
      have h2 : MemLp (fun x => u.grad x i) 2 (volume.restrict (euclideanBall (0 : Vec d) R)) :=
        u.gradMemL2 i
      have := h1.integrable_mul h2
      exact this.mono_measure (Measure.restrict_mono hUbR le_rfl)
    have hprod2 : Integrable (fun x => 2 * u.toFun x * u.grad x i) (volume.restrict Ub) := by
      simpa only [mul_assoc] using hprod.const_mul 2
    refine Integrable.mul_bdd (c := C) hprod2 (hφcont i).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => by simpa using hC x
  -- weak identity for each coordinate
  have hkey (i : Fin d) : ∫ x in Ub, u.toFun x ^ 2 *
        (K (vecNormSq x) + 2 * x i ^ 2 * deriv K (vecNormSq x)) =
      -∫ x in Ub, (2 * u.toFun x * u.grad x i) * radialField K i x := by
    have := hweak i (radialField K i) (contDiff_radialField hK i)
      (hasCompactSupport_radialField hρ.le hK0 i)
      ((tsupport_radialField_subset hK0 i).trans hclosedUb)
    simp only [fderiv_radialField_basisVec hK] at this
    exact this
  -- sum over coordinates
  have hsumL : ∫ x in Ub, u.toFun x ^ 2 *
        (d * K (vecNormSq x) + 2 * vecNormSq x * deriv K (vecNormSq x)) =
      ∑ i, ∫ x in Ub, u.toFun x ^ 2 *
        (K (vecNormSq x) + 2 * x i ^ 2 * deriv K (vecNormSq x)) := by
    rw [← integral_finsetSum _ (fun i _ => hInt1 i)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum]
    rw [← vecNormSq_eq_sum_sq]
  have hsumR : ∫ x in Ub, u.toFun x * (K (vecNormSq x) * vecDot x (u.grad x)) =
      (1 / 2) * ∑ i, ∫ x in Ub, (2 * u.toFun x * u.grad x i) * radialField K i x := by
    rw [← integral_finsetSum _ (fun i _ => hInt2 i), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [vecDot, radialField, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hL : ∫ x in Ub, u.toFun x * (K (vecNormSq x) * vecDot x (u.grad x)) =
      -(1 / 2) * ∫ x in Ub, u.toFun x ^ 2 *
        (d * K (vecNormSq x) + 2 * vecNormSq x * deriv K (vecNormSq x)) := by
    rw [hsumR, hsumL, Finset.sum_congr rfl (fun i _ => hkey i), Finset.sum_neg_distrib]
    ring
  -- pass from `Ub` to the full ball
  have hvanish1 : ∫ x in euclideanBall (0 : Vec d) R,
        u.toFun x * (K (vecNormSq x) * vecDot x (u.grad x)) =
      ∫ x in Ub, u.toFun x * (K (vecNormSq x) * vecDot x (u.grad x)) := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hRMeas hUbR ?_
    intro x hx
    have : ρ ^ 2 ≤ vecNormSq x := by
      by_contra h
      rw [not_le] at h
      apply hx.2
      rw [hUb, mem_euclideanBall_zero_iff]
      nlinarith
    simp [hK0 _ this]
  have hvanish2 : ∫ x in euclideanBall (0 : Vec d) R, u.toFun x ^ 2 *
        (d * K (vecNormSq x) + 2 * vecNormSq x * deriv K (vecNormSq x)) =
      ∫ x in Ub, u.toFun x ^ 2 *
        (d * K (vecNormSq x) + 2 * vecNormSq x * deriv K (vecNormSq x)) := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hRMeas hUbR ?_
    intro x hx
    have : ρ ^ 2 < vecNormSq x := by
      by_contra h
      rw [not_lt] at h
      apply hx.2
      rw [hUb, mem_euclideanBall_zero_iff]
      nlinarith
    simp [hK0 _ this.le, deriv_eq_zero_of_support hK0 this]
  rw [hvanish1, hvanish2, hL]

end

end PDE
