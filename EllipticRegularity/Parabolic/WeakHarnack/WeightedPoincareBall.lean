module

public import EllipticRegularity.Parabolic.WeakHarnack.WeightedPoincareVariational
public import PDEFoundation.Sobolev.Inequalities.ConvexPoincareL2
public import PDEFoundation.Measure.BallVolume

/-!
# Shifted-mean Poincaré inequality on intermediate balls

For `u ∈ H¹(U)` with `B₁ ⊆ U`, `c` the mean of `u` over `B_{3/4}` and `3/4 ≤ r ≤ 7/8`,
`∫_{B_r} |u - c|² ≤ C(d) ∫_{B_r} |∇u|²`, with `C(d) = weightedPoincareConst d`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.Parabolic.WeakHarnack

open PDE

/-- The dimensional constant of the weighted Poincaré inequality. -/
noncomputable def weightedPoincareConst (d : ℕ) : ℝ :=
  2 * (1 + (7 / 6 : ℝ) ^ d) * ((2 : ℝ) ^ d * (7 / 4)) ^ 2

theorem weightedPoincareConst_pos (d : ℕ) : 0 < weightedPoincareConst d := by
  unfold weightedPoincareConst; positivity

section Ball

variable {d : ℕ} {U : Set (Vec d)}

theorem memLp_ball (u : H1Function U) {R : ℝ} (hR : euclideanBall (0 : Vec d) R ⊆ U) :
    MemLp u 2 (volume.restrict (euclideanBall (0 : Vec d) R)) :=
  u.memL2.mono_measure (Measure.restrict_mono hR le_rfl)

theorem integrableOn_sq_ball (u : H1Function U) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : euclideanBall (0 : Vec d) R ⊆ U) (a : ℝ) :
    IntegrableOn (fun x => (u x - a) ^ 2) (euclideanBall (0 : Vec d) R) volume := by
  have : IsFiniteMeasure (volume.restrict (euclideanBall (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.mpr (volume_euclideanBall_ne_top 0 hR0)
  exact ((memLp_ball u hR).sub (memLp_const a)).integrable_sq

theorem integrableOn_grad_ball (u : H1Function U) {R : ℝ}
    (hR : euclideanBall (0 : Vec d) R ⊆ U) :
    IntegrableOn (fun x => vecNormSq (u.grad x)) (euclideanBall (0 : Vec d) R) volume :=
  (integrableOn_vecNormSq_of_memVectorL2On u.gradMemL2).mono_set hR

/-- Shifted-mean Poincaré inequality on `B_r`, `3/4 ≤ r ≤ 7/8`. -/
theorem shiftedPoincare_ball (hU : euclideanBall (0 : Vec d) 1 ⊆ U) (u : H1Function U)
    {r : ℝ} (hr : 3 / 4 ≤ r) (hr' : r ≤ 7 / 8) :
    ∫ x in euclideanBall (0 : Vec d) r,
        (u x - integralAverage (euclideanBall (0 : Vec d) (3 / 4)) u) ^ 2 ≤
      weightedPoincareConst d * ∫ x in euclideanBall (0 : Vec d) r, vecNormSq (u.grad x) := by
  set V := euclideanBall (0 : Vec d) r with hVdef
  set W := euclideanBall (0 : Vec d) (3 / 4) with hWdef
  have hr0 : 0 < r := by linarith
  have hVU : V ⊆ U := (euclideanBall_mono hr0.le (by linarith)).trans hU
  have hWV : W ⊆ V := euclideanBall_mono (by norm_num) hr
  have hWU : W ⊆ U := hWV.trans hVU
  set c := integralAverage W u with hc
  set a := integralAverage V u with ha
  -- the ball Poincaré inequality on `V`
  have hP : ∫ x in V, (u x - a) ^ 2 ≤ ((2 : ℝ) ^ d * (2 * r)) ^ 2 *
      ∫ x in V, vecNormSq (u.grad x) :=
    centeredPoincare_sq_on_boundedConvexSubdomain u
      (isOpenBoundedConvexDomain_euclideanBall 0 hr0) hVU
      (hasEuclideanDiameterLE_euclideanBall 0 hr0) (by linarith)
      (euclideanBall_nonempty 0 hr0)
  have hPle : ((2 : ℝ) ^ d * (2 * r)) ^ 2 ≤ ((2 : ℝ) ^ d * (7 / 4)) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hgrad_nn : 0 ≤ ∫ x in V, vecNormSq (u.grad x) :=
    setIntegral_nonneg_of_ae_restrict (Filter.Eventually.of_forall fun x => vecNormSq_nonneg _)
  -- volumes
  have hWpos : 0 < (volume W).toReal := volume_euclideanBall_toReal_pos 0 (by norm_num)
  have hVpos : 0 < (volume V).toReal := volume_euclideanBall_toReal_pos 0 hr0
  have hratio : (volume V).toReal ≤ (7 / 6 : ℝ) ^ d * (volume W).toReal := by
    have h := volume_euclideanBall_toReal_div_eq_div_pow (0 : Vec d) (0 : Vec d)
      (r := 3 / 4) (R := r) (by norm_num) hr0
    rw [div_eq_iff hWpos.ne'] at h
    rw [h]
    refine mul_le_mul_of_nonneg_right ?_ hWpos.le
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_iff₀ (by norm_num)]; linarith
  -- variational identity on `W`
  have hfinV : IsFiniteMeasure (volume.restrict V) :=
    isFiniteMeasure_restrict.mpr (volume_euclideanBall_ne_top 0 hr0.le)
  have : IsFiniteMeasure (volume.restrict W) :=
    isFiniteMeasure_restrict.mpr (volume_euclideanBall_ne_top 0 (by norm_num))
  have hcW : ∫ x in W, (u x - c) * (fun _ => (1 : ℝ)) x = 0 := by
    have hint : IntegrableOn u W volume := (memLp_ball u hWU).integrable one_le_two
    simp only [mul_one]
    rw [integral_sub hint (integrable_const c), setIntegral_const, hc, integralAverage]
    simp only [smul_eq_mul, Measure.real]
    field_simp
    ring
  have hvar := weighted_sq_sub_eq (μ := volume.restrict W) (g := u) (ρ := fun _ => (1 : ℝ))
    (memLp_ball u hWU) measurable_const (fun _ => zero_le_one) (fun _ => le_rfl) a hcW
  simp only [mul_one] at hvar
  have hWvol : ∫ x in W, (1 : ℝ) = (volume W).toReal := by
    simp [Measure.real]
  rw [hWvol] at hvar
  have hWmono : ∫ x in W, (u x - a) ^ 2 ≤ ∫ x in V, (u x - a) ^ 2 :=
    setIntegral_mono_set (integrableOn_sq_ball u hr0.le hVU a)
      (Filter.Eventually.of_forall fun x => sq_nonneg _) (Filter.Eventually.of_forall hWV)
  have hWc : ∫ x in W, (u x - c) ^ 2 ≥ 0 :=
    setIntegral_nonneg_of_ae_restrict (Filter.Eventually.of_forall fun x => sq_nonneg _)
  have hkey : (volume W).toReal * (c - a) ^ 2 ≤ ∫ x in V, (u x - a) ^ 2 := by
    nlinarith
  -- compare with `c`
  have hpt : ∫ x in V, (u x - c) ^ 2 ≤
      2 * (∫ x in V, (u x - a) ^ 2) + 2 * ((volume V).toReal * (a - c) ^ 2) := by
    have h1 : IntegrableOn (fun x => 2 * (u x - a) ^ 2 + 2 * (a - c) ^ 2) V volume :=
      ((integrableOn_sq_ball u hr0.le hVU a).const_mul 2).add (integrable_const _)
    calc ∫ x in V, (u x - c) ^ 2
        ≤ ∫ x in V, (2 * (u x - a) ^ 2 + 2 * (a - c) ^ 2) := by
          apply setIntegral_mono (integrableOn_sq_ball u hr0.le hVU c) h1
          intro x
          nlinarith [sq_nonneg (u x - a - (a - c))]
      _ = _ := by
          rw [integral_add ((integrableOn_sq_ball u hr0.le hVU a).const_mul 2) (integrable_const _),
            integral_const_mul, setIntegral_const]
          simp only [smul_eq_mul, Measure.real]
          generalize (∫ x in V, (u x - a) ^ 2) = I
          ring
  have hsq : (volume V).toReal * (a - c) ^ 2 ≤
      (7 / 6 : ℝ) ^ d * ∫ x in V, (u x - a) ^ 2 := by
    have : (a - c) ^ 2 = (c - a) ^ 2 := by ring
    rw [this]
    calc (volume V).toReal * (c - a) ^ 2
        ≤ ((7 / 6 : ℝ) ^ d * (volume W).toReal) * (c - a) ^ 2 :=
          mul_le_mul_of_nonneg_right hratio (sq_nonneg _)
      _ = (7 / 6 : ℝ) ^ d * ((volume W).toReal * (c - a) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hkey (by positivity)
  have hQ : 0 ≤ ∫ x in V, (u x - a) ^ 2 :=
    setIntegral_nonneg_of_ae_restrict (Filter.Eventually.of_forall fun x => sq_nonneg _)
  calc ∫ x in V, (u x - c) ^ 2
      ≤ 2 * (1 + (7 / 6 : ℝ) ^ d) * ∫ x in V, (u x - a) ^ 2 := by nlinarith
    _ ≤ 2 * (1 + (7 / 6 : ℝ) ^ d) * (((2 : ℝ) ^ d * (7 / 4)) ^ 2 *
          ∫ x in V, vecNormSq (u.grad x)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hP.trans (mul_le_mul_of_nonneg_right hPle hgrad_nn)
    _ = _ := by unfold weightedPoincareConst; ring

end Ball

end PDE.Parabolic.WeakHarnack
