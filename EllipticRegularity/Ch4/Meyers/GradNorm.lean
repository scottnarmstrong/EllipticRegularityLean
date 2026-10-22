module

public import EllipticRegularity.Ch4.Meyers.H1
public import EllipticRegularity.Ch4.Meyers.NonIntegrability

/-!
# The Euclidean size of the gradient of `s^γ x_k`

With `β = 2γ + 1 ∈ (0,1]` one has `β s^γ ≤ |∇(s^γ x_k)| ≤ s^γ` off the singular set, and
`∇(s^γ x_k) ∈ L^p` on a ball if and only if `p (1-β) < 2` (planar case).
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4Meyers

open MeasureTheory Set

variable {d : ℕ} {w : Fin d → ℝ}

theorem vecNormSq_profGrad (hw : ∀ i, w i = 0 ∨ w i = 1) {k : Fin d} (hk : w k = 1) (γ : ℝ)
    {x : Vec d} (hs : 0 < axisSq w x) :
    vecNormSq (profGrad w γ k x) =
      (axisSq w x ^ γ) ^ 2 * (1 - (1 - (2 * γ + 1) ^ 2) * (x k ^ 2 / axisSq w x)) := by
  have hrs : axisSq w x ^ (γ - 1) = axisSq w x ^ γ / axisSq w x := Real.rpow_sub_one hs.ne' γ
  have hsum := sum_wx_sq hw x
  have hG : ∀ j, profGrad w γ k x j =
      axisSq w x ^ γ * (if k = j then 1 else 0) +
        2 * γ * (axisSq w x ^ γ / axisSq w x) * x k * (w j * x j) := by
    intro j; simp only [profGrad, hrs]
  generalize axisSq w x ^ γ = P at hG ⊢
  generalize hsx : axisSq w x = s at *
  have h1 : ∀ j, profGrad w γ k x j ^ 2 =
      P ^ 2 * (if k = j then 1 else 0) +
        4 * γ * P ^ 2 * x k / s * ((if k = j then 1 else 0) * (w j * x j)) +
        (2 * γ * P * x k / s) ^ 2 * (w j * x j) ^ 2 := by
    intro j
    rw [hG j]
    by_cases hkj : k = j
    · simp only [hkj, ite_true]; field_simp; ring
    · simp only [hkj, ite_false]; field_simp; ring
  rw [vecNormSq_eq_sum_sq]
  simp_rw [h1]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]
  rw [hsum]
  simp only [ite_mul, one_mul, zero_mul, mul_one, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, hk]
  field_simp
  ring

theorem vecEuclideanNorm_profGrad_bounds (hw : ∀ i, w i = 0 ∨ w i = 1) {k : Fin d}
    (hk : w k = 1) {γ : ℝ} (hγ0 : -1 / 2 < γ) (hγ1 : γ ≤ 0) {x : Vec d}
    (hs : 0 < axisSq w x) :
    (2 * γ + 1) * axisSq w x ^ γ ≤ vecEuclideanNorm (profGrad w γ k x) ∧
      vecEuclideanNorm (profGrad w γ k x) ≤ axisSq w x ^ γ := by
  have hP : 0 ≤ axisSq w x ^ γ := Real.rpow_nonneg hs.le _
  have hβ0 : 0 < 2 * γ + 1 := by linarith
  have hβ1 : 2 * γ + 1 ≤ 1 := by linarith
  have ht0 : 0 ≤ x k ^ 2 / axisSq w x := div_nonneg (sq_nonneg _) hs.le
  have ht1 : x k ^ 2 / axisSq w x ≤ 1 := by
    rw [div_le_one hs]; exact sq_le_axisSq hw x hk
  have hβsq : (2 * γ + 1) ^ 2 ≤ 1 := by nlinarith
  rw [vecEuclideanNorm, vecNormSq_profGrad hw hk γ hs]
  constructor
  · apply Real.le_sqrt_of_sq_le
    rw [mul_pow]
    have := mul_nonneg (mul_nonneg (sq_nonneg (axisSq w x ^ γ)) (by linarith : 0 ≤ 1 - (2 * γ + 1) ^ 2))
      (sub_nonneg.mpr ht1)
    nlinarith [this]
  · apply Real.sqrt_le_iff.mpr
    refine ⟨hP, ?_⟩
    have : 0 ≤ (1 - (2 * γ + 1) ^ 2) * (x k ^ 2 / axisSq w x) :=
      mul_nonneg (by linarith) ht0
    nlinarith [sq_nonneg (axisSq w x ^ γ)]

theorem euclideanBall_subset_cube {ρ : ℝ} (hρ : 0 ≤ ρ) :
    euclideanBall (0 : Vec d) ρ ⊆ Set.pi univ fun _ => Icc (-ρ) ρ := by
  intro x hx j _
  have h2 : euclideanSqDist x 0 < ρ ^ 2 := hx
  have h3 : euclideanSqDist x 0 = vecNormSq x := by simp [euclideanSqDist]
  rw [h3] at h2
  have h4 : x j ^ 2 ≤ ρ ^ 2 := le_trans (sq_apply_le_vecNormSq x j) h2.le
  exact abs_le.mp (abs_le_of_sq_le_sq h4 hρ)

theorem measurable_vecEuclideanNorm_profGrad (w : Fin d → ℝ) (γ : ℝ) (k : Fin d) :
    Measurable (fun x : Vec d => vecEuclideanNorm (profGrad w γ k x)) :=
  continuous_vecEuclideanNorm.measurable.comp
    (measurable_pi_iff.mpr fun i => measurable_profGrad_apply w γ k i)

/-- `∇(s^γ x_{i0}) ∈ L^p` on a ball if and only if `p (-γ) < 1` (planar weights). -/
theorem memLp_gradNorm_iff (hw : ∀ i, w i = 0 ∨ w i = 1) {i0 i1 : Fin d} (hi : i0 ≠ i1)
    (h0 : w i0 = 1) (h1 : w i1 = 1) (hrest : ∀ j, j ≠ i0 → j ≠ i1 → w j = 0) {γ : ℝ}
    (hγ0 : -1 / 2 < γ) (hγ1 : γ < 0) {ρ : ℝ} (hρ : 0 < ρ) {p : ℝ} (hp : 0 < p) :
    MemLp (fun x => vecEuclideanNorm (profGrad w γ i0 x)) (ENNReal.ofReal p)
        (volume.restrict (euclideanBall (0 : Vec d) ρ)) ↔ p * (-γ) < 1 := by
  set μ := volume.restrict (euclideanBall (0 : Vec d) ρ) with hμ
  set g : Vec d → ℝ := fun x => vecEuclideanNorm (profGrad w γ i0 x) with hg
  have hgm : Measurable g := measurable_vecEuclideanNorm_profGrad w γ i0
  have hp0 : ENNReal.ofReal p ≠ 0 := by simpa using hp
  rw [← integrable_norm_rpow_iff hgm.aestronglyMeasurable hp0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le]
  set e : ℝ := p * (-γ) with he
  have he0 : 0 ≤ e := by rw [he]; nlinarith
  set β : ℝ := 2 * γ + 1 with hβ
  have hβ0 : 0 < β := by rw [hβ]; linarith
  let H : Vec d → ℝ := fun x => axisSq w x ^ (-e)
  have hHm : Measurable H := (measurable_axisSq w).pow_const _
  have hFm : Measurable (fun x => ‖g x‖ ^ p) := (hgm.norm).pow_const p
  have hbounds : ∀ᵐ x ∂μ, β ^ p * H x ≤ ‖g x‖ ^ p ∧ ‖g x‖ ^ p ≤ H x := by
    have hpos := ae_axisSq_pos hw h0 (euclideanBall (0 : Vec d) ρ)
    filter_upwards [hpos] with x hx
    obtain ⟨hlo, hhi⟩ := vecEuclideanNorm_profGrad_bounds hw h0 hγ0 hγ1.le hx
    have hHx : H x = (axisSq w x ^ γ) ^ p := by
      simp only [H, he]
      rw [← Real.rpow_mul hx.le]; congr 1; ring
    have hn : ‖g x‖ = g x := Real.norm_of_nonneg (vecEuclideanNorm_nonneg _)
    rw [hn, hHx]
    have hP : 0 ≤ axisSq w x ^ γ := Real.rpow_nonneg hx.le _
    constructor
    · rw [← Real.mul_rpow hβ0.le hP]
      exact Real.rpow_le_rpow (mul_nonneg hβ0.le hP) hlo hp.le
    · exact Real.rpow_le_rpow (vecEuclideanNorm_nonneg _) hhi hp.le
  have hcube : IntegrableOn H (euclideanBall (0 : Vec d) ρ) ↔ e < 1 := by
    constructor
    · intro hint
      by_contra hcon
      exact not_integrableOn_axisSq_rpow_neg hi h0 h1 hrest (not_lt.mp hcon) hρ hint
    · intro he1
      exact (integrableOn_axisSq_rpow_neg hw hi h0 h1 he0 he1 ρ).mono_set
        (euclideanBall_subset_cube hρ.le)
  rw [← hcube]
  constructor
  · intro hF
    have hc : 0 < β ^ p := Real.rpow_pos_of_pos hβ0 p
    refine (hF.const_mul ((β ^ p)⁻¹)).mono' hHm.aestronglyMeasurable ?_
    filter_upwards [hbounds] with x hx
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (axisSq_nonneg hw x) _)]
    rw [inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
    exact hx.1
  · intro hH
    exact hH.mono' hFm.aestronglyMeasurable (by
      filter_upwards [hbounds] with x hx
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact hx.2)

end PDE.Ch4Meyers
