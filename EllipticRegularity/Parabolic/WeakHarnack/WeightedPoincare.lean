module

public import EllipticRegularity.Parabolic.WeakHarnack.WeightedPoincareBall
public import EllipticRegularity.Parabolic.WeakHarnack.WeightedPoincareLayer

/-!
# Weighted Poincaré inequality for a radial cutoff weight

Let `ρ = ζ²` be a weight with `0 ≤ ρ ≤ 1` whose superlevel sets `{ρ > s}`, `0 ≤ s < 1`, are
round balls `B_{r(s)}` centered at the origin with `3/4 ≤ r(s) ≤ 7/8`.  Then for `u ∈ H¹(B₁)`
and `m = ∫ u ρ / ∫ ρ`,
`∫_{B₁} |u - m|² ρ ≤ C(d) ∫_{B₁} |∇u|² ρ`
with `C(d) = weightedPoincareConst d` independent of `u` and of the weight.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.Parabolic.WeakHarnack

open PDE

variable {d : ℕ}

/-- The hypothesis on the weight: superlevel sets are centered balls of radius in
`[3/4, 7/8]`. -/
def IsRadialLevelWeight (ρ : Vec d → ℝ) : Prop :=
  ∀ s : ℝ, 0 ≤ s → s < 1 →
    ∃ r : ℝ, 3 / 4 ≤ r ∧ r ≤ 7 / 8 ∧ {x | s < ρ x} = euclideanBall (0 : Vec d) r

theorem IsRadialLevelWeight.measurable {ρ : Vec d → ℝ} (h : IsRadialLevelWeight ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∀ x, ρ x ≤ 1) : Measurable ρ := by
  refine measurable_of_Ioi fun a => ?_
  by_cases ha0 : a < 0
  · have : ρ ⁻¹' Ioi a = univ := by
      ext x; simp only [mem_preimage, mem_Ioi, mem_univ, iff_true]; linarith [hρ0 x]
    rw [this]; exact MeasurableSet.univ
  by_cases ha1 : 1 ≤ a
  · have : ρ ⁻¹' Ioi a = ∅ := by
      ext x; simp only [mem_preimage, mem_Ioi, mem_empty_iff_false, iff_false, not_lt]
      linarith [hρ1 x]
    rw [this]; exact MeasurableSet.empty
  · obtain ⟨r, -, -, hr⟩ := h a (not_lt.1 ha0) (not_le.1 ha1)
    have : ρ ⁻¹' Ioi a = euclideanBall (0 : Vec d) r := hr
    rw [this]; exact (isOpen_euclideanBall 0 r).measurableSet

/-- **Weighted Poincaré inequality** for a radial weight with ball superlevel sets. -/
theorem weightedPoincare {ρ : Vec d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∀ x, ρ x ≤ 1)
    (hlevel : IsRadialLevelWeight ρ) {U : Set (Vec d)}
    (hU : euclideanBall (0 : Vec d) 1 ⊆ U) (u : H1Function U) :
    ∫ x in euclideanBall (0 : Vec d) 1,
        (u x - (∫ y in euclideanBall (0 : Vec d) 1, u y * ρ y) /
          (∫ y in euclideanBall (0 : Vec d) 1, ρ y)) ^ 2 * ρ x ≤
      weightedPoincareConst d *
        ∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (u.grad x) * ρ x := by
  set B := euclideanBall (0 : Vec d) 1 with hB
  have hfin : IsFiniteMeasure (volume.restrict B) :=
    isFiniteMeasure_restrict.mpr (volume_euclideanBall_ne_top 0 zero_le_one)
  have hρm : Measurable ρ := hlevel.measurable hρ0 hρ1
  have hρint : Integrable ρ (volume.restrict B) := integrable_weight hρm hρ0 hρ1
  -- positivity of the total weight
  have hρpos : 0 < ∫ y in B, ρ y := by
    obtain ⟨r, hr1, hr2, hr⟩ := hlevel 0 le_rfl zero_lt_one
    rw [integral_pos_iff_support_of_nonneg hρ0 hρint]
    have hsupp : Function.support ρ = euclideanBall (0 : Vec d) r := by
      rw [← hr]; ext x
      simp only [Function.mem_support, mem_ofPred_eq]
      exact ⟨fun h => lt_of_le_of_ne (hρ0 x) (Ne.symm h), fun h => h.ne'⟩
    rw [hsupp, Measure.restrict_apply (isOpen_euclideanBall 0 r).measurableSet,
      inter_eq_left.2 (euclideanBall_mono (by linarith) (by linarith))]
    exact volume_euclideanBall_pos 0 (by linarith)
  set m := (∫ y in B, u y * ρ y) / (∫ y in B, ρ y) with hm
  set c₀ := integralAverage (euclideanBall (0 : Vec d) (3 / 4)) u with hc₀
  have hu : MemLp u 2 (volume.restrict B) := memLp_ball u hU
  -- the weighted mean minimizes the weighted quadratic
  have hcm : ∫ x in B, (u x - m) * ρ x = 0 := by
    have h1 : Integrable (fun x => u x * ρ x) (volume.restrict B) :=
      integrable_mul_weight (hu.integrable one_le_two) hρm hρ0 hρ1
    have : (fun x => (u x - m) * ρ x) = fun x => u x * ρ x - m * ρ x := by
      funext x; ring
    rw [this, integral_sub h1 (hρint.const_mul m), integral_const_mul, hm]
    field_simp
    ring
  have hvar := weighted_sq_sub_eq (μ := volume.restrict B) hu hρm hρ0 hρ1 c₀ hcm
  have hmin : ∫ x in B, (u x - m) ^ 2 * ρ x ≤ ∫ x in B, (u x - c₀) ^ 2 * ρ x := by
    rw [hvar]
    have : 0 ≤ (m - c₀) ^ 2 * ∫ x in B, ρ x := mul_nonneg (sq_nonneg _) hρpos.le
    linarith
  -- layer cake
  have hlayer : ∫ x in B, (u x - c₀) ^ 2 * ρ x ≤
      weightedPoincareConst d * ∫ x in B, vecNormSq (u.grad x) * ρ x := by
    refine layerCake_mono (weightedPoincareConst_pos d).le (fun x => sq_nonneg _)
      (fun x => vecNormSq_nonneg _) (integrableOn_sq_ball u zero_le_one hU c₀)
      (integrableOn_grad_ball u hU) hρm hρ0 hρ1 ?_
    intro s hs
    obtain ⟨r, hr1, hr2, hr⟩ := hlevel s hs.1 hs.2
    have hsub : euclideanBall (0 : Vec d) r ⊆ B := euclideanBall_mono (by linarith) (by linarith)
    have hmeas : MeasurableSet (euclideanBall (0 : Vec d) r) := (isOpen_euclideanBall 0 r).measurableSet
    simp only [hr, Measure.restrict_restrict hmeas, inter_eq_left.2 hsub]
    exact shiftedPoincare_ball hU u hr1 hr2
  exact hmin.trans hlayer

end PDE.Parabolic.WeakHarnack
