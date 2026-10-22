module

public import EllipticRegularity.Ch4.Meyers.Integrability
public import EllipticRegularity.Ch4.Meyers.Elliptic

/-!
# Pointwise bounds and `L²` membership for the profiles
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4Meyers

open MeasureTheory Set

variable {d : ℕ} {w : Fin d → ℝ}

theorem axisSq_le_vecNormSq (hw : ∀ i, w i = 0 ∨ w i = 1) (x : Vec d) :
    axisSq w x ≤ vecNormSq x := by
  rw [vecNormSq_eq_sum_sq]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases hw j with h | h <;> simp [h, sq_nonneg]

theorem axisSq_lt_one_of_mem_ball (hw : ∀ i, w i = 0 ∨ w i = 1) {x : Vec d}
    (hx : x ∈ euclideanBall (0 : Vec d) 1) : axisSq w x < 1 := by
  have : euclideanSqDist x 0 < 1 ^ 2 := hx
  have h2 : euclideanSqDist x 0 = vecNormSq x := by simp [euclideanSqDist]
  rw [h2] at this
  exact lt_of_le_of_lt (axisSq_le_vecNormSq hw x) (by simpa using this)

theorem abs_coord_le_sqrt (hw : ∀ i, w i = 0 ∨ w i = 1) {k : Fin d} (hk : w k = 1) (x : Vec d) :
    |x k| ≤ Real.sqrt (axisSq w x) := by
  apply Real.abs_le_sqrt
  exact sq_le_axisSq hw x hk

theorem rpow_mul_self_sqrt (x : ℝ) (hx : 0 < x) (γ : ℝ) :
    x ^ (γ - 1) * Real.sqrt x * Real.sqrt x = x ^ γ := by
  rw [mul_assoc, Real.mul_self_sqrt hx.le, Real.rpow_sub_one hx.ne']
  field_simp

theorem abs_prof_le_one (hw : ∀ i, w i = 0 ∨ w i = 1) {k : Fin d} (hk : w k = 1) {γ : ℝ}
    (hγ0 : -1 / 2 < γ) {x : Vec d} (hx : x ∈ euclideanBall (0 : Vec d) 1) :
    |prof w γ k x| ≤ 1 := by
  have hs1 := axisSq_lt_one_of_mem_ball hw hx
  rcases (axisSq_nonneg hw x).eq_or_lt with hs | hs
  · have : x k ^ 2 = 0 := le_antisymm (hs ▸ sq_le_axisSq hw x hk) (sq_nonneg _)
    have hxk : x k = 0 := pow_eq_zero_iff two_ne_zero |>.mp this
    simp [prof, hxk]
  · unfold prof
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hs.le _)]
    calc axisSq w x ^ γ * |x k| ≤ axisSq w x ^ γ * axisSq w x ^ (1 / 2 : ℝ) := by
          gcongr
          rw [← Real.sqrt_eq_rpow]; exact abs_coord_le_sqrt hw hk x
      _ = axisSq w x ^ (γ + 1 / 2) := by rw [Real.rpow_add hs]
      _ ≤ 1 := Real.rpow_le_one hs.le hs1.le (by linarith)

/-- Common shape of the gradient and flux components. -/
theorem abs_rpow_term_le (hw : ∀ i, w i = 0 ∨ w i = 1) {k : Fin d} (hk : w k = 1) (c γ : ℝ)
    (x : Vec d) (i : Fin d) :
    |axisSq w x ^ γ * (if k = i then 1 else 0) +
      c * axisSq w x ^ (γ - 1) * x k * (w i * x i)| ≤ (1 + |c|) * axisSq w x ^ γ := by
  have hs0 := axisSq_nonneg hw x
  have hpow : 0 ≤ axisSq w x ^ γ := Real.rpow_nonneg hs0 _
  have hA : |axisSq w x ^ γ * (if k = i then (1 : ℝ) else 0)| ≤ axisSq w x ^ γ := by
    split_ifs <;> simp [abs_of_nonneg hpow, hpow]
  have hB : |c * axisSq w x ^ (γ - 1) * x k * (w i * x i)| ≤ |c| * axisSq w x ^ γ := by
    rcases hs0.eq_or_lt with hs | hs
    · have : x k ^ 2 = 0 := le_antisymm (hs ▸ sq_le_axisSq hw x hk) (sq_nonneg _)
      have hxk : x k = 0 := pow_eq_zero_iff two_ne_zero |>.mp this
      simp [hxk]
      positivity
    · have hxk := abs_coord_le_sqrt hw hk x
      have hwx := abs_wx_le_sqrt hw x i
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs.le _)]
      calc |c| * axisSq w x ^ (γ - 1) * |x k| * |w i * x i|
          ≤ |c| * axisSq w x ^ (γ - 1) * Real.sqrt (axisSq w x) * Real.sqrt (axisSq w x) := by
            gcongr
        _ = |c| * axisSq w x ^ γ := by
            rw [mul_assoc, mul_assoc, ← mul_assoc (axisSq w x ^ (γ - 1)),
              rpow_mul_self_sqrt _ hs]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ axisSq w x ^ γ + |c| * axisSq w x ^ γ := add_le_add hA hB
    _ = _ := by ring

theorem measurable_prof (w : Fin d → ℝ) (γ : ℝ) (k : Fin d) : Measurable (prof w γ k) :=
  ((measurable_axisSq w).pow_const γ).mul (measurable_pi_apply k)

theorem measurable_rpow_term (w : Fin d → ℝ) (c γ : ℝ) (k i : Fin d) :
    Measurable (fun x : Vec d => axisSq w x ^ γ * (if k = i then 1 else 0) +
      c * axisSq w x ^ (γ - 1) * x k * (w i * x i)) := by
  have h1 := (measurable_axisSq w).pow_const γ
  have h2 := (measurable_axisSq w).pow_const (γ - 1)
  have h3 : Measurable (fun x : Vec d => w i * x i) := measurable_const.mul (measurable_pi_apply i)
  exact (h1.mul_const _).add (((h2.const_mul c).mul (measurable_pi_apply k)).mul h3)

theorem measurable_profGrad_apply (w : Fin d → ℝ) (γ : ℝ) (k i : Fin d) :
    Measurable (fun x : Vec d => profGrad w γ k x i) := by
  have := measurable_rpow_term w (2 * γ) γ k i
  exact this

theorem measurable_profFlux_apply (w : Fin d → ℝ) (Λ γ : ℝ) (k i : Fin d) :
    Measurable (fun x : Vec d => profFlux w Λ γ k x i) :=
  measurable_rpow_term w _ γ k i

theorem measurable_meyersCoeff_apply (w : Fin d → ℝ) (Λ : ℝ) (i j : Fin d) :
    Measurable (fun x : Vec d => meyersCoeff w Λ x i j) := by
  unfold meyersCoeff
  exact measurable_const.add (((measurable_const.mul (measurable_pi_apply i)).const_mul (Λ - 1)).mul
    ((measurable_pi_apply j).const_mul (w j)) |>.div (measurable_axisSq w))

/-- `L²` membership on the unit ball of a function dominated by `C s^γ`, `-1/2 < γ ≤ 0`. -/
theorem memLp_two_of_abs_le_rpow (hw : ∀ i, w i = 0 ∨ w i = 1) {i0 i1 : Fin d}
    (hi : i0 ≠ i1) (h0 : w i0 = 1) (h1 : w i1 = 1) {γ : ℝ} (hγ0 : -1 / 2 < γ) (hγ1 : γ ≤ 0)
    {g : Vec d → ℝ} (hg : Measurable g) {C : ℝ}
    (hb : ∀ᵐ x ∂(volume.restrict (euclideanBall (0 : Vec d) 1)), |g x| ≤ C * axisSq w x ^ γ) :
    MemLp g 2 (volume.restrict (euclideanBall (0 : Vec d) 1)) := by
  rw [memLp_two_iff_integrable_sq hg.aestronglyMeasurable]
  have hint : IntegrableOn (fun x : Vec d => axisSq w x ^ (-(-2 * γ)))
      (euclideanBall (0 : Vec d) 1) := by
    refine (integrableOn_axisSq_rpow_neg hw hi h0 h1 (e := -2 * γ) (by linarith)
      (by linarith) 1).mono_set ?_
    intro x hx j _
    have h2 : x j ^ 2 ≤ 1 := by
      have : euclideanSqDist x 0 < 1 ^ 2 := hx
      have h3 : euclideanSqDist x 0 = vecNormSq x := by simp [euclideanSqDist]
      rw [h3] at this
      exact le_trans (sq_apply_le_vecNormSq x j) (by simpa using this.le)
    exact abs_le.mp (abs_le_of_sq_le_sq (by simpa using h2) zero_le_one)
  refine ((hint.const_mul (C ^ 2))).mono' (hg.pow_const 2).aestronglyMeasurable ?_
  filter_upwards [hb] with x h1
  have hs0 := axisSq_nonneg hw x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  have h3 : (axisSq w x ^ γ) ^ 2 = axisSq w x ^ (-(-2 * γ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs0]
    congr 1; push_cast; ring
  have h2 : (C * axisSq w x ^ γ) ^ 2 = C ^ 2 * axisSq w x ^ (-(-2 * γ)) := by
    rw [mul_pow, h3]
  rw [← h2]
  exact pow_le_pow_left₀ (abs_nonneg _) h1 2

end PDE.Ch4Meyers
