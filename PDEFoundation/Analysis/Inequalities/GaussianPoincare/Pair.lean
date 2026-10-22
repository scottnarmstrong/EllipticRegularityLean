module

public import PDEFoundation.Analysis.Inequalities.GaussianPoincare.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The product heat kernel on `Vec d × Vec d`

`pairHeat t (x, y) = Φ(t,x) Φ(t,y)`, with integrability of polynomial-weighted versions and its
line derivatives.
-/

@[expose] public section

open MeasureTheory Real

namespace PDE.GaussianPoincare

/-- The squared Euclidean norm on the product `Vec d × Vec d`. -/
def pairNormSq {d : ℕ} (p : Vec d × Vec d) : ℝ := vecNormSq p.1 + vecNormSq p.2

/-- The product heat kernel. -/
noncomputable def pairHeat (d : ℕ) (t : ℝ) (p : Vec d × Vec d) : ℝ :=
  heat d t p.1 * heat d t p.2

theorem pairHeat_eq {d : ℕ} (t : ℝ) (p : Vec d × Vec d) :
    pairHeat d t p = ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) * (4 * Real.pi * t) ^ (-(d : ℝ) / 2)) *
      Real.exp (-(1 / (4 * t)) * pairNormSq p) := by
  unfold pairHeat pairNormSq
  rw [heat_eq_mul_exp, heat_eq_mul_exp, mul_add, Real.exp_add]
  ring

theorem pairHeat_nonneg {d : ℕ} {t : ℝ} (ht : 0 < t) (p : Vec d × Vec d) :
    0 ≤ pairHeat d t p :=
  mul_nonneg (heat_nonneg ht _) (heat_nonneg ht _)

theorem continuous_pairHeat {d : ℕ} (t : ℝ) : Continuous (pairHeat d t : Vec d × Vec d → ℝ) :=
  ((continuous_heat t).comp continuous_fst).mul ((continuous_heat t).comp continuous_snd)

theorem integrable_pairHeat {d : ℕ} {t : ℝ} (ht : 0 < t) :
    Integrable (pairHeat d t : Vec d × Vec d → ℝ) (volume.prod volume) :=
  (integrable_heat ht).mul_prod (integrable_heat ht)

theorem integrable_exp_neg_mul_pairNormSq {d : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun p : Vec d × Vec d => Real.exp (-b * pairNormSq p)) (volume.prod volume) := by
  have : (fun p : Vec d × Vec d => Real.exp (-b * pairNormSq p)) =
      fun p => Real.exp (-b * vecNormSq p.1) * Real.exp (-b * vecNormSq p.2) := by
    funext p
    rw [← Real.exp_add, pairNormSq, mul_add]
  rw [this]
  exact (integrable_exp_neg_mul_vecNormSq hb).mul_prod (integrable_exp_neg_mul_vecNormSq hb)

theorem norm_le_one_add_vecNormSq {d : ℕ} (x : Vec d) : ‖x‖ ≤ 1 + vecNormSq x := by
  have h0 := vecNormSq_nonneg x
  refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun i => ?_
  have := sq_apply_le_vecNormSq x i
  rw [Real.norm_eq_abs]
  nlinarith [abs_nonneg (x i), sq_abs (x i), sq_nonneg (|x i| - 1)]

theorem integrable_norm_mul_pairHeat {d : ℕ} {t : ℝ} (ht : 0 < t) :
    Integrable (fun p : Vec d × Vec d => (‖p.1‖ + ‖p.2‖) * pairHeat d t p) (volume.prod volume) := by
  set a : ℝ := 1 / (4 * t) with ha
  have ha0 : 0 < a := by positivity
  have hint := (integrable_exp_neg_mul_pairNormSq (d := d) (b := a / 2) (by positivity)).const_mul
    ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) * (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * (2 + 2 / a))
  refine Integrable.mono' hint ?_ ?_
  · exact ((continuous_norm.comp continuous_fst).add
      (continuous_norm.comp continuous_snd)).mul (continuous_pairHeat t) |>.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun p => ?_
    have hN : 0 ≤ pairNormSq p := add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _)
    have h1 : ‖p.1‖ + ‖p.2‖ ≤ 2 + pairNormSq p := by
      have := norm_le_one_add_vecNormSq p.1
      have := norm_le_one_add_vecNormSq p.2
      unfold pairNormSq
      linarith
    have h2 : 2 + pairNormSq p ≤ (2 + 2 / a) * Real.exp (a / 2 * pairNormSq p) := by
      have hexp := Real.add_one_le_exp (a / 2 * pairNormSq p)
      have hk : 0 ≤ 2 + 2 / a := by positivity
      have : (2 + 2 / a) * (a / 2 * pairNormSq p + 1) = 2 + 2 / a + (a + 1) * pairNormSq p := by
        field_simp
        ring
      have h5 := mul_le_mul_of_nonneg_left hexp hk
      have h6 := mul_nonneg ha0.le hN
      have h7 : 0 ≤ 2 / a := by positivity
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
      (pairHeat_nonneg ht p)), pairHeat_eq]
    have hc : 0 ≤ (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * (4 * Real.pi * t) ^ (-(d : ℝ) / 2) := by
      have : 0 < 4 * Real.pi * t := by positivity
      positivity
    have he : Real.exp (-(a) * pairNormSq p) =
        Real.exp (-(a / 2) * pairNormSq p) * Real.exp (a / 2 * pairNormSq p) ^ 0 *
          Real.exp (-(a / 2) * pairNormSq p) := by
      rw [pow_zero, mul_one, ← Real.exp_add]
      congr 1
      ring
    have h3 : (‖p.1‖ + ‖p.2‖) * Real.exp (-a * pairNormSq p) ≤
        (2 + 2 / a) * Real.exp (-(a / 2) * pairNormSq p) := by
      have : Real.exp (-a * pairNormSq p) = Real.exp (-(a / 2) * pairNormSq p) *
          Real.exp (-(a / 2) * pairNormSq p) := by
        rw [← Real.exp_add]; congr 1; ring
      have hpos : 0 < Real.exp (-(a / 2) * pairNormSq p) := Real.exp_pos _
      have hh : (2 + 2 / a) * Real.exp (-(a / 2) * pairNormSq p) =
          (2 + 2 / a) * Real.exp (a / 2 * pairNormSq p) * Real.exp (-(a) * pairNormSq p) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      rw [hh]
      exact mul_le_mul_of_nonneg_right (h1.trans h2) (Real.exp_pos _).le
    calc (‖p.1‖ + ‖p.2‖) * (_ * Real.exp (-a * pairNormSq p))
        = _ * ((‖p.1‖ + ‖p.2‖) * Real.exp (-a * pairNormSq p)) := by ring
      _ ≤ _ * ((2 + 2 / a) * Real.exp (-(a / 2) * pairNormSq p)) :=
          mul_le_mul_of_nonneg_left h3 hc
      _ = _ := by ring

theorem vecNormSq_add_smul {d : ℕ} (x a : Vec d) (τ : ℝ) :
    vecNormSq (x + τ • a) = vecNormSq x + 2 * τ * vecDot x a + τ ^ 2 * vecNormSq a := by
  simp only [vecNormSq, vecDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have : ∀ i, (x i + τ * a i) * (x i + τ * a i) =
      x i * x i + 2 * τ * (x i * a i) + τ ^ 2 * (a i * a i) := fun i => by ring
  simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The line derivative of the product heat kernel. -/
theorem hasDerivAt_pairHeat_line {d : ℕ} {t : ℝ} (ht : 0 < t) (p v : Vec d × Vec d) :
    HasDerivAt (fun τ : ℝ => pairHeat d t (p + τ • v))
      (-(1 / (2 * t)) * (vecDot p.1 v.1 + vecDot p.2 v.2) * pairHeat d t p) 0 := by
  set a : ℝ := 1 / (4 * t) with ha
  set B : ℝ := vecDot p.1 v.1 + vecDot p.2 v.2
  set c : ℝ := (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * (4 * Real.pi * t) ^ (-(d : ℝ) / 2)
  have hfun : (fun τ : ℝ => pairHeat d t (p + τ • v)) = fun τ =>
      c * Real.exp (-a * (pairNormSq p + 2 * τ * B + τ ^ 2 * pairNormSq v)) := by
    funext τ
    rw [pairHeat_eq]
    congr 2
    simp only [pairNormSq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      vecNormSq_add_smul, B]
    ring
  rw [hfun]
  have hin : HasDerivAt (fun τ : ℝ => -a * (pairNormSq p + 2 * τ * B + τ ^ 2 * pairNormSq v))
      (-a * (2 * B)) 0 := by
    have h1 : HasDerivAt (fun τ : ℝ => pairNormSq p + 2 * τ * B + τ ^ 2 * pairNormSq v)
        (2 * B) 0 := by
      have := ((((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const B).const_add (pairNormSq p)).add
        (((hasDerivAt_pow 2 (0 : ℝ)).mul_const (pairNormSq v)))
      convert this using 1
      · funext τ
        simp
      · simp
    exact h1.const_mul _
  have hph : pairHeat d t p = c * Real.exp (-a * pairNormSq p) := pairHeat_eq t p
  have := (hin.exp).const_mul c
  convert this using 1
  rw [hph]
  simp only [mul_zero, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow]
  rw [show (1 / (2 * t)) = 2 * a by rw [ha]; field_simp; ring]
  ring

end PDE.GaussianPoincare
