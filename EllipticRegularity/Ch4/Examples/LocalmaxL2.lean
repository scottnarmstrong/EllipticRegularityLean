module

public import EllipticRegularity.Ch4.Examples.LocalmaxCalc
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Algebra.Order.Chebyshev

/-!
# The `L²` bound in Proposition 4.12

The one-dimensional building blocks: `∫_ℝ e^{-β|t|} dt = 2/β`, and the product integral.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE.Ch4Examples

open MeasureTheory Filter Set

theorem integrable_exp_neg_abs : Integrable (fun t : ℝ => Real.exp (-|t|)) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_exp_Iic (0 : ℝ)).congr_fun (fun t ht => ?_) measurableSet_Iic
    simp [abs_of_nonpos (show t ≤ 0 from ht)]
  · refine (integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0).congr_fun (fun t ht => ?_)
      measurableSet_Ioi
    simp [abs_of_pos (show 0 < t from ht)]

theorem integral_exp_neg_abs : ∫ t : ℝ, Real.exp (-|t|) = 2 := by
  rw [integral_comp_abs (f := fun x => Real.exp (-x)), integral_exp_neg_Ioi_zero]
  norm_num

theorem integrable_exp_neg_mul_abs {β : ℝ} (hβ : 0 < β) :
    Integrable (fun t : ℝ => Real.exp (-(β * |t|))) := by
  have := integrable_exp_neg_abs.comp_mul_left' (R := β) hβ.ne'
  refine this.congr (Eventually.of_forall fun t => ?_)
  simp [abs_mul, abs_of_pos hβ]

theorem integral_exp_neg_mul_abs {β : ℝ} (hβ : 0 < β) :
    ∫ t : ℝ, Real.exp (-(β * |t|)) = 2 / β := by
  have h := Measure.integral_comp_mul_left (fun t : ℝ => Real.exp (-|t|)) β
  simp only [abs_mul, abs_of_pos hβ, smul_eq_mul, integral_exp_neg_abs] at h
  rw [h, abs_inv, abs_of_pos hβ]
  field_simp

/-- One-dimensional factor: `e^{-β|t|}` for tangential coordinates, the indicator of `(-1,1)` for
the last one. -/
noncomputable def gLM (β : ℝ) (d : ℕ) (i : Fin d) (t : ℝ) : ℝ :=
  if i.val + 1 < d then Real.exp (-(β * |t|)) else (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) t

theorem integrable_gLM {β : ℝ} (hβ : 0 < β) {d : ℕ} (i : Fin d) : Integrable (gLM β d i) := by
  unfold gLM
  split_ifs
  · exact integrable_exp_neg_mul_abs hβ
  · exact (integrable_indicator_iff measurableSet_Ioo).2
      (integrableOn_const (by simp))

theorem integral_gLM {β : ℝ} (hβ : 0 < β) {d : ℕ} (i : Fin d) :
    ∫ t, gLM β d i t = if i.val + 1 < d then 2 / β else 2 := by
  unfold gLM
  split_ifs
  · exact integral_exp_neg_mul_abs hβ
  · rw [integral_indicator measurableSet_Ioo]
    simp
    norm_num

theorem integral_prod_gLM {β : ℝ} (hβ : 0 < β) {d : ℕ} (hd : 1 ≤ d) :
    ∫ x : Vec d, ∏ i, gLM β d i (x i) = 2 * (2 / β) ^ (d - 1) := by
  rw [integral_fintype_prod_volume_eq_prod]
  simp_rw [integral_gLM hβ]
  set l : Fin d := ⟨d - 1, by omega⟩ with hl
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l)]
  have h1 : (if l.val + 1 < d then 2 / β else 2) = 2 := by
    simp [hl]; omega
  have h2 : ∏ i ∈ Finset.univ.erase l, (if i.val + 1 < d then 2 / β else 2) = (2 / β) ^ (d - 1) := by
    rw [Finset.prod_congr rfl (g := fun _ => 2 / β)]
    · rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ,
        Fintype.card_fin]
    · intro i hi
      have hne : i ≠ l := (Finset.mem_erase.1 hi).1
      have : i.val ≠ d - 1 := fun h => hne (Fin.ext (by simp [hl, h]))
      have := i.isLt
      have h3 : i.val + 1 < d := by omega
      simp [h3]
  rw [h1, h2]

/-- Pointwise domination of `u²` on the unit ball by a product of one-dimensional factors. -/
theorem sq_le_prod_gLM (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (x : Vec d)
    (hx : x ∈ euclideanBall (0 : Vec d) 1) :
    Real.exp (x ⟨d - 1, by omega⟩ ^ 2 / 2 -
        Real.sqrt (1 + Λ * ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val + 1 < d),
          x i ^ 2) / ((d : ℝ) - 1)) ^ 2 ≤
      Real.exp 1 * ∏ i, gLM (2 * Real.sqrt Λ / ((d : ℝ) - 1) ^ 2) d i (x i) := by
  set l : Fin d := ⟨d - 1, by omega⟩ with hl
  set m : ℝ := (d : ℝ) - 1 with hm
  have hm1 : 1 ≤ m := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    rw [hm]; linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  set T := Finset.univ.filter (fun i : Fin d => i.val + 1 < d) with hT
  set q := ∑ i ∈ T, x i ^ 2 with hq
  set S := ∑ i ∈ T, |x i| with hS
  set β : ℝ := 2 * Real.sqrt Λ / m ^ 2 with hβ
  have hΛs : 0 ≤ Real.sqrt Λ := Real.sqrt_nonneg _
  have hq0 : 0 ≤ q := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => abs_nonneg _
  -- the product equals `exp (-β S)`
  have hlt : ∀ i : Fin d, |x i| < 1 := fun i => abs_apply_lt_of_mem_ball zero_le_one hx i
  have hprod : ∏ i, gLM β d i (x i) = Real.exp (-(β * S)) := by
    have h1 : ∀ i : Fin d, gLM β d i (x i) =
        Real.exp (if i.val + 1 < d then -(β * |x i|) else 0) := by
      intro i
      unfold gLM
      split_ifs with h
      · rfl
      · rw [indicator_of_mem (by simpa [abs_lt] using hlt i)]
        simp
    simp_rw [h1]
    rw [← Real.exp_sum]
    congr 1
    rw [← Finset.sum_filter, Finset.sum_neg_distrib, ← Finset.mul_sum]
  -- Cauchy--Schwarz: `S ≤ m √q`
  have hcard : (T.card : ℝ) ≤ m := by
    have hsub : T ⊆ Finset.univ.erase l := by
      intro i hi
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩
      intro h
      subst h
      simp [hl] at hi
      omega
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ, Fintype.card_fin] at this
    have h2 : ((d - 1 : ℕ) : ℝ) = m := by rw [hm, Nat.cast_sub (by omega)]; simp
    calc (T.card : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by exact_mod_cast this
      _ = m := h2
  have hCS : S ^ 2 ≤ m * q := by
    have := sq_sum_le_card_mul_sum_sq (s := T) (f := fun i => |x i|)
    simp only [sq_abs] at this
    calc S ^ 2 ≤ T.card * q := this
      _ ≤ m * q := mul_le_mul_of_nonneg_right hcard hq0
  have hSm : S ≤ m * Real.sqrt q := by
    have : S ≤ Real.sqrt (m ^ 2 * q) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith
    rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)] at this
  have hs : Real.sqrt Λ * Real.sqrt q ≤ Real.sqrt (1 + Λ * q) := by
    rw [← Real.sqrt_mul hΛ0]
    exact Real.sqrt_le_sqrt (by linarith)
  have hβS : β * S ≤ 2 * Real.sqrt (1 + Λ * q) / m := by
    rw [hβ]
    have hmpos : 0 < m := by linarith
    calc 2 * Real.sqrt Λ / m ^ 2 * S ≤ 2 * Real.sqrt Λ / m ^ 2 * (m * Real.sqrt q) :=
          mul_le_mul_of_nonneg_left hSm (by positivity)
      _ = 2 * (Real.sqrt Λ * Real.sqrt q) / m := by field_simp
      _ ≤ 2 * Real.sqrt (1 + Λ * q) / m := by gcongr
  have hl2 : x l ^ 2 ≤ 1 := by
    have := abs_lt.1 (hlt l)
    nlinarith
  rw [hprod, sq, ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  rw [mul_div_assoc] at hβS
  linarith

theorem gLM_nonneg (β : ℝ) (d : ℕ) (i : Fin d) (t : ℝ) : 0 ≤ gLM β d i t := by
  unfold gLM
  split_ifs
  · exact (Real.exp_pos _).le
  · exact indicator_nonneg (fun _ _ => zero_le_one) _

theorem localmax_lintegral_bound (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (u : Vec d → ℝ)
    (hu : ∀ x, u x = Real.exp (x ⟨d - 1, by omega⟩ ^ 2 / 2 -
        Real.sqrt (1 + Λ * ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val + 1 < d),
          x i ^ 2) / ((d : ℝ) - 1))) :
    ∫⁻ x in euclideanBall (0 : Vec d) 1, ENNReal.ofReal (u x ^ 2) ≤
      ENNReal.ofReal (Real.exp 1 *
        (2 * (2 / (2 * Real.sqrt Λ / ((d : ℝ) - 1) ^ 2)) ^ (d - 1))) := by
  set β : ℝ := 2 * Real.sqrt Λ / ((d : ℝ) - 1) ^ 2 with hβ
  have hm1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsq : 1 ≤ Real.sqrt Λ := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hΛ
  have hβpos : 0 < β := by rw [hβ]; positivity
  have hB : MeasurableSet (euclideanBall (0 : Vec d) 1) := (isOpen_euclideanBall _ _).measurableSet
  have hint0 : Integrable (fun x : Vec d => ∏ i, gLM β d i (x i)) (Measure.pi fun _ => volume) :=
    Integrable.fintype_prod (fun i => integrable_gLM hβpos i)
  have hint : Integrable (fun x : Vec d => Real.exp 1 * ∏ i, gLM β d i (x i)) := by
    have := hint0.const_mul (Real.exp 1)
    rwa [← volume_pi] at this
  have hnn : 0 ≤ᵐ[volume] fun x : Vec d => Real.exp 1 * ∏ i, gLM β d i (x i) :=
    Eventually.of_forall fun x => mul_nonneg (Real.exp_pos _).le
      (Finset.prod_nonneg fun i _ => gLM_nonneg β d i (x i))
  have h1 : ∫⁻ x in euclideanBall (0 : Vec d) 1, ENNReal.ofReal (u x ^ 2) ≤
          ∫⁻ x in euclideanBall (0 : Vec d) 1,
          ENNReal.ofReal (Real.exp 1 * ∏ i, gLM β d i (x i)) := by
    refine setLIntegral_mono' hB fun x hx => ENNReal.ofReal_le_ofReal ?_
    rw [hu]
    exact sq_le_prod_gLM d hd Λ hΛ x hx
  have h2 : ∫⁻ x in euclideanBall (0 : Vec d) 1,
          ENNReal.ofReal (Real.exp 1 * ∏ i, gLM β d i (x i)) ≤
      ∫⁻ x : Vec d, ENNReal.ofReal (Real.exp 1 * ∏ i, gLM β d i (x i)) :=
    setLIntegral_le_lintegral _ _
  have h3 := (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
  have h4 : ∫ x : Vec d, Real.exp 1 * ∏ i, gLM β d i (x i) =
      Real.exp 1 * (2 * (2 / β) ^ (d - 1)) := by
    rw [integral_const_mul, integral_prod_gLM hβpos (by omega)]
  rw [h4] at h3
  exact h1.trans (h2.trans h3.le)

/-- The `L²(B₁)` norm of the example is at most `√(e · 2 (2/β)^{d-1})`. -/
theorem localmax_eLpNorm_bound (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (u : Vec d → ℝ)
    (hcont : Continuous u)
    (hu : ∀ x, u x = Real.exp (x ⟨d - 1, by omega⟩ ^ 2 / 2 -
        Real.sqrt (1 + Λ * ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val + 1 < d),
          x i ^ 2) / ((d : ℝ) - 1))) :
    eLpNorm u 2 (volumeOn (euclideanBall (0 : Vec d) 1)) ≤
      ENNReal.ofReal (Real.sqrt (Real.exp 1 *
        (2 * (2 / (2 * Real.sqrt Λ / ((d : ℝ) - 1) ^ 2)) ^ (d - 1)))) := by
  have hb := localmax_lintegral_bound d hd Λ hΛ u hu
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hcont.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  have h1 : ∀ x, ‖u x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (u x ^ 2) := by
    intro x
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
      Real.rpow_two, sq_abs]
  simp_rw [h1]
  rw [volumeOn]
  have hnn : 0 ≤ Real.exp 1 *
      (2 * (2 / (2 * Real.sqrt Λ / ((d : ℝ) - 1) ^ 2)) ^ (d - 1)) := by
    have hm1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have hsq : 1 ≤ Real.sqrt Λ := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hΛ
    positivity
  calc (∫⁻ x in euclideanBall (0 : Vec d) 1, ENNReal.ofReal (u x ^ 2)) ^ (1 / (2 : ℝ))
      ≤ (ENNReal.ofReal (Real.exp 1 *
        (2 * (2 / (2 * Real.sqrt Λ / ((d : ℝ) - 1) ^ 2)) ^ (d - 1)))) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow hb (by norm_num)
    _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg hnn (by norm_num)]
        congr 1
        exact (Real.sqrt_eq_rpow _).symm

end PDE.Ch4Examples
