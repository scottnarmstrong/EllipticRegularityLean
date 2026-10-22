module

public import EllipticRegularity.Parabolic.WeakHarnack.MeasuresLogTailBombieri
public import EllipticRegularity.Parabolic.WeakHarnack.IterationLinfty
public import EllipticRegularity.Parabolic.WeakHarnack.IterationHrh
public import PDEFoundation.Analysis.Inequalities.Bombieri.Abstract

/-!
# Bombieri-Giusti on the positive and negative side for a fixed `v`

For a fixed measurable `v` (`= u + ε`) these lemmas run the manuscript step "apply the
Bombieri-Giusti lemma to `e^{-k} v`" (positive powers on `posCyl`), resp. to `e^k / v`
(negative powers on `negCyl`), followed by the `L^1 → L^∞` Moser iteration on `negCylInner`.
All constants depend only on `χ, q`, the step constants and `c₀` (the constant of `hlog`), never
on `v` or `k`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.WeakHarnack

variable {d : ℕ}

/-- Scaling a function by a nonnegative constant scales every `eLpNorm`. -/
theorem eLpNorm_const_mul_fun {X : Type*} [MeasurableSpace X] (f : X → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (p : ℝ≥0∞) (μ : Measure X) :
    eLpNorm (fun z => r * f z) p μ = ENNReal.ofReal r * eLpNorm f p μ := by
  have := eLpNorm_const_smul (𝕜 := ℝ) r f p μ
  rw [Real.enorm_eq_ofReal hr] at this
  exact this

/-- The `hrh`-type inequality is invariant under multiplication by a nonnegative constant. -/
theorem step_const_mul {X : Type*} [MeasurableSpace X] {f : X → ℝ} {r : ℝ} (hr : 0 ≤ r)
    {p₁ p₂ : ℝ≥0∞} {μ₁ μ₂ : Measure X} {B : ℝ≥0∞}
    (h : eLpNorm f p₁ μ₁ ≤ B * eLpNorm f p₂ μ₂) :
    eLpNorm (fun z => r * f z) p₁ μ₁ ≤ B * eLpNorm (fun z => r * f z) p₂ μ₂ := by
  rw [eLpNorm_const_mul_fun f hr, eLpNorm_const_mul_fun f hr]
  calc ENNReal.ofReal r * eLpNorm f p₁ μ₁ ≤ ENNReal.ofReal r * (B * eLpNorm f p₂ μ₂) := by gcongr
    _ = _ := by ring

/-- Change of normalization of a cylinder measure, restricted to a subset of both cylinders. -/
theorem cylMeasure_restrict_ratio {S S' T : Set (Vec d × ℝ)} (hT : MeasurableSet T) (hTS : T ⊆ S)
    (hTS' : T ⊆ S') (hS0 : volume S ≠ 0) (hSt : volume S ≠ ⊤) :
    (cylMeasure S').restrict T = ((volume S')⁻¹ * volume S) • (cylMeasure S).restrict T := by
  rw [cylMeasure_restrict hT hTS, cylMeasure_restrict hT hTS', smul_smul, mul_assoc,
    ENNReal.mul_inv_cancel hS0 hSt, mul_one]

/-- The ratio `vol(negCylInner 1)⁻¹ vol(negCyl 1)`. -/
noncomputable def negRatio (d : ℕ) : ℝ≥0∞ := (volume (negCylInner d 1))⁻¹ * volume (negCyl d 1)

theorem negRatio_ne_zero : negRatio d ≠ 0 :=
  mul_ne_zero (ENNReal.inv_ne_zero.2 (volume_negCylInner_ne_top (by norm_num)))
    (volume_negCyl_pos (by norm_num)).ne'

theorem negRatio_ne_top : negRatio d ≠ ⊤ :=
  ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (volume_negCylInner_pos (by norm_num)).ne')
    (volume_negCyl_ne_top (by norm_num))

/-! ### Positive side -/

theorem pos_side {χ A m q k c₀ : ℝ} (hχ : 1 < χ) (hA : 1 ≤ A) (hm : 0 < m) (hq : 0 < q)
    {v : Vec d × ℝ → ℝ} (hv : Measurable v) (hvpos : ∀ z, 0 < v z)
    (hfin : eLpNorm v (ENNReal.ofReal (q * χ)) ((cylMeasure (posCyl d 1)).restrict (posCyl d 1)) < ⊤)
    (hstep : ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p → p ≤ q →
      eLpNorm v (ENNReal.ofReal (χ * p)) ((cylMeasure (posCyl d 1)).restrict (posCyl d σ')) ≤
        ENNReal.ofReal ((A * (σ - σ') ^ (-m)) ^ (1 / p)) *
          eLpNorm v (ENNReal.ofReal p) ((cylMeasure (posCyl d 1)).restrict (posCyl d σ)))
    (hlog : ∀ lam : ℝ, 0 < lam →
      cylMeasure (posCyl d 1) (posCyl d 1 ∩ {z | lam < Real.log (Real.exp (-k) * v z)}) ≤
        ENNReal.ofReal (c₀ / lam)) :
    eLpNorm v (ENNReal.ofReal (q * χ)) ((cylMeasure (posCyl d 1)).restrict (posCyl d (1 / 2))) ≤
      ENNReal.ofReal (PDE.Bombieri.giustiConst (1 / 2) (q * χ)
        (max c₀ (PDE.ParabIter.posC χ A m q)) (PDE.ParabIter.posM χ m q) * Real.exp k) := by
  obtain ⟨hc1, hM, hrh⟩ := PDE.ParabIter.hrh_of_posStep (cylMeasure (posCyl d 1)) (posCyl d) v
    (δ := 1 / 2) (by norm_num) hχ hA hm hq posCyl_hUmono hstep
  have hχ0 : 0 < χ := by linarith
  have hc : 1 ≤ max c₀ (PDE.ParabIter.posC χ A m q) := hc1.trans (le_max_right _ _)
  have hrh' := hrh_mono_const (1 / 2) (q * χ) (PDE.ParabIter.posM χ m q) (by positivity)
    (cylMeasure (posCyl d 1)) (posCyl d) v (by linarith) (le_max_right c₀ _) hrh
  have hek : 0 ≤ Real.exp (-k) := (Real.exp_pos _).le
  set f : Vec d × ℝ → ℝ := fun z => Real.exp (-k) * v z with hf
  have hrhf := fun σ' σ h1 h2 h3 α hα hαle =>
    step_const_mul (r := Real.exp (-k)) hek (hrh' σ' σ h1 h2 h3 α hα hαle)
  have hfpos : ∀ z, 0 < f z := fun z => mul_pos (Real.exp_pos _) (hvpos z)
  have hfinf : eLpNorm f (ENNReal.ofReal (q * χ))
      ((cylMeasure (posCyl d 1)).restrict (posCyl d 1)) < ⊤ := by
    rw [hf, eLpNorm_const_mul_fun v hek]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  have hlogf : ∀ lam : ℝ, 0 < lam →
      cylMeasure (posCyl d 1) (posCyl d 1 ∩ {x | lam < Real.log (f x)}) ≤
        ENNReal.ofReal (max c₀ (PDE.ParabIter.posC χ A m q) / lam) := fun lam hlam =>
    (hlog lam hlam).trans (ENNReal.ofReal_le_ofReal (by gcongr; exact le_max_left _ _))
  have hB := PDE.Bombieri.bombieri_giusti (1 / 2) (q * χ) (max c₀ (PDE.ParabIter.posC χ A m q))
    (PDE.ParabIter.posM χ m q) (by norm_num) (by norm_num) (by positivity) hc hM
    (cylMeasure (posCyl d 1)) (posCyl d) posCyl_hUm posCyl_hUmono f
    ((measurable_const.mul hv)) hfpos hfinf hlogf hrhf
  have hv_eq : v = fun z => Real.exp k * f z := by
    funext z
    simp only [hf]
    rw [← mul_assoc, ← Real.exp_add]
    simp
  rw [hv_eq, eLpNorm_const_mul_fun f (Real.exp_pos k).le]
  calc ENNReal.ofReal (Real.exp k) * eLpNorm f (ENNReal.ofReal (q * χ))
        ((cylMeasure (posCyl d 1)).restrict (posCyl d (1 / 2)))
      ≤ ENNReal.ofReal (Real.exp k) * ENNReal.ofReal (PDE.Bombieri.giustiConst (1 / 2) (q * χ)
        (max c₀ (PDE.ParabIter.posC χ A m q)) (PDE.ParabIter.posM χ m q)) := by gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos k).le, mul_comm]

end PDE.Parabolic.WeakHarnack
