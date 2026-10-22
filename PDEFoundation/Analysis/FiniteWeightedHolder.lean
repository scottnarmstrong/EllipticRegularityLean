module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.MeanInequalities

@[expose] public section

open scoped BigOperators

namespace PDE

variable {ι : Type*}

/-- Weighted Hölder inequality for finite sums of nonnegative real functions. -/
theorem weighted_holder_of_nonneg
    (s : Finset ι) (w f g : ι → ℝ) {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hf : ∀ i ∈ s, 0 ≤ f i)
    (hg : ∀ i ∈ s, 0 ≤ g i) :
    ∑ i ∈ s, w i * f i * g i ≤
      (∑ i ∈ s, w i * (f i) ^ p) ^ (1 / p) *
        (∑ i ∈ s, w i * (g i) ^ q) ^ (1 / q) := by
  let F : ι → ℝ := fun i => (w i) ^ p⁻¹ * f i
  let G : ι → ℝ := fun i => (w i) ^ q⁻¹ * g i
  have hF : ∀ i ∈ s, 0 ≤ F i := by
    intro i hi
    exact mul_nonneg (Real.rpow_nonneg (hw i hi) _) (hf i hi)
  have hG : ∀ i ∈ s, 0 ≤ G i := by
    intro i hi
    exact mul_nonneg (Real.rpow_nonneg (hw i hi) _) (hg i hi)
  have hweight (i : ι) (hi : i ∈ s) :
      (w i) ^ p⁻¹ * (w i) ^ q⁻¹ = w i := by
    calc
      (w i) ^ p⁻¹ * (w i) ^ q⁻¹ = (w i) ^ (p⁻¹ + q⁻¹) :=
        (Real.rpow_add_of_nonneg (hw i hi) hpq.inv_nonneg hpq.symm.inv_nonneg).symm
      _ = w i := by
        rw [hpq.inv_add_inv_eq_one, Real.rpow_one]
  have hFp (i : ι) (hi : i ∈ s) : (F i) ^ p = w i * (f i) ^ p := by
    dsimp only [F]
    rw [Real.mul_rpow (Real.rpow_nonneg (hw i hi) _) (hf i hi),
      ← Real.rpow_mul (hw i hi)]
    rw [inv_mul_cancel₀ hpq.ne_zero, Real.rpow_one]
  have hGq (i : ι) (hi : i ∈ s) : (G i) ^ q = w i * (g i) ^ q := by
    dsimp only [G]
    rw [Real.mul_rpow (Real.rpow_nonneg (hw i hi) _) (hg i hi),
      ← Real.rpow_mul (hw i hi)]
    rw [inv_mul_cancel₀ hpq.symm.ne_zero, Real.rpow_one]
  have hholder := Real.inner_le_Lp_mul_Lq_of_nonneg s hpq hF hG
  have hsumF : ∑ i ∈ s, (F i) ^ p = ∑ i ∈ s, w i * (f i) ^ p := by
    apply Finset.sum_congr rfl
    exact hFp
  have hsumG : ∑ i ∈ s, (G i) ^ q = ∑ i ∈ s, w i * (g i) ^ q := by
    apply Finset.sum_congr rfl
    exact hGq
  calc
    ∑ i ∈ s, w i * f i * g i = ∑ i ∈ s, F i * G i := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only [F, G]
      calc
        w i * f i * g i =
            ((w i) ^ p⁻¹ * (w i) ^ q⁻¹) * f i * g i := by
          exact congrArg (fun x : ℝ => x * f i * g i) (hweight i hi).symm
        _ = ((w i) ^ p⁻¹ * f i) * ((w i) ^ q⁻¹ * g i) := by ring
    _ ≤ (∑ i ∈ s, (F i) ^ p) ^ (1 / p) *
        (∑ i ∈ s, (G i) ^ q) ^ (1 / q) := hholder
    _ = (∑ i ∈ s, w i * (f i) ^ p) ^ (1 / p) *
        (∑ i ∈ s, w i * (g i) ^ q) ^ (1 / q) := by
      rw [hsumF, hsumG]

/-- Weighted Hölder inequality for finite complex sums. -/
theorem norm_weighted_sum_mul_le
    (s : Finset ι) (w : ι → ℝ) (f g : ι → ℂ) {p q : ℝ}
    (hpq : p.HolderConjugate q) (hw : ∀ i ∈ s, 0 ≤ w i) :
    ‖∑ i ∈ s, (w i : ℂ) * f i * g i‖ ≤
      (∑ i ∈ s, w i * ‖f i‖ ^ p) ^ (1 / p) *
        (∑ i ∈ s, w i * ‖g i‖ ^ q) ^ (1 / q) := by
  calc
    ‖∑ i ∈ s, (w i : ℂ) * f i * g i‖ ≤
        ∑ i ∈ s, ‖(w i : ℂ) * f i * g i‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, w i * ‖f i‖ * ‖g i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
    _ ≤ (∑ i ∈ s, w i * ‖f i‖ ^ p) ^ (1 / p) *
        (∑ i ∈ s, w i * ‖g i‖ ^ q) ^ (1 / q) :=
      weighted_holder_of_nonneg s w (fun i => ‖f i‖) (fun i => ‖g i‖)
        hpq hw (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)

end PDE
