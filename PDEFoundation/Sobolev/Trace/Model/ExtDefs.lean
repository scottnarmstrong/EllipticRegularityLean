module

public import PDEFoundation.Sobolev.Trace.Model.ExtProfile
public import PDEFoundation.Sobolev.Trace.Model.ExtCutoff
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The model extension operator

`dil k ψ z t = t⁻ᵏ ψ(z / t)`; the operator is `E g (x', t) = χ(t) ∫ t⁻ⁿ ρ((x' - y') / t) g(y') dy'`
for `t > 0` (and `0` for `t ≤ 0`).  We record the elementary properties of dilates of a
compactly supported profile and the linearity of `E`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- The dilate `t⁻ᵏ ψ(z / t)` of a profile. -/
noncomputable def dil {n : ℕ} (k : ℕ) (ψ : Vec n → ℝ) (z : Vec n) (t : ℝ) : ℝ :=
  (t⁻¹) ^ k * ψ (t⁻¹ • z)

/-- Convolution of the dilate of `ψ` with `g` at `(x', t)`. -/
noncomputable def dilConv {n : ℕ} (k : ℕ) (ψ : Vec n → ℝ) (g : Vec n → ℝ) (z : Vec n × ℝ) : ℝ :=
  ∫ y, dil k ψ (z.1 - y) z.2 * g y

/-- `E g (x', t) = χ(t) ∫ t^{-n} ρ((x'-y')/t) g(y') dy'` for `t > 0` (`0` for `t ≤ 0`). -/
noncomputable def modelExt (n : ℕ) (g : Vec n → ℝ) (z : Vec n × ℝ) : ℝ :=
  if 0 < z.2 then extCutoff z.2 * dilConv n (extKernel n) g z else 0

/-- A continuous profile supported in the closed Euclidean unit ball. -/
structure IsProfile {n : ℕ} (ψ : Vec n → ℝ) : Prop where
  cont : Continuous ψ
  zero : ∀ w, 1 < vecEuclideanNorm w → ψ w = 0

theorem isProfile_extKernel (n : ℕ) : IsProfile (extKernel n) :=
  ⟨continuous_extKernel n, fun _ hw => extKernel_eq_zero_of_one_lt n hw⟩

theorem isProfile_extTan (n : ℕ) (i : Fin n) : IsProfile (extTan n i) :=
  ⟨continuous_extTan n i, fun _ hw => extTan_eq_zero_of_one_lt n i hw⟩

theorem isProfile_extRad (n : ℕ) : IsProfile (extRad n) :=
  ⟨continuous_extRad n, fun _ hw => extRad_eq_zero_of_one_lt n hw⟩

section Dil

variable {n : ℕ} {ψ : Vec n → ℝ}

theorem continuous_dil (k : ℕ) (hψ : IsProfile ψ) (t : ℝ) : Continuous fun z => dil k ψ z t :=
  continuous_const.mul (hψ.cont.comp (continuous_const_smul _))

theorem dil_eq_zero (k : ℕ) (hψ : IsProfile ψ) {z : Vec n} {t : ℝ} (ht : 0 < t)
    (hz : t < vecEuclideanNorm z) : dil k ψ z t = 0 := by
  unfold dil
  rw [hψ.zero, mul_zero]
  rw [vecEuclideanNorm_smul, abs_of_pos (inv_pos.2 ht), ← div_eq_inv_mul, one_lt_div ht]
  exact hz

theorem abs_dil_le (k : ℕ) {M : ℝ} (hM : ∀ w, |ψ w| ≤ M) {t : ℝ} (ht : 0 < t) (z : Vec n) :
    |dil k ψ z t| ≤ (t⁻¹) ^ k * M := by
  unfold dil
  rw [abs_mul, abs_pow, abs_of_pos (inv_pos.2 ht)]
  exact mul_le_mul_of_nonneg_left (hM _) (by positivity)

theorem hasCompactSupport_dil_sub (k : ℕ) (hψ : IsProfile ψ) {t : ℝ} (ht : 0 < t) (x : Vec n) :
    HasCompactSupport fun y => dil k ψ (x - y) t := by
  refine HasCompactSupport.intro (isCompact_closedBall x t) ?_
  intro y hy
  refine dil_eq_zero k hψ ht ?_
  have h1 : t < ‖y - x‖ := by simpa [dist_eq_norm] using hy
  rw [← norm_neg, neg_sub] at h1
  exact lt_of_lt_of_le h1 (norm_le_vecEuclideanNorm _)

theorem continuous_dil_sub (k : ℕ) (hψ : IsProfile ψ) (t : ℝ) (x : Vec n) :
    Continuous fun y => dil k ψ (x - y) t :=
  (continuous_dil k hψ t).comp (continuous_const.sub continuous_id)

theorem integrable_dil_mul (k : ℕ) (hψ : IsProfile ψ) {t : ℝ} (ht : 0 < t) {g : Vec n → ℝ}
    (hg : LocallyIntegrable g volume) (x : Vec n) :
    Integrable (fun y => dil k ψ (x - y) t * g y) volume := by
  simpa only [smul_eq_mul] using hg.integrable_smul_left_of_hasCompactSupport (𝕜 := ℝ)
    (continuous_dil_sub k hψ t x) (hasCompactSupport_dil_sub k hψ ht x)

theorem integrable_dil (k : ℕ) (hψ : IsProfile ψ) {t : ℝ} (ht : 0 < t) (x : Vec n) :
    Integrable (fun y => dil k ψ (x - y) t) volume := by
  simpa using (integrable_dil_mul k hψ ht (g := fun _ => (1 : ℝ))
    (continuous_const.locallyIntegrable) x)

theorem integral_dil (k : ℕ) {t : ℝ} (ht : 0 < t) (ψ : Vec n → ℝ) :
    ∫ z, dil k ψ z t = (t⁻¹) ^ k * (t ^ n * ∫ z, ψ z) := by
  unfold dil
  rw [integral_const_mul, Measure.integral_comp_smul (μ := volume) ψ t⁻¹, Module.finrank_fin_fun]
  congr 1
  rw [inv_pow, inv_inv, abs_of_pos (by positivity), smul_eq_mul]

theorem integral_dil_sub (k : ℕ) {t : ℝ} (ht : 0 < t) (ψ : Vec n → ℝ) (x : Vec n) :
    ∫ y, dil k ψ (x - y) t = (t⁻¹) ^ k * (t ^ n * ∫ z, ψ z) := by
  rw [integral_sub_left_eq_self (fun z => dil k ψ z t) volume x, integral_dil k ht]

/-- Cancellation: if `∫ ψ = 0` the convolution only sees `g - g x`. -/
theorem dilConv_eq_sub (k : ℕ) (hψ : IsProfile ψ) (h0 : ∫ z, ψ z = 0) {g : Vec n → ℝ}
    (hg : LocallyIntegrable g volume) {t : ℝ} (ht : 0 < t) (x : Vec n) :
    dilConv k ψ g (x, t) = ∫ y, dil k ψ (x - y) t * (g y - g x) := by
  have h1 := integrable_dil_mul k hψ ht hg x
  have h2 : Integrable (fun y => dil k ψ (x - y) t * g x) volume :=
    (integrable_dil k hψ ht x).mul_const _
  simp_rw [mul_sub]
  rw [integral_sub h1 h2, integral_mul_const, integral_dil_sub k ht, h0]
  simp [dilConv]

end Dil

theorem modelExt_eq_zero {n : ℕ} (g : Vec n → ℝ) (z : Vec n × ℝ) (hz : 1 ≤ z.2) :
    modelExt n g z = 0 := by
  unfold modelExt
  split_ifs with h
  · rw [extCutoff_eq_zero hz, zero_mul]
  · rfl

theorem modelExt_smul {n : ℕ} (c : ℝ) (g : Vec n → ℝ) : modelExt n (c • g) = c • modelExt n g := by
  funext z
  simp only [Pi.smul_apply, smul_eq_mul, modelExt, dilConv]
  split_ifs with h
  · simp_rw [mul_left_comm _ c, integral_const_mul]
    ring
  · simp

theorem modelExt_add {n : ℕ} {p : ℝ} (hp : 1 < p) (g h : Vec n → ℝ)
    (hg : MemLp g (ENNReal.ofReal p) volume) (hh : MemLp h (ENNReal.ofReal p) volume) :
    modelExt n (g + h) = modelExt n g + modelExt n h := by
  have hq : 1 ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp.le
  funext z
  simp only [Pi.add_apply, modelExt, dilConv]
  split_ifs with ht
  · simp_rw [mul_add]
    rw [integral_add (integrable_dil_mul n (isProfile_extKernel n) ht (hg.locallyIntegrable hq) z.1)
      (integrable_dil_mul n (isProfile_extKernel n) ht (hh.locallyIntegrable hq) z.1)]
    ring
  · simp

end PDE.TraceLane
