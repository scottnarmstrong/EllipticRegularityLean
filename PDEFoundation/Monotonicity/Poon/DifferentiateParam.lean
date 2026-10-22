module

public import PDEFoundation.Monotonicity.Poon.Gaussian
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiation under the integral against the heat kernel

Abstract parametric statement: if `P r x` is differentiable in `r ∈ (a, b)` with derivative `P' r x`,
and `P`, `P'` are bounded by `C exp (2 A' |x|²)` on `[a, b]` where `A'` admits the Gaussian
domination of the heat kernel, then `r ↦ ∫ P r x Φ(r, x) dx` is differentiable at every `s ∈ (a, b)`
with derivative `∫ (P' s x + P s x κ(s, x)) Φ(s, x) dx`, `κ = -d/(2s) + |x|²/(4s²)`.
-/

@[expose] public section

open Set Filter MeasureTheory Metric

namespace PDE

noncomputable section

variable {d : ℕ}

theorem continuous_heatKernel_space {s : ℝ} : Continuous (heatKernel d s) :=
  continuous_iff_continuousAt.2 fun x => (hasFDerivAt_heatKernel s x).continuousAt

theorem abs_heatKernel_kappa_le {a r : ℝ} (ha : 0 < a) (hr : a ≤ r) (x : Vec d) :
    |(-(d : ℝ) / (2 * r) + vecNormSq x / (4 * r ^ 2))| ≤
      (1 + (d : ℝ) / (2 * a) + 1 / (4 * a ^ 2)) * (1 + vecNormSq x) - 1 := by
  have hr0 : 0 < r := ha.trans_le hr
  have hq : 0 ≤ vecNormSq x := by
    rw [vecNormSq_eq_sum_sq]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have h1 : (d : ℝ) / (2 * r) ≤ (d : ℝ) / (2 * a) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg d) (by positivity) (by linarith)
  have h2 : vecNormSq x / (4 * r ^ 2) ≤ vecNormSq x / (4 * a ^ 2) :=
    div_le_div_of_nonneg_left hq (by positivity) (by nlinarith)
  have h3 : 0 ≤ (d : ℝ) / (2 * r) := by positivity
  have h4 : 0 ≤ vecNormSq x / (4 * r ^ 2) := by positivity
  have h5 : vecNormSq x / (4 * a ^ 2) = 1 / (4 * a ^ 2) * vecNormSq x := by ring
  have h6 : 0 ≤ 1 / (4 * a ^ 2) * vecNormSq x := by positivity
  have h7 : 0 ≤ (d : ℝ) / (2 * a) * vecNormSq x := by positivity
  have h8 : 0 ≤ (d : ℝ) / (2 * a) := by positivity
  have h9 : 0 ≤ 1 / (4 * a ^ 2) := by positivity
  have h10 : (1 + (d : ℝ) / (2 * a) + 1 / (4 * a ^ 2)) * (1 + vecNormSq x) - 1 =
      (d : ℝ) / (2 * a) + 1 / (4 * a ^ 2) + vecNormSq x + (d : ℝ) / (2 * a) * vecNormSq x +
        1 / (4 * a ^ 2) * vecNormSq x := by ring
  have h11 : -(d : ℝ) / (2 * r) = -((d : ℝ) / (2 * r)) := neg_div _ _
  rw [abs_le, h10, h11]
  constructor <;> linarith

/-- Differentiation under the integral sign with Gaussian domination. -/
theorem hasDerivAt_integral_heatKernel_param {P P' : ℝ → Vec d → ℝ} {a b s A' : ℝ}
    (ha : 0 < a) (hs : s ∈ Ioo a b)
    (hG : ∃ c M : ℝ, 0 < c ∧ 0 ≤ M ∧ ∀ r ∈ Icc a b, ∀ x : Vec d,
      (1 + vecNormSq x) * (Real.exp (2 * A' * vecNormSq x) * heatKernel d r x) ≤
        M * Real.exp (-c * vecNormSq x))
    (hPc : ∀ r ∈ Ioo a b, Continuous (P r)) (hP'c : Continuous (P' s))
    (hder : ∀ r ∈ Ioo a b, ∀ x, HasDerivAt (fun r => P r x) (P' r x) r)
    (hB : ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc a b, ∀ x : Vec d,
      |P r x| ≤ C * Real.exp (2 * A' * vecNormSq x) ∧
      |P' r x| ≤ C * Real.exp (2 * A' * vecNormSq x)) :
    Integrable (fun x => P s x * heatKernel d s x) ∧
    Integrable (fun x => (P' s x + P s x * (-(d : ℝ) / (2 * s) + vecNormSq x / (4 * s ^ 2))) *
      heatKernel d s x) ∧
    HasDerivAt (fun r => ∫ x, P r x * heatKernel d r x)
      (∫ x, (P' s x + P s x * (-(d : ℝ) / (2 * s) + vecNormSq x / (4 * s ^ 2))) *
        heatKernel d s x) s := by
  obtain ⟨c, M, hc, hM, hGM⟩ := hG
  obtain ⟨C, hC, hPB⟩ := hB
  have hs0 : 0 < s := ha.trans hs.1
  have hsI : s ∈ Icc a b := ⟨hs.1.le, hs.2.le⟩
  set K : ℝ := 1 + (d : ℝ) / (2 * a) + 1 / (4 * a ^ 2) with hK
  have hK0 : 0 ≤ K := by positivity
  have hq : ∀ x : Vec d, 0 ≤ vecNormSq x := fun x => by
    rw [vecNormSq_eq_sum_sq]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hΦ0 : ∀ r ∈ Icc a b, ∀ x : Vec d, 0 < heatKernel d r x :=
    fun r hr x => heatKernel_pos d (ha.trans_le hr.1) x
  have hmeas : ∀ r ∈ Ioo a b, AEStronglyMeasurable (fun x => P r x * heatKernel d r x) volume :=
    fun r hr => ((hPc r hr).mul continuous_heatKernel_space).aestronglyMeasurable
  -- bound for the derivative integrand
  have hbound : ∀ r ∈ Icc a b, ∀ x : Vec d,
      ‖(P' r x + P r x * (-(d : ℝ) / (2 * r) + vecNormSq x / (4 * r ^ 2))) * heatKernel d r x‖ ≤
        C * K * (M * Real.exp (-c * vecNormSq x)) := by
    intro r hr x
    have hk := abs_heatKernel_kappa_le (d := d) ha hr.1 x
    obtain ⟨h1, h2⟩ := hPB r hr x
    have hΦ := hΦ0 r hr x
    have hE := hGM r hr x
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hΦ]
    have e1 : |P' r x + P r x * (-(d : ℝ) / (2 * r) + vecNormSq x / (4 * r ^ 2))| ≤
        C * Real.exp (2 * A' * vecNormSq x) * (K * (1 + vecNormSq x)) := by
      calc _ ≤ |P' r x| + |P r x| * |(-(d : ℝ) / (2 * r) + vecNormSq x / (4 * r ^ 2))| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul]
        _ ≤ C * Real.exp (2 * A' * vecNormSq x) +
            C * Real.exp (2 * A' * vecNormSq x) * (K * (1 + vecNormSq x) - 1) := by
            gcongr
        _ = _ := by ring
    calc _ ≤ C * Real.exp (2 * A' * vecNormSq x) * (K * (1 + vecNormSq x)) * heatKernel d r x :=
          mul_le_mul_of_nonneg_right e1 hΦ.le
      _ = C * K * ((1 + vecNormSq x) * (Real.exp (2 * A' * vecNormSq x) * heatKernel d r x)) := by
          ring
      _ ≤ C * K * (M * Real.exp (-c * vecNormSq x)) :=
          mul_le_mul_of_nonneg_left hE (mul_nonneg hC hK0)
  have hGint : Integrable (fun x : Vec d => Real.exp (-c * vecNormSq x)) volume :=
    integrable_exp_neg_mul_vecNormSq hc
  -- integrability of the integrand at s
  have hint : Integrable (fun x => P s x * heatKernel d s x) volume := by
    refine Integrable.mono' (hGint.const_mul (C * M)) (hmeas s hs) (Filter.Eventually.of_forall
      fun x => ?_)
    obtain ⟨h1, _⟩ := hPB s hsI x
    have hΦ := hΦ0 s hsI x
    have hE := hGM s hsI x
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hΦ]
    have hq0 := hq x
    calc |P s x| * heatKernel d s x
        ≤ C * Real.exp (2 * A' * vecNormSq x) * heatKernel d s x :=
          mul_le_mul_of_nonneg_right h1 hΦ.le
      _ = C * (Real.exp (2 * A' * vecNormSq x) * heatKernel d s x) := by ring
      _ ≤ C * ((1 + vecNormSq x) * (Real.exp (2 * A' * vecNormSq x) * heatKernel d s x)) := by
          have : 0 ≤ Real.exp (2 * A' * vecNormSq x) * heatKernel d s x := by positivity
          exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left this (by linarith)) hC
      _ ≤ C * (M * Real.exp (-c * vecNormSq x)) := mul_le_mul_of_nonneg_left hE hC
      _ = C * M * Real.exp (-c * vecNormSq x) := by ring
  have hmeas' : AEStronglyMeasurable (fun x =>
      (P' s x + P s x * (-(d : ℝ) / (2 * s) + vecNormSq x / (4 * s ^ 2))) *
        heatKernel d s x) volume := by
    refine Continuous.aestronglyMeasurable ?_
    have hvn : Continuous (fun x : Vec d => vecNormSq x) := contDiff_vecNormSq.continuous
    exact (hP'c.add ((hPc s hs).mul (continuous_const.add (hvn.div_const _)))).mul
      continuous_heatKernel_space
  have hIoo : Ioo a b ∈ nhds s := isOpen_Ioo.mem_nhds hs
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r x => P r x * heatKernel d r x)
    (F' := fun r x => (P' r x + P r x * (-(d : ℝ) / (2 * r) + vecNormSq x / (4 * r ^ 2))) *
      heatKernel d r x)
    (bound := fun x => C * K * (M * Real.exp (-c * vecNormSq x)))
    hIoo (Filter.mem_of_superset hIoo fun r hr => hmeas r hr) hint hmeas'
    (Filter.Eventually.of_forall fun x r hr => hbound r ⟨hr.1.le, hr.2.le⟩ x)
    (by simpa only [mul_assoc] using hGint.const_mul (C * K * M))
    (Filter.Eventually.of_forall fun x r hr => by
      have hr0 : 0 < r := ha.trans hr.1
      have h1 := hder r hr x
      have h2 := hasDerivAt_heatKernel_s hr0 x
      have := h1.mul h2
      convert this using 1
      ring)
  exact ⟨hint, key⟩

end

end PDE
