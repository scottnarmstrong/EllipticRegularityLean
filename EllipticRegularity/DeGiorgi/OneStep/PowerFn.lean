module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Topology.Algebra.Module.ModuleTopology


/-!
# `C¹` functions with bounded derivative agreeing with a power

For `δ > 0` and a real exponent `s` we construct globally defined `C¹` functions `G` with
bounded derivative and `G t = t ^ s` on `[δ, ∞)` (if `s ≤ 1`) or on `[δ, M]` (any `s`),
together with `deriv G t = s * t ^ (s - 1)` on the same set.  These feed the `H¹` chain rule
for `u ↦ u ^ s` when `u ≥ δ` (and `u ≤ M`).
-/

@[expose] public section

namespace PDE.DGNMOneStep

open Real

/-- A smooth positive function equal to the identity on `[3δ/4, ∞)` and `≥ δ/2` everywhere. -/
noncomputable def powBase (δ : ℝ) (t : ℝ) : ℝ :=
  δ / 2 + Real.smoothTransition ((4 * t - 2 * δ) / δ) * (t - δ / 2)

variable {δ : ℝ}

theorem powBase_eq_of_le (hδ : 0 < δ) {t : ℝ} (ht : 3 * δ / 4 ≤ t) : powBase δ t = t := by
  unfold powBase
  have : Real.smoothTransition ((4 * t - 2 * δ) / δ) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ hδ]; linarith
  rw [this]; ring

theorem powBase_eq_of_ge (hδ : 0 < δ) {t : ℝ} (ht : t ≤ δ / 2) : powBase δ t = δ / 2 := by
  unfold powBase
  have : Real.smoothTransition ((4 * t - 2 * δ) / δ) = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    apply div_nonpos_of_nonpos_of_nonneg _ hδ.le
    linarith
  rw [this]; ring

theorem powBase_ge (hδ : 0 < δ) (t : ℝ) : δ / 2 ≤ powBase δ t := by
  unfold powBase
  by_cases ht : t ≤ δ / 2
  · have := powBase_eq_of_ge hδ ht
    unfold powBase at this; linarith
  · rw [not_le] at ht
    have h0 := Real.smoothTransition.nonneg ((4 * t - 2 * δ) / δ)
    nlinarith

theorem powBase_pos (hδ : 0 < δ) (t : ℝ) : 0 < powBase δ t :=
  lt_of_lt_of_le (by linarith) (powBase_ge hδ t)

theorem powBase_contDiff : ContDiff ℝ 1 (powBase δ) := by
  unfold powBase
  have h1 : ContDiff ℝ 1 (fun t : ℝ => Real.smoothTransition ((4 * t - 2 * δ) / δ)) :=
    (Real.smoothTransition.contDiff (n := 1)).comp (by fun_prop)
  exact contDiff_const.add (h1.mul (by fun_prop))

theorem deriv_powBase_of_lt (hδ : 0 < δ) {t : ℝ} (ht : 3 * δ / 4 < t) :
    deriv (powBase δ) t = 1 := by
  have : (powBase δ) =ᶠ[nhds t] (fun x => x) := by
    filter_upwards [lt_mem_nhds ht] with x hx
    exact powBase_eq_of_le hδ hx.le
  rw [this.deriv_eq]; simp

theorem deriv_powBase_of_gt (hδ : 0 < δ) {t : ℝ} (ht : t < δ / 2) :
    deriv (powBase δ) t = 0 := by
  have : (powBase δ) =ᶠ[nhds t] (fun _ => δ / 2) := by
    filter_upwards [gt_mem_nhds ht] with x hx
    exact powBase_eq_of_ge hδ hx.le
  rw [this.deriv_eq]; simp

theorem exists_bound_deriv_powBase (hδ : 0 < δ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |deriv (powBase δ) t| ≤ B := by
  have hcont : Continuous (deriv (powBase δ)) := (powBase_contDiff).continuous_deriv le_rfl
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := δ / 2) (b := 3 * δ / 4)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max K 1, le_trans zero_le_one (le_max_right _ _), fun t => ?_⟩
  by_cases h1 : t < δ / 2
  · rw [deriv_powBase_of_gt hδ h1]; simp
  · by_cases h2 : 3 * δ / 4 < t
    · rw [deriv_powBase_of_lt hδ h2]; simp
    · rw [not_lt] at h1 h2
      have := hK t ⟨h1, h2⟩
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)

/-- One-sided power function: `C¹`, bounded derivative, `G t = t ^ s` for `t ≥ δ` (`s ≤ 1`). -/
theorem exists_powerFn_oneSided (hδ : 0 < δ) {s : ℝ} (hs : s ≤ 1) :
    ∃ G : ℝ → ℝ, ContDiff ℝ 1 G ∧ (∃ B : ℝ, 0 ≤ B ∧ ∀ t, |deriv G t| ≤ B) ∧
      (∀ t, 0 ≤ G t) ∧ ∀ t, δ ≤ t → G t = t ^ s ∧ deriv G t = s * t ^ (s - 1) := by
  refine ⟨fun t => powBase δ t ^ s, ?_, ?_, ?_, ?_⟩
  · exact (powBase_contDiff).rpow_const_of_ne (fun t => (powBase_pos hδ t).ne')
  · obtain ⟨B, hB0, hB⟩ := exists_bound_deriv_powBase hδ
    have hderiv : ∀ t, deriv (fun t => powBase δ t ^ s) t =
        deriv (powBase δ) t * s * powBase δ t ^ (s - 1) := by
      intro t
      have hd : HasDerivAt (powBase δ) (deriv (powBase δ) t) t :=
        (((powBase_contDiff).differentiable one_ne_zero) t).hasDerivAt
      exact (hd.rpow_const (Or.inl (powBase_pos hδ t).ne')).deriv
    refine ⟨B * |s| * (δ / 2) ^ (s - 1), by positivity, fun t => ?_⟩
    rw [hderiv, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (powBase_pos hδ t) _)]
    have h1 : powBase δ t ^ (s - 1) ≤ (δ / 2) ^ (s - 1) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (powBase_ge hδ t) (by linarith)
    have h2 := hB t
    have h3 : 0 ≤ |s| := abs_nonneg s
    have h4 : 0 ≤ |deriv (powBase δ) t| := abs_nonneg _
    have h5 : 0 ≤ powBase δ t ^ (s - 1) := Real.rpow_nonneg (powBase_pos hδ t).le _
    calc |deriv (powBase δ) t| * |s| * powBase δ t ^ (s - 1)
        ≤ B * |s| * powBase δ t ^ (s - 1) := by gcongr
      _ ≤ B * |s| * (δ / 2) ^ (s - 1) := by gcongr
  · intro t
    exact Real.rpow_nonneg (powBase_pos hδ t).le _
  · intro t ht
    have h34 : 3 * δ / 4 < t := by linarith
    have heq : (fun t => powBase δ t ^ s) =ᶠ[nhds t] (fun x => x ^ s) := by
      filter_upwards [lt_mem_nhds h34] with x hx
      simp only [powBase_eq_of_le hδ hx.le]
    refine ⟨by simp only [powBase_eq_of_le hδ h34.le], ?_⟩
    rw [heq.deriv_eq, Real.deriv_rpow_const]

end PDE.DGNMOneStep
