module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Friedland--Hayman: radial profiles with a cutoff at the origin

The cutoff `χ_ε(r) = smoothTransition((r - ε)/ε)` vanishes for `r ≤ ε` and equals `1` for `r ≥ 2ε`.
The radial profile is `g_ε(r) = χ_ε(r) r^a`, with explicit derivative `radProfD`.
-/

@[expose] public section

namespace PDE.FHLane

noncomputable section

namespace Susp

theorem deriv_smoothTransition_eq_zero {x : ℝ} (hx : x ∉ Set.Icc (0 : ℝ) 1) :
    deriv Real.smoothTransition x = 0 := by
  rcases not_and_or.1 hx with h | h
  · have h' : x < 0 := not_le.1 h
    have : Real.smoothTransition =ᶠ[nhds x] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (Iio_mem_nhds h') fun y hy =>
        Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [this.deriv_eq]; simp
  · have h' : 1 < x := not_le.1 h
    have : Real.smoothTransition =ᶠ[nhds x] fun _ => (1 : ℝ) :=
      Filter.eventually_of_mem (Ioi_mem_nhds h') fun y hy =>
        Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [this.deriv_eq]; simp

/-- A bound `K ≥ 0` for the derivative of the smooth step. -/
theorem exists_bound_deriv_smoothTransition :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |deriv Real.smoothTransition x| ≤ K := by
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := ⊤)).continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := deriv Real.smoothTransition)
    (s := Set.Icc (0 : ℝ) 1) hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · exact (hC x hx).trans' (by rw [Real.norm_eq_abs]) |>.trans (le_max_left _ _)
  · rw [deriv_smoothTransition_eq_zero hx, abs_zero]; exact le_max_right _ _

/-- The cutoff `χ_ε`. -/
def cutoff (ε r : ℝ) : ℝ := Real.smoothTransition ((r - ε) / ε)

/-- The derivative of the cutoff. -/
def cutoffD (ε r : ℝ) : ℝ := ε⁻¹ * deriv Real.smoothTransition ((r - ε) / ε)

/-- The radial profile `χ_ε(r) r^a`. -/
def radProf (ε a r : ℝ) : ℝ := cutoff ε r * r ^ a

/-- The derivative of the radial profile (for `r > 0`). -/
def radProfD (ε a r : ℝ) : ℝ := cutoffD ε r * r ^ a + cutoff ε r * (a * r ^ (a - 1))

theorem cutoff_nonneg (ε r : ℝ) : 0 ≤ cutoff ε r := Real.smoothTransition.nonneg _

theorem cutoff_le_one (ε r : ℝ) : cutoff ε r ≤ 1 := Real.smoothTransition.le_one _

theorem cutoff_eq_zero {ε r : ℝ} (hε : 0 < ε) (h : r ≤ ε) : cutoff ε r = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)

theorem cutoff_eq_one {ε r : ℝ} (hε : 0 < ε) (h : 2 * ε ≤ r) : cutoff ε r = 1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div hε).2 (by linarith))

theorem hasDerivAt_cutoff (ε r : ℝ) : HasDerivAt (cutoff ε) (cutoffD ε r) r := by
  have h1 : HasDerivAt (fun r : ℝ => (r - ε) / ε) ε⁻¹ r := by
    simpa [div_eq_mul_inv] using ((hasDerivAt_id r).sub_const ε).mul_const ε⁻¹
  have h2 := (Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)
    ((r - ε) / ε) |>.hasDerivAt
  have := h2.comp r h1
  unfold cutoff cutoffD
  rw [mul_comm]
  exact this

theorem cutoffD_eq_zero_of_lt {ε r : ℝ} (hε : 0 < ε) (h : r < ε) : cutoffD ε r = 0 := by
  unfold cutoffD
  rw [deriv_smoothTransition_eq_zero, mul_zero]
  intro hx
  have := hx.1
  have : (r - ε) / ε < 0 := div_neg_of_neg_of_pos (by linarith) hε
  linarith [hx.1]

theorem cutoffD_eq_zero_of_gt {ε r : ℝ} (hε : 0 < ε) (h : 2 * ε < r) : cutoffD ε r = 0 := by
  unfold cutoffD
  rw [deriv_smoothTransition_eq_zero, mul_zero]
  intro hx
  have : 1 < (r - ε) / ε := (one_lt_div hε).2 (by linarith)
  linarith [hx.2]

theorem abs_cutoffD_le {ε r K : ℝ} (hε : 0 < ε) (hr : 0 < r) (hK : ∀ x, |deriv Real.smoothTransition x| ≤ K)
    (hK0 : 0 ≤ K) : |cutoffD ε r| ≤ 2 * K / r := by
  by_cases h1 : r < ε
  · rw [cutoffD_eq_zero_of_lt hε h1, abs_zero]; positivity
  by_cases h2 : 2 * ε < r
  · rw [cutoffD_eq_zero_of_gt hε h2, abs_zero]; positivity
  push Not at h1 h2
  unfold cutoffD
  rw [abs_mul, abs_of_pos (inv_pos.2 hε)]
  calc ε⁻¹ * |deriv Real.smoothTransition ((r - ε) / ε)| ≤ ε⁻¹ * K :=
        mul_le_mul_of_nonneg_left (hK _) (inv_pos.2 hε).le
    _ ≤ 2 * K / r := by
        rw [inv_mul_eq_div, div_le_div_iff₀ hε hr]
        nlinarith

theorem radProf_eq_zero {ε a r : ℝ} (hε : 0 < ε) (h : r ≤ ε) : radProf ε a r = 0 := by
  unfold radProf; rw [cutoff_eq_zero hε h, zero_mul]

theorem radProf_eq_rpow {ε a r : ℝ} (hε : 0 < ε) (h : 2 * ε ≤ r) : radProf ε a r = r ^ a := by
  unfold radProf; rw [cutoff_eq_one hε h, one_mul]

theorem radProfD_eq {ε a r : ℝ} (hε : 0 < ε) (h : 2 * ε < r) :
    radProfD ε a r = a * r ^ (a - 1) := by
  unfold radProfD
  rw [cutoffD_eq_zero_of_gt hε h, cutoff_eq_one hε h.le]; ring

theorem hasDerivAt_radProf {ε a r : ℝ} (hr : 0 < r) :
    HasDerivAt (radProf ε a) (radProfD ε a r) r :=
  (hasDerivAt_cutoff ε r).mul (Real.hasDerivAt_rpow_const (Or.inl hr.ne'))

theorem abs_radProf_le {ε a r : ℝ} (hr : 0 ≤ r) : |radProf ε a r| ≤ r ^ a := by
  unfold radProf
  rw [abs_mul, abs_of_nonneg (cutoff_nonneg _ _), abs_of_nonneg (Real.rpow_nonneg hr _)]
  calc cutoff ε r * r ^ a ≤ 1 * r ^ a :=
        mul_le_mul_of_nonneg_right (cutoff_le_one _ _) (Real.rpow_nonneg hr _)
    _ = r ^ a := one_mul _

theorem abs_radProfD_le {ε a r K : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) (hr : 0 < r)
    (hK : ∀ x, |deriv Real.smoothTransition x| ≤ K) (hK0 : 0 ≤ K) :
    |radProfD ε a r| ≤ (2 * K + a) * r ^ (a - 1) := by
  have hrp : r ^ a = r * r ^ (a - 1) := by
    rw [Real.rpow_sub_one hr.ne' a]; field_simp
  have hq : 0 ≤ r ^ (a - 1) := Real.rpow_nonneg hr.le _
  unfold radProfD
  have h1 : |cutoffD ε r * r ^ a| ≤ 2 * K * r ^ (a - 1) := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hr.le _)]
    calc |cutoffD ε r| * r ^ a ≤ (2 * K / r) * r ^ a :=
          mul_le_mul_of_nonneg_right (abs_cutoffD_le hε hr hK hK0) (Real.rpow_nonneg hr.le _)
      _ = 2 * K * r ^ (a - 1) := by rw [hrp]; field_simp
  have h2 : |cutoff ε r * (a * r ^ (a - 1))| ≤ a * r ^ (a - 1) := by
    rw [abs_mul, abs_of_nonneg (cutoff_nonneg _ _), abs_of_nonneg (mul_nonneg ha hq)]
    calc cutoff ε r * (a * r ^ (a - 1)) ≤ 1 * (a * r ^ (a - 1)) :=
          mul_le_mul_of_nonneg_right (cutoff_le_one _ _) (mul_nonneg ha hq)
      _ = a * r ^ (a - 1) := one_mul _
  calc _ ≤ |cutoffD ε r * r ^ a| + |cutoff ε r * (a * r ^ (a - 1))| := abs_add_le _ _
    _ ≤ 2 * K * r ^ (a - 1) + a * r ^ (a - 1) := add_le_add h1 h2
    _ = (2 * K + a) * r ^ (a - 1) := by ring

end Susp

end

end PDE.FHLane
