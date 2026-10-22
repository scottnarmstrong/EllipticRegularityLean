module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Radial cutoffs `Z(s) = ζ(√s)` and their kernels

For `0 < r`, `0 < k`: `ζ(ρ) = 1 - σ((ρ - r)/k)` with `σ = Real.smoothTransition` is a smooth
profile equal to `1` on `ρ ≤ r` and `0` on `ρ ≥ r + k`; `Z(s) = ζ(√s)` is globally smooth, equal
to `1` on `s ≤ r²` (also for `s < 0`) and `0` for `s ≥ (r+k)²`.  Its derivative is
`Z'(s) = -ker(√s)/(2√s)` with the kernel `ker(ρ) = σ'((ρ - r)/k)/k` of total mass `1`
supported in `[r, r + k]`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

noncomputable section

/-- The radial profile `ζ(ρ) = 1 - σ((ρ - r)/k)`. -/
def acfZeta (r k ρ : ℝ) : ℝ := 1 - Real.smoothTransition ((ρ - r) / k)

/-- The cutoff in the variable `s = |x|²`: `Z(s) = ζ(√s)`. -/
def acfCut (r k s : ℝ) : ℝ := acfZeta r k (Real.sqrt s)

/-- The averaging kernel `σ'((ρ - r)/k)/k`. -/
def acfKer (r k ρ : ℝ) : ℝ := deriv Real.smoothTransition ((ρ - r) / k) / k

variable {r k : ℝ}

theorem acfCut_nonneg (s : ℝ) : 0 ≤ acfCut r k s := by
  unfold acfCut acfZeta
  linarith [Real.smoothTransition.le_one ((Real.sqrt s - r) / k)]

theorem acfCut_le_one (s : ℝ) : acfCut r k s ≤ 1 := by
  unfold acfCut acfZeta
  linarith [Real.smoothTransition.nonneg ((Real.sqrt s - r) / k)]

theorem acfCut_eq_one (hr : 0 < r) (hk : 0 < k) {s : ℝ} (hs : s ≤ r ^ 2) : acfCut r k s = 1 := by
  unfold acfCut acfZeta
  have : Real.sqrt s ≤ r := Real.sqrt_le_iff.mpr ⟨hr.le, hs⟩
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hk.le)]
  ring

theorem acfCut_eq_zero (hk : 0 < k) {s : ℝ} (hs : (r + k) ^ 2 ≤ s) :
    acfCut r k s = 0 := by
  unfold acfCut acfZeta
  have : r + k ≤ Real.sqrt s := Real.le_sqrt_of_sq_le hs
  rw [Real.smoothTransition.one_of_one_le ((one_le_div hk).mpr (by linarith))]
  ring

theorem contDiff_acfCut (hr : 0 < r) (hk : 0 < k) : ContDiff ℝ (⊤ : ℕ∞) (acfCut r k) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : s < r ^ 2
  · have : acfCut r k =ᶠ[nhds s] fun _ => 1 := by
      filter_upwards [gt_mem_nhds hs] with t ht using acfCut_eq_one hr hk ht.le
    exact (contDiffAt_const).congr_of_eventuallyEq this
  · have hs0 : 0 < s := lt_of_lt_of_le (by positivity) (not_lt.mp hs)
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) Real.sqrt s := Real.contDiffAt_sqrt hs0.ne'
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (acfZeta r k) :=
      contDiff_const.sub (Real.smoothTransition.contDiff.comp
        ((contDiff_id.sub contDiff_const).div_const k))
    exact h2.contDiffAt.comp s h1

theorem hasDerivAt_acfZeta (ρ : ℝ) :
    HasDerivAt (acfZeta r k) (-acfKer r k ρ) ρ := by
  have hd : DifferentiableAt ℝ Real.smoothTransition ((ρ - r) / k) :=
    (Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp) _
  have h1 : HasDerivAt (fun ρ : ℝ => (ρ - r) / k) (1 / k) ρ := by
    simpa using ((hasDerivAt_id ρ).sub_const r).div_const k
  have h2 := hd.hasDerivAt.comp ρ h1
  have h3 := h2.const_sub 1
  refine h3.congr_deriv ?_
  unfold acfKer
  ring

theorem hasDerivAt_acfCut {s : ℝ} (hs : 0 < s) :
    HasDerivAt (acfCut r k) (-acfKer r k (Real.sqrt s) / (2 * Real.sqrt s)) s := by
  have h1 := Real.hasDerivAt_sqrt hs.ne'
  have h2 := (hasDerivAt_acfZeta (r := r) (k := k) (Real.sqrt s)).comp s h1
  refine h2.congr_deriv ?_
  ring

theorem deriv_acfCut_eq_zero_of_lt (hr : 0 < r) (hk : 0 < k) {s : ℝ} (hs : s < r ^ 2) :
    deriv (acfCut r k) s = 0 := by
  have : acfCut r k =ᶠ[nhds s] fun _ => 1 := by
    filter_upwards [gt_mem_nhds hs] with t ht using acfCut_eq_one hr hk ht.le
  rw [this.deriv_eq]; simp

theorem deriv_acfCut_eq_zero_of_gt (hk : 0 < k) {s : ℝ} (hs : (r + k) ^ 2 < s) :
    deriv (acfCut r k) s = 0 := by
  have : acfCut r k =ᶠ[nhds s] fun _ => 0 := by
    filter_upwards [lt_mem_nhds hs] with t ht using acfCut_eq_zero hk ht.le
  rw [this.deriv_eq]; simp

theorem deriv_deriv_acfCut_eq_zero_of_lt (hr : 0 < r) (hk : 0 < k) {s : ℝ} (hs : s < r ^ 2) :
    deriv (deriv (acfCut r k)) s = 0 := by
  have : deriv (acfCut r k) =ᶠ[nhds s] fun _ => 0 := by
    filter_upwards [gt_mem_nhds hs] with t ht using deriv_acfCut_eq_zero_of_lt hr hk ht
  rw [this.deriv_eq]; simp

theorem deriv_deriv_acfCut_eq_zero_of_gt (hk : 0 < k) {s : ℝ} (hs : (r + k) ^ 2 < s) :
    deriv (deriv (acfCut r k)) s = 0 := by
  have : deriv (acfCut r k) =ᶠ[nhds s] fun _ => 0 := by
    filter_upwards [lt_mem_nhds hs] with t ht using deriv_acfCut_eq_zero_of_gt hk ht
  rw [this.deriv_eq]; simp

theorem acfKer_eq_zero_of_lt (hk : 0 < k) {ρ : ℝ} (h : ρ < r) : acfKer r k ρ = 0 := by
  unfold acfKer
  have : Real.smoothTransition =ᶠ[nhds ((ρ - r) / k)] fun _ => 0 := by
    filter_upwards [gt_mem_nhds (show (ρ - r) / k < 0 from div_neg_of_neg_of_pos (by linarith) hk)]
      with t ht using Real.smoothTransition.zero_of_nonpos ht.le
  rw [this.deriv_eq]; simp

theorem acfKer_eq_zero_of_gt (hk : 0 < k) {ρ : ℝ} (h : r + k < ρ) : acfKer r k ρ = 0 := by
  unfold acfKer
  have h1 : 1 < (ρ - r) / k := by rw [lt_div_iff₀ hk]; linarith
  have : Real.smoothTransition =ᶠ[nhds ((ρ - r) / k)] fun _ => 1 := by
    filter_upwards [lt_mem_nhds h1] with t ht using Real.smoothTransition.one_of_one_le ht.le
  rw [this.deriv_eq]; simp

theorem continuous_acfKer : Continuous (acfKer r k) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition := Real.smoothTransition.contDiff
  have hc : Continuous (deriv Real.smoothTransition) := h.continuous_deriv (by simp)
  exact (hc.comp ((continuous_id.sub continuous_const).div_const k)).div_const k

theorem acfKer_support_subset (hk : 0 < k) : Function.support (acfKer r k) ⊆ Icc r (r + k) := by
  intro ρ hρ
  by_contra h
  rw [mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · exact hρ (acfKer_eq_zero_of_lt hk h)
  · exact hρ (acfKer_eq_zero_of_gt hk h)

/-- The kernel has total mass `1`. -/
theorem integral_acfKer (hk : 0 < k) : ∫ ρ, acfKer r k ρ = 1 := by
  have hsupp : ∀ ρ, ρ ∉ Icc r (r + k) → acfKer r k ρ = 0 := fun ρ hρ =>
    Function.notMem_support.mp fun h => hρ (acfKer_support_subset hk h)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  have hd : ∀ ρ ∈ uIcc r (r + k), HasDerivAt (fun ρ => 1 - acfZeta r k ρ) (acfKer r k ρ) ρ := by
    intro ρ _
    simpa using (hasDerivAt_acfZeta (r := r) (k := k) ρ).const_sub 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (continuous_acfKer.intervalIntegrable _ _)]
  have h1 : acfZeta r k r = 1 := by
    unfold acfZeta
    simp [Real.smoothTransition.zero]
  have h2 : acfZeta r k (r + k) = 0 := by
    unfold acfZeta
    have : (r + k - r) / k = 1 := by field_simp; ring
    rw [this, Real.smoothTransition.one]; ring
  simp [h1, h2]

/-- The kernel is bounded by `C / k`. -/
theorem exists_acfKer_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (r k ρ : ℝ), 0 < k →
    |acfKer r k ρ| ≤ C / k := by
  have h : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition := Real.smoothTransition.contDiff
  have hc : Continuous (deriv Real.smoothTransition) := h.continuous_deriv (by simp)
  have hcs : HasCompactSupport (deriv Real.smoothTransition) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := 0) (b := 1)) ?_
    intro x hx
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · have : Real.smoothTransition =ᶠ[nhds x] fun _ => 0 := by
        filter_upwards [gt_mem_nhds hx] with t ht using Real.smoothTransition.zero_of_nonpos ht.le
      rw [this.deriv_eq]; simp
    · have : Real.smoothTransition =ᶠ[nhds x] fun _ => 1 := by
        filter_upwards [lt_mem_nhds hx] with t ht using
          Real.smoothTransition.one_of_one_le ht.le
      rw [this.deriv_eq]; simp
  obtain ⟨C, hC⟩ := hc.norm.bounded_above_of_compact_support hcs.norm
  refine ⟨max C 0, le_max_right _ _, fun r k ρ hk => ?_⟩
  unfold acfKer
  rw [abs_div, abs_of_pos hk]
  have h1 : |deriv Real.smoothTransition ((ρ - r) / k)| ≤ C := by simpa using hC ((ρ - r) / k)
  exact div_le_div_of_nonneg_right (h1.trans (le_max_left _ _)) hk.le

end

end PDE
