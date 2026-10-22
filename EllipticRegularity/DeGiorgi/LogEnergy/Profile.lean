module

public import PDEFoundation.Sobolev.Cutoff.Profile
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# A sharp one-dimensional smooth transition

For `0 < ε ≤ 1/4` there is a smooth function `χ` equal to `1` on `(-∞, 0]`, to `0` on `[1, ∞)`,
with values in `[0, 1]` and `|χ'| ≤ (1 - 2ε)⁻¹`.  It is built as one minus the normalized primitive
of the plateau bump `p(τ/ε) p((1-τ)/ε)`, where `p` is the canonical transition profile.
-/

@[expose] public section

namespace PDE.DGNMLogEnergy

open MeasureTheory intervalIntegral

/-- The plateau bump. -/
noncomputable def bump (ε τ : ℝ) : ℝ :=
  smoothTransitionProfile (τ / ε) * smoothTransitionProfile ((1 - τ) / ε)

theorem bump_contDiff (ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (bump ε) := by
  unfold bump
  exact (smoothTransitionProfile.smooth.comp (contDiff_id.div_const ε)).mul
    (smoothTransitionProfile.smooth.comp ((contDiff_const.sub contDiff_id).div_const ε))

theorem bump_nonneg (ε τ : ℝ) : 0 ≤ bump ε τ :=
  mul_nonneg (smoothTransitionProfile.nonneg _) (smoothTransitionProfile.nonneg _)

theorem bump_le_one (ε τ : ℝ) : bump ε τ ≤ 1 :=
  calc _ ≤ 1 * 1 := mul_le_mul (smoothTransitionProfile.le_one _) (smoothTransitionProfile.le_one _)
        (smoothTransitionProfile.nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem bump_eq_zero_of_nonpos {ε τ : ℝ} (hε : 0 < ε) (h : τ ≤ 0) : bump ε τ = 0 := by
  unfold bump
  rw [smoothTransitionProfile.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg h hε.le), zero_mul]

theorem bump_eq_zero_of_one_le {ε τ : ℝ} (hε : 0 < ε) (h : 1 ≤ τ) : bump ε τ = 0 := by
  unfold bump
  rw [smoothTransitionProfile.zero_of_nonpos (t := (1 - τ) / ε)
    (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le), mul_zero]

theorem bump_eq_one {ε τ : ℝ} (hε : 0 < ε) (h1 : ε ≤ τ) (h2 : τ ≤ 1 - ε) : bump ε τ = 1 := by
  unfold bump
  rw [smoothTransitionProfile.one_of_one_le ((one_le_div hε).mpr h1),
    smoothTransitionProfile.one_of_one_le ((one_le_div hε).mpr (by linarith)), one_mul]

/-- The primitive of the bump from `0`. -/
noncomputable def bumpInt (ε t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, bump ε s

theorem bumpInt_hasDerivAt (ε t : ℝ) : HasDerivAt (bumpInt ε) (bump ε t) t :=
  ((bump_contDiff ε).continuous.integral_hasStrictDerivAt 0 t).hasDerivAt

theorem bumpInt_deriv (ε t : ℝ) : deriv (bumpInt ε) t = bump ε t :=
  (bumpInt_hasDerivAt ε t).deriv

theorem bumpInt_contDiff (ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (bumpInt ε) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun t => (bumpInt_hasDerivAt ε t).differentiableAt, ?_⟩
  have : deriv (bumpInt ε) = bump ε := funext (bumpInt_deriv ε)
  rw [this]
  exact bump_contDiff ε

theorem bumpInt_monotone (ε : ℝ) : Monotone (bumpInt ε) :=
  monotone_of_deriv_nonneg (fun t => (bumpInt_hasDerivAt ε t).differentiableAt)
    (fun t => by rw [bumpInt_deriv]; exact bump_nonneg _ _)

theorem bumpInt_eq_zero_of_nonpos {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ 0) : bumpInt ε t = 0 := by
  unfold bumpInt
  rw [integral_symm]
  have : ∫ s in t..(0 : ℝ), bump ε s = 0 := by
    have h : ∀ s ∈ Set.uIcc t 0, bump ε s = 0 := fun s hs => by
      rw [Set.uIcc_of_le ht] at hs
      exact bump_eq_zero_of_nonpos hε hs.2
    rw [integral_congr h]; simp
  rw [this]; simp

theorem bumpInt_eq_of_one_le {ε t : ℝ} (hε : 0 < ε) (ht : 1 ≤ t) :
    bumpInt ε t = bumpInt ε 1 := by
  unfold bumpInt
  rw [← integral_add_adjacent_intervals (b := 1) ((bump_contDiff ε).continuous.intervalIntegrable _ _)
    ((bump_contDiff ε).continuous.intervalIntegrable _ _)]
  have h : ∀ s ∈ Set.uIcc (1 : ℝ) t, bump ε s = 0 := fun s hs => by
    rw [Set.uIcc_of_le ht] at hs
    exact bump_eq_zero_of_one_le hε hs.1
  rw [integral_congr h]; simp

theorem one_sub_two_mul_le_bumpInt_one {ε : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    1 - 2 * ε ≤ bumpInt ε 1 := by
  have hint : bumpInt ε (1 - ε) - bumpInt ε ε = 1 - 2 * ε := by
    unfold bumpInt
    rw [integral_interval_sub_left ((bump_contDiff ε).continuous.intervalIntegrable _ _)
      ((bump_contDiff ε).continuous.intervalIntegrable _ _)]
    have h : ∀ s ∈ Set.uIcc ε (1 - ε), bump ε s = 1 := fun s hs => by
      rw [Set.uIcc_of_le (by linarith)] at hs
      exact bump_eq_one hε hs.1 hs.2
    rw [integral_congr h]; simp; ring
  have h0 : 0 ≤ bumpInt ε ε := by
    rw [← bumpInt_eq_zero_of_nonpos hε (le_refl 0)]
    · exact bumpInt_monotone ε hε.le
  have hm : bumpInt ε (1 - ε) ≤ bumpInt ε 1 := bumpInt_monotone ε (by linarith)
  linarith

/-- The sharp transition profile. -/
noncomputable def sharpProfile (ε t : ℝ) : ℝ := 1 - bumpInt ε t / bumpInt ε 1

theorem sharpProfile_contDiff (ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (sharpProfile ε) := by
  unfold sharpProfile
  exact contDiff_const.sub ((bumpInt_contDiff ε).div_const _)

theorem sharpProfile_eq_one {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ 0) : sharpProfile ε t = 1 := by
  unfold sharpProfile; rw [bumpInt_eq_zero_of_nonpos hε ht]; simp

theorem sharpProfile_eq_zero {ε t : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) (ht : 1 ≤ t) :
    sharpProfile ε t = 0 := by
  have hI : 0 < bumpInt ε 1 := by linarith [one_sub_two_mul_le_bumpInt_one hε hε4]
  unfold sharpProfile; rw [bumpInt_eq_of_one_le hε ht, div_self hI.ne']; simp

theorem sharpProfile_mem {ε : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) (t : ℝ) :
    0 ≤ sharpProfile ε t ∧ sharpProfile ε t ≤ 1 := by
  have hI : 0 < bumpInt ε 1 := by linarith [one_sub_two_mul_le_bumpInt_one hε hε4]
  have h0 : 0 ≤ bumpInt ε t := by
    rw [← bumpInt_eq_zero_of_nonpos hε (le_refl 0)]
    rcases le_total 0 t with h | h
    · exact bumpInt_monotone ε h
    · rw [bumpInt_eq_zero_of_nonpos hε h, bumpInt_eq_zero_of_nonpos hε (le_refl 0)]
  have h1 : bumpInt ε t ≤ bumpInt ε 1 := by
    rcases le_total t 1 with h | h
    · exact bumpInt_monotone ε h
    · rw [bumpInt_eq_of_one_le hε h]
  unfold sharpProfile
  constructor
  · have := (div_le_one hI).mpr h1; linarith
  · have := div_nonneg h0 hI.le; linarith

theorem abs_deriv_sharpProfile_le {ε : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) (t : ℝ) :
    |deriv (sharpProfile ε) t| ≤ (1 - 2 * ε)⁻¹ := by
  have hI : 1 - 2 * ε ≤ bumpInt ε 1 := one_sub_two_mul_le_bumpInt_one hε hε4
  have hpos : 0 < 1 - 2 * ε := by linarith
  have hd : deriv (sharpProfile ε) t = -(bump ε t / bumpInt ε 1) := by
    have := ((bumpInt_hasDerivAt ε t).div_const (bumpInt ε 1)).const_sub 1
    exact this.deriv
  rw [hd, abs_neg, abs_of_nonneg (div_nonneg (bump_nonneg _ _) (by linarith))]
  calc bump ε t / bumpInt ε 1 ≤ 1 / bumpInt ε 1 :=
        div_le_div_of_nonneg_right (bump_le_one _ _) (by linarith)
    _ ≤ 1 / (1 - 2 * ε) := one_div_le_one_div_of_le hpos hI
    _ = (1 - 2 * ε)⁻¹ := one_div _

end PDE.DGNMLogEnergy
