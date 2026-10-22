module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus


/-!
# Truncated powers for the parabolic Moser iteration

For `p > 1`, `ε > 0` and a truncation level `N ≥ 0` we build `F, G : ℝ → ℝ` with `F ∈ C²`,
`F''` bounded, `G ∈ C¹`, `G'` bounded, which on `s ≥ 0` satisfy, with `K = 2 + p/(p-1)`,

* `F, F'' ≥ 0`, `F'² ≤ K F'' F`, `G² ≤ K F`, `G'² ≤ K F''`,
* `F s ≤ (s+ε)^p`, `G ≥ 0`, and `G s = (s+ε)^{p/2}` for `s ≤ N`.

Both are built by integrating a capped power profile: `F'' = p(p-1) c^{p-2}` and
`G' = (p/2) c^{p/2-1}` with `c(s) = max (s+ε) ε`, capped at `N+ε` when `p > 2`.  For `p ≤ 2`
no cap is needed, since `c ≥ ε` already bounds the negative powers.  Beyond the cap `F` is the
quadratic and `G` the linear Taylor polynomial of `(s+ε)^p`, `(s+ε)^{p/2}` at `s = N`.
-/

@[expose] public section

namespace PDE.Parabolic.LocalMax

open MeasureTheory Set intervalIntegral

noncomputable section

/-- The capped base `max (s+ε) ε`, additionally capped at `N + ε` when `p > 2`. -/
def powCap (p ε N s : ℝ) : ℝ :=
  if p ≤ 2 then max (s + ε) ε else min (max (s + ε) ε) (N + ε)

/-- `F'' = p(p-1) c^{p-2}`. -/
def powF2 (p ε N s : ℝ) : ℝ := p * (p - 1) * powCap p ε N s ^ (p - 2)

/-- `F' = p ε^{p-1} + ∫₀ˢ F''`. -/
def powF1 (p ε N s : ℝ) : ℝ := p * ε ^ (p - 1) + ∫ r in (0 : ℝ)..s, powF2 p ε N r

/-- The truncated power `F = ε^p + ∫₀ˢ F'`. -/
def powF (p ε N s : ℝ) : ℝ := ε ^ p + ∫ r in (0 : ℝ)..s, powF1 p ε N r

/-- `G' = (p/2) c^{p/2-1}`. -/
def powG1 (p ε N s : ℝ) : ℝ := p / 2 * powCap p ε N s ^ (p / 2 - 1)

/-- The truncated half power `G = ε^{p/2} + ∫₀ˢ G'`. -/
def powG (p ε N s : ℝ) : ℝ := ε ^ (p / 2) + ∫ r in (0 : ℝ)..s, powG1 p ε N r

variable {p ε N : ℝ}

theorem powCap_continuous : Continuous (powCap p ε N) := by
  unfold powCap
  split_ifs <;> fun_prop

theorem le_powCap (hN : 0 ≤ N) (s : ℝ) : ε ≤ powCap p ε N s := by
  unfold powCap
  split_ifs
  · exact le_max_right _ _
  · exact le_min (le_max_right _ _) (by linarith)

theorem powCap_pos (hε : 0 < ε) (hN : 0 ≤ N) (s : ℝ) : 0 < powCap p ε N s :=
  hε.trans_le (le_powCap hN s)

theorem powCap_le_self {s : ℝ} (hs : 0 ≤ s) : powCap p ε N s ≤ s + ε := by
  unfold powCap
  split_ifs
  · exact max_le le_rfl (by linarith)
  · exact (min_le_left _ _).trans (max_le le_rfl (by linarith))

theorem powCap_eq_of_le {s : ℝ} (hs : 0 ≤ s) (h : p ≤ 2 ∨ s ≤ N) : powCap p ε N s = s + ε := by
  unfold powCap
  have hmax : max (s + ε) ε = s + ε := max_eq_left (by linarith)
  split_ifs with hp
  · exact hmax
  · rw [hmax]
    exact min_eq_left (by rcases h with h | h <;> [exact absurd h hp; linarith])

theorem powCap_eq_cap (hp : 2 < p) {s : ℝ} (hs : N ≤ s) (hN : 0 ≤ N) :
    powCap p ε N s = N + ε := by
  unfold powCap
  split_ifs with h
  · exact absurd h (not_le.2 hp)
  rw [max_eq_left (by linarith)]
  exact min_eq_right (by linarith)

theorem powCap_le_cap (hp : 2 < p) (s : ℝ) : powCap p ε N s ≤ N + ε := by
  unfold powCap
  split_ifs with h
  · exact absurd h (not_le.2 hp)
  exact min_le_right _ _

section Regularity

variable (hε : 0 < ε) (hN : 0 ≤ N)
include hε hN

theorem powF2_continuous : Continuous (powF2 p ε N) := by
  unfold powF2
  exact continuous_const.mul (powCap_continuous.rpow_const fun s =>
    Or.inl (powCap_pos hε hN s).ne')

theorem powG1_continuous : Continuous (powG1 p ε N) := by
  unfold powG1
  exact continuous_const.mul (powCap_continuous.rpow_const fun s =>
    Or.inl (powCap_pos hε hN s).ne')

theorem powF1_hasDerivAt (s : ℝ) : HasDerivAt (powF1 p ε N) (powF2 p ε N s) s :=
  ((powF2_continuous hε hN).integral_hasStrictDerivAt 0 s).hasDerivAt.const_add _

theorem powF1_continuous : Continuous (powF1 p ε N) :=
  continuous_iff_continuousAt.2 fun s => (powF1_hasDerivAt hε hN s).continuousAt

theorem powF_hasDerivAt (s : ℝ) : HasDerivAt (powF p ε N) (powF1 p ε N s) s :=
  ((powF1_continuous hε hN).integral_hasStrictDerivAt 0 s).hasDerivAt.const_add _

theorem powG_hasDerivAt (s : ℝ) : HasDerivAt (powG p ε N) (powG1 p ε N s) s :=
  ((powG1_continuous hε hN).integral_hasStrictDerivAt 0 s).hasDerivAt.const_add _

theorem deriv_powF : deriv (powF p ε N) = powF1 p ε N :=
  funext fun s => (powF_hasDerivAt hε hN s).deriv

theorem deriv_powF1 : deriv (powF1 p ε N) = powF2 p ε N :=
  funext fun s => (powF1_hasDerivAt hε hN s).deriv

theorem deriv_deriv_powF : deriv (deriv (powF p ε N)) = powF2 p ε N := by
  rw [deriv_powF hε hN, deriv_powF1 hε hN]

theorem deriv_powG : deriv (powG p ε N) = powG1 p ε N :=
  funext fun s => (powG_hasDerivAt hε hN s).deriv

theorem powF_contDiff : ContDiff ℝ 2 (powF p ε N) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun s => (powF_hasDerivAt hε hN s).differentiableAt, by simp, ?_⟩
  rw [deriv_powF hε hN, contDiff_one_iff_deriv, deriv_powF1 hε hN]
  exact ⟨fun s => (powF1_hasDerivAt hε hN s).differentiableAt, powF2_continuous hε hN⟩

theorem powG_contDiff : ContDiff ℝ 1 (powG p ε N) := by
  rw [contDiff_one_iff_deriv, deriv_powG hε hN]
  exact ⟨fun s => (powG_hasDerivAt hε hN s).differentiableAt, powG1_continuous hε hN⟩

end Regularity

section Bounds

theorem powF2_nonneg (hp : 1 < p) (hε : 0 < ε) (hN : 0 ≤ N) (s : ℝ) : 0 ≤ powF2 p ε N s := by
  unfold powF2
  have := (powCap_pos (p := p) hε hN s).le
  have : 0 ≤ p - 1 := by linarith
  positivity

theorem powG1_nonneg (hp : 1 < p) (hε : 0 < ε) (hN : 0 ≤ N) (s : ℝ) : 0 ≤ powG1 p ε N s := by
  unfold powG1
  have := (powCap_pos (p := p) hε hN s).le
  have : 0 ≤ p := by linarith
  positivity

/-- A uniform bound for a capped power `c^e` with `ε ≤ c`, and `c ≤ N + ε` when `p > 2`. -/
theorem powCap_rpow_le (hε : 0 < ε) (hN : 0 ≤ N) {e : ℝ} (he : p ≤ 2 → e ≤ 0) (s : ℝ) :
    powCap p ε N s ^ e ≤ max (ε ^ e) ((N + ε) ^ e) := by
  by_cases hp : p ≤ 2
  · exact (Real.rpow_le_rpow_of_nonpos hε (le_powCap hN s) (he hp)).trans (le_max_left _ _)
  · by_cases he0 : 0 ≤ e
    · exact (Real.rpow_le_rpow (powCap_pos hε hN s).le (powCap_le_cap (not_le.1 hp) s) he0).trans
        (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_nonpos hε (le_powCap hN s) (not_le.1 he0).le).trans
        (le_max_left _ _)

theorem exists_powF2_bound (hp : 1 < p) (hε : 0 < ε) (hN : 0 ≤ N) :
    ∃ C : NNReal, ∀ s, |deriv (deriv (powF p ε N)) s| ≤ C := by
  refine ⟨(p * (p - 1) * max (ε ^ (p - 2)) ((N + ε) ^ (p - 2))).toNNReal, fun s => ?_⟩
  rw [deriv_deriv_powF hε hN, abs_of_nonneg (powF2_nonneg hp hε hN s)]
  refine le_trans ?_ (Real.le_coe_toNNReal _)
  unfold powF2
  have : 0 ≤ p * (p - 1) := by nlinarith
  exact mul_le_mul_of_nonneg_left (powCap_rpow_le hε hN (fun h => by linarith) s) this

theorem exists_powG1_bound (hp : 1 < p) (hε : 0 < ε) (hN : 0 ≤ N) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s, |deriv (powG p ε N) s| ≤ M := by
  refine ⟨p / 2 * max (ε ^ (p / 2 - 1)) ((N + ε) ^ (p / 2 - 1)), ?_, fun s => ?_⟩
  · have : 0 ≤ ε ^ (p / 2 - 1) := Real.rpow_nonneg hε.le _
    have : 0 ≤ p / 2 := by linarith
    positivity
  rw [deriv_powG hε hN, abs_of_nonneg (powG1_nonneg hp hε hN s)]
  unfold powG1
  exact mul_le_mul_of_nonneg_left (powCap_rpow_le hε hN (fun h => by linarith) s) (by linarith)

end Bounds

section ClosedForms

/-- `∫₀ˢ q (r+ε)^{q-1} dr = (s+ε)^q - ε^q`. -/
theorem integral_shift_rpow (hε : 0 < ε) {s : ℝ} (hs : 0 ≤ s) (q : ℝ) :
    ∫ r in (0 : ℝ)..s, q * (r + ε) ^ (q - 1) = (s + ε) ^ q - ε ^ q := by
  have hderiv : ∀ r ∈ uIcc (0 : ℝ) s,
      HasDerivAt (fun r => (r + ε) ^ q) (q * (r + ε) ^ (q - 1)) r := by
    intro r hr
    rw [uIcc_of_le hs] at hr
    have hpos : 0 < r + ε := by linarith [hr.1]
    simpa using ((hasDerivAt_id r).add_const ε).rpow_const (p := q) (Or.inl hpos.ne')
  have hcont : ContinuousOn (fun r => q * (r + ε) ^ (q - 1)) (uIcc 0 s) := by
    intro r hr
    rw [uIcc_of_le hs] at hr
    have hpos : 0 < r + ε := by linarith [hr.1]
    exact (continuousAt_const.mul ((continuousAt_id.add continuousAt_const).rpow_const
      (Or.inl hpos.ne'))).continuousWithinAt
  rw [integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp

theorem powF1_eq_of_le (hε : 0 < ε) {s : ℝ} (hs : 0 ≤ s) (h : p ≤ 2 ∨ s ≤ N) :
    powF1 p ε N s = p * (s + ε) ^ (p - 1) := by
  unfold powF1
  have hcongr : ∫ r in (0 : ℝ)..s, powF2 p ε N r =
      ∫ r in (0 : ℝ)..s, p * ((p - 1) * (r + ε) ^ (p - 1 - 1)) := by
    refine integral_congr fun r hr => ?_
    rw [uIcc_of_le hs] at hr
    have hcap := powCap_eq_of_le (p := p) (ε := ε) (N := N) hr.1
      (h.imp id fun h => hr.2.trans h)
    simp only [powF2, hcap]
    rw [show p - 1 - 1 = p - 2 by ring]
    ring
  rw [hcongr, intervalIntegral.integral_const_mul, integral_shift_rpow hε hs]
  ring

theorem powF_eq_of_le (hε : 0 < ε) {s : ℝ} (hs : 0 ≤ s) (h : p ≤ 2 ∨ s ≤ N) :
    powF p ε N s = (s + ε) ^ p := by
  unfold powF
  have hcongr : ∫ r in (0 : ℝ)..s, powF1 p ε N r = ∫ r in (0 : ℝ)..s, p * (r + ε) ^ (p - 1) := by
    refine integral_congr fun r hr => ?_
    rw [uIcc_of_le hs] at hr
    exact powF1_eq_of_le hε hr.1 (h.imp id fun h => hr.2.trans h)
  rw [hcongr, integral_shift_rpow hε hs]
  ring

theorem powG_eq_of_le (hε : 0 < ε) {s : ℝ} (hs : 0 ≤ s) (h : p ≤ 2 ∨ s ≤ N) :
    powG p ε N s = (s + ε) ^ (p / 2) := by
  unfold powG
  have hcongr : ∫ r in (0 : ℝ)..s, powG1 p ε N r =
      ∫ r in (0 : ℝ)..s, p / 2 * (r + ε) ^ (p / 2 - 1) := by
    refine integral_congr fun r hr => ?_
    rw [uIcc_of_le hs] at hr
    have hcap := powCap_eq_of_le (p := p) (ε := ε) (N := N) hr.1
      (h.imp id fun h => hr.2.trans h)
    simp only [powG1, hcap]
  rw [hcongr, integral_shift_rpow hε hs]
  ring

/-- Beyond the cap (`p > 2`, `s ≥ N`), `F'` is affine. -/
theorem powF1_eq_of_ge (hp : 2 < p) (hε : 0 < ε) (hN : 0 ≤ N) {s : ℝ} (hs : N ≤ s) :
    powF1 p ε N s = p * (N + ε) ^ (p - 1) + p * (p - 1) * (N + ε) ^ (p - 2) * (s - N) := by
  have hN' : powF1 p ε N N = p * (N + ε) ^ (p - 1) := powF1_eq_of_le hε hN (Or.inr le_rfl)
  have hint := powF2_continuous (p := p) hε hN
  have hsplit : powF1 p ε N s - powF1 p ε N N = ∫ r in N..s, powF2 p ε N r := by
    unfold powF1
    rw [add_sub_add_left_eq_sub,
      integral_interval_sub_left (hint.intervalIntegrable _ _) (hint.intervalIntegrable _ _)]
  have hconst : ∫ r in N..s, powF2 p ε N r =
      ∫ _r in N..s, p * (p - 1) * (N + ε) ^ (p - 2) := by
    refine integral_congr fun r hr => ?_
    rw [uIcc_of_le hs] at hr
    simp only [powF2, powCap_eq_cap hp hr.1 hN]
  rw [hconst, intervalIntegral.integral_const, smul_eq_mul] at hsplit
  linarith

/-- Beyond the cap (`p > 2`, `s ≥ N`), `F` is quadratic. -/
theorem powF_eq_of_ge (hp : 2 < p) (hε : 0 < ε) (hN : 0 ≤ N) {s : ℝ} (hs : N ≤ s) :
    powF p ε N s = (N + ε) ^ p + p * (N + ε) ^ (p - 1) * (s - N) +
      p * (p - 1) * (N + ε) ^ (p - 2) * (s - N) ^ 2 / 2 := by
  have hN' : powF p ε N N = (N + ε) ^ p := powF_eq_of_le hε hN (Or.inr le_rfl)
  have hint := powF1_continuous (p := p) hε hN
  have hsplit : powF p ε N s - powF p ε N N = ∫ r in N..s, powF1 p ε N r := by
    unfold powF
    rw [add_sub_add_left_eq_sub,
      integral_interval_sub_left (hint.intervalIntegrable _ _) (hint.intervalIntegrable _ _)]
  set a := p * (N + ε) ^ (p - 1)
  set c := p * (p - 1) * (N + ε) ^ (p - 2)
  have hcongr : ∫ r in N..s, powF1 p ε N r = ∫ r in N..s, (a + c * (r - N)) := by
    refine integral_congr fun r hr => ?_
    rw [uIcc_of_le hs] at hr
    exact powF1_eq_of_ge hp hε hN hr.1
  have hderiv : ∀ r ∈ uIcc N s,
      HasDerivAt (fun r => a * (r - N) + c * (r - N) ^ 2 / 2) (a + c * (r - N)) r := by
    intro r _
    have h1 : HasDerivAt (fun r => a * (r - N)) a r :=
      (((hasDerivAt_id' r).sub_const N).const_mul a).congr_deriv (by ring)
    have h2 : HasDerivAt (fun r => c * (r - N) ^ 2 / 2) (c * (r - N)) r :=
      ((((hasDerivAt_id' r).sub_const N).pow 2).const_mul c |>.div_const 2).congr_deriv
        (by simp; ring)
    exact h1.add h2
  have hval : ∫ r in N..s, (a + c * (r - N)) = a * (s - N) + c * (s - N) ^ 2 / 2 := by
    rw [integral_eq_sub_of_hasDerivAt hderiv ((by fun_prop : Continuous fun r =>
      a + c * (r - N)).intervalIntegrable N s)]
    ring
  rw [hcongr, hval] at hsplit
  linarith

/-- Beyond the cap (`p > 2`, `s ≥ N`), `G` is affine. -/
theorem powG_eq_of_ge (hp : 2 < p) (hε : 0 < ε) (hN : 0 ≤ N) {s : ℝ} (hs : N ≤ s) :
    powG p ε N s = (N + ε) ^ (p / 2) + p / 2 * (N + ε) ^ (p / 2 - 1) * (s - N) := by
  have hN' : powG p ε N N = (N + ε) ^ (p / 2) := powG_eq_of_le hε hN (Or.inr le_rfl)
  have hint := powG1_continuous (p := p) hε hN
  have hsplit : powG p ε N s - powG p ε N N = ∫ r in N..s, powG1 p ε N r := by
    unfold powG
    rw [add_sub_add_left_eq_sub,
      integral_interval_sub_left (hint.intervalIntegrable _ _) (hint.intervalIntegrable _ _)]
  have hconst : ∫ r in N..s, powG1 p ε N r = ∫ _r in N..s, p / 2 * (N + ε) ^ (p / 2 - 1) := by
    refine integral_congr fun r hr => ?_
    rw [uIcc_of_le hs] at hr
    simp only [powG1, powCap_eq_cap hp hr.1 hN]
  rw [hconst, intervalIntegral.integral_const, smul_eq_mul] at hsplit
  linarith

/-- `F'(r) ≤ p (r+ε)^{p-1}` for `r ≥ 0` (the cap only lowers `F''`). -/
theorem powF1_le (hp : 1 < p) (hε : 0 < ε) (hN : 0 ≤ N) {s : ℝ} (hs : 0 ≤ s) :
    powF1 p ε N s ≤ p * (s + ε) ^ (p - 1) := by
  by_cases hp2 : p ≤ 2
  · exact (powF1_eq_of_le hε hs (Or.inl hp2)).le
  have hle : ∫ r in (0 : ℝ)..s, powF2 p ε N r ≤
      ∫ r in (0 : ℝ)..s, p * ((p - 1) * (r + ε) ^ (p - 1 - 1)) := by
    refine integral_mono_on hs ((powF2_continuous hε hN).intervalIntegrable _ _) ?_ ?_
    · refine ContinuousOn.intervalIntegrable fun r hr => ?_
      rw [uIcc_of_le hs] at hr
      have hpos : 0 < r + ε := by linarith [hr.1]
      exact (continuousAt_const.mul (continuousAt_const.mul
        ((continuousAt_id.add continuousAt_const).rpow_const
          (Or.inl hpos.ne')))).continuousWithinAt
    · intro r hr
      rw [show p - 1 - 1 = p - 2 by ring]
      have hcap := powCap_le_self (p := p) (ε := ε) (N := N) hr.1
      have hpow := Real.rpow_le_rpow (powCap_pos hε hN r).le hcap (by linarith : (0 : ℝ) ≤ p - 2)
      unfold powF2
      have : 0 ≤ p * (p - 1) := by nlinarith
      calc p * (p - 1) * powCap p ε N r ^ (p - 2) ≤ p * (p - 1) * (r + ε) ^ (p - 2) :=
            mul_le_mul_of_nonneg_left hpow this
        _ = p * ((p - 1) * (r + ε) ^ (p - 2)) := by ring
  rw [intervalIntegral.integral_const_mul, integral_shift_rpow hε hs] at hle
  unfold powF1
  linarith

theorem powF_le (hp : 1 < p) (hε : 0 < ε) (hN : 0 ≤ N) {s : ℝ} (hs : 0 ≤ s) :
    powF p ε N s ≤ (s + ε) ^ p := by
  have hle : ∫ r in (0 : ℝ)..s, powF1 p ε N r ≤ ∫ r in (0 : ℝ)..s, p * (r + ε) ^ (p - 1) := by
    refine integral_mono_on hs ((powF1_continuous hε hN).intervalIntegrable _ _) ?_ ?_
    · refine ContinuousOn.intervalIntegrable fun r hr => ?_
      rw [uIcc_of_le hs] at hr
      have hpos : 0 < r + ε := by linarith [hr.1]
      exact (continuousAt_const.mul ((continuousAt_id.add continuousAt_const).rpow_const
        (Or.inl hpos.ne'))).continuousWithinAt
    · intro r hr
      exact powF1_le hp hε hN hr.1
  rw [integral_shift_rpow hε hs] at hle
  unfold powF
  linarith

theorem powF1_nonneg (hp : 1 < p) (hε : 0 < ε) (hN : 0 ≤ N) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ powF1 p ε N s := by
  unfold powF1
  have h1 : 0 ≤ ∫ r in (0 : ℝ)..s, powF2 p ε N r :=
    integral_nonneg hs fun r _ => powF2_nonneg hp hε hN r
  have h2 : 0 ≤ p * ε ^ (p - 1) := mul_nonneg (by linarith) (Real.rpow_nonneg hε.le _)
  linarith

theorem powF_nonneg (hp : 1 < p) (hε : 0 < ε) (hN : 0 ≤ N) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ powF p ε N s := by
  unfold powF
  have h1 : 0 ≤ ∫ r in (0 : ℝ)..s, powF1 p ε N r :=
    integral_nonneg hs fun r hr => powF1_nonneg hp hε hN hr.1
  have h2 : 0 ≤ ε ^ p := Real.rpow_nonneg hε.le _
  linarith

theorem powG_nonneg (hp : 1 < p) (hε : 0 < ε) (hN : 0 ≤ N) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ powG p ε N s := by
  unfold powG
  have h1 : 0 ≤ ∫ r in (0 : ℝ)..s, powG1 p ε N r :=
    integral_nonneg hs fun r _ => powG1_nonneg hp hε hN r
  have h2 : 0 ≤ ε ^ (p / 2) := Real.rpow_nonneg hε.le _
  linarith

end ClosedForms

end

end PDE.Parabolic.LocalMax
