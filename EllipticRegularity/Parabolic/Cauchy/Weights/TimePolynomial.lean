module

public import EllipticRegularity.Parabolic.Cauchy.Weights.SmoothGaussian
public import PDEFoundation.Sobolev.W1p.Truncation
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# A bounded smooth time power on a fixed interval

The Nash weighted-energy argument multiplies its Gaussian weight by
`(t - s + σ)^((d+2)/4)`. This module extends that factor smoothly and
positively outside the energy interval, with bounded value and derivative, so
it remains admissible for the whole-space weighted identity.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Weights

variable {d : ℕ}

/-- Cap the positive shifted time smoothly after an interval of length `H`.
On `[0,H]` this is exactly `x + σ`; on the whole line it stays positive and
bounded. -/
noncomputable def nashCappedTimeShift (H σ x : ℝ) : ℝ :=
  nashPositiveTimeShift σ x - PDE.smoothPositivePartApprox H (σ / 8) x

theorem nashCappedTimeShift_bounds {H σ x : ℝ} (hH : 0 < H) (hσ : 0 < σ) :
    σ / 2 ≤ nashCappedTimeShift H σ x ∧
      nashCappedTimeShift H σ x ≤ H + 2 * σ := by
  let F : ℝ → ℝ := PDE.smoothPositivePartApprox (-σ / 4) (σ / 8)
  let G : ℝ → ℝ := PDE.smoothPositivePartApprox H (σ / 8)
  have hδ : 0 < σ / 8 := by positivity
  have hF0 : 0 ≤ F 0 := by
    dsimp [F]
    exact PDE.smoothPositivePartApprox_nonneg hδ 0
  have hFapprox : |F x - max (x + σ / 4) 0| ≤ σ / 4 := by
    have h := PDE.abs_smoothPositivePartApprox_sub_le (c := -σ / 4) hδ x
    have harg : x - (-σ / 4) = x + σ / 4 := by ring
    rw [harg] at h
    have hbound : 2 * (σ / 8) = σ / 4 := by ring
    rw [hbound] at h
    simpa [F] using h
  have hGapprox : |G x - max (x - H) 0| ≤ σ / 4 := by
    have h := PDE.abs_smoothPositivePartApprox_sub_le (c := H) hδ x
    have hbound : 2 * (σ / 8) = σ / 4 := by ring
    rw [hbound] at h
    simpa [G] using h
  by_cases hx : x ≤ H
  · have hGzero : G x = 0 := by
      dsimp [G]
      exact PDE.smoothPositivePartApprox_eq_zero_of_le hδ hx
    have hshiftlower := nashPositiveTimeShift_lower (σ := σ) (t := x) hσ
    have hmax : max (x + σ / 4) 0 ≤ H + σ / 4 := by
      rw [max_le_iff]
      constructor <;> linarith
    have hFupper : F x ≤ H + σ / 2 := by
      have habs := abs_le.mp hFapprox
      linarith
    constructor
    · dsimp [nashCappedTimeShift, G]
      change σ / 2 ≤ nashPositiveTimeShift σ x - G x
      simpa [hGzero] using hshiftlower
    · have hshiftupper : nashPositiveTimeShift σ x ≤ H + 2 * σ := by
        dsimp [nashPositiveTimeShift, F]
        dsimp [F] at hFupper hF0
        linarith
      change nashPositiveTimeShift σ x - G x ≤ H + 2 * σ
      simpa [hGzero] using hshiftupper
  · have hx' : H < x := lt_of_not_ge hx
    have hshift : nashPositiveTimeShift σ x = x + σ := by
      exact nashPositiveTimeShift_eq_add hσ (le_trans hH.le hx'.le)
    have hmax : max (x - H) 0 = x - H := max_eq_left (sub_nonneg.mpr hx'.le)
    have hGerr := abs_le.mp (by simpa [hmax] using hGapprox)
    constructor
    · dsimp [nashCappedTimeShift]
      rw [hshift]
      have hGupper : G x ≤ x - H + σ / 4 := by linarith [hGerr.2]
      linarith
    · dsimp [nashCappedTimeShift]
      rw [hshift]
      have hGlower : x - H - σ / 4 ≤ G x := by linarith [hGerr.1]
      linarith

theorem nashCappedTimeShift_eq_shift {H σ x : ℝ} (_hH : 0 < H) (hσ : 0 < σ)
    (_hx0 : 0 ≤ x) (hxH : x ≤ H) :
    nashCappedTimeShift H σ x = nashPositiveTimeShift σ x := by
  rw [nashCappedTimeShift,
    PDE.smoothPositivePartApprox_eq_zero_of_le (by positivity) hxH, sub_zero]

theorem hasDerivAt_nashCappedTimeShift {H σ x : ℝ} :
    HasDerivAt (nashCappedTimeShift H σ)
      (PDE.smoothPositivePartStep (-σ / 4) (σ / 8) x -
        PDE.smoothPositivePartStep H (σ / 8) x) x := by
  unfold nashCappedTimeShift
  exact nashPositiveTimeShift_hasDerivAt.sub
    (PDE.smoothPositivePartApprox_hasDerivAt H (σ / 8) x)

theorem deriv_nashCappedTimeShift_abs_le_one {H σ x : ℝ} :
    |deriv (nashCappedTimeShift H σ) x| ≤ 1 := by
  rw [(hasDerivAt_nashCappedTimeShift (H := H) (σ := σ) (x := x)).deriv]
  have h₁lo := PDE.smoothPositivePartStep_nonneg (-σ / 4) (σ / 8) x
  have h₁hi := PDE.smoothPositivePartStep_le_one (-σ / 4) (σ / 8) x
  have h₂lo := PDE.smoothPositivePartStep_nonneg H (σ / 8) x
  have h₂hi := PDE.smoothPositivePartStep_le_one H (σ / 8) x
  rw [abs_le]
  constructor <;> linarith

theorem deriv_nashCappedTimeShift_eq_one {H σ x : ℝ} (hσ : 0 < σ)
    (hx0 : 0 ≤ x) (hxH : x ≤ H) :
    deriv (nashCappedTimeShift H σ) x = 1 := by
  rw [(hasDerivAt_nashCappedTimeShift (H := H) (σ := σ) (x := x)).deriv]
  have hfirst : PDE.smoothPositivePartStep (-σ / 4) (σ / 8) x = 1 := by
    apply PDE.smoothPositivePartStep_eq_one
    · positivity
    · linarith
  have hsecond : PDE.smoothPositivePartStep H (σ / 8) x = 0 := by
    apply PDE.smoothPositivePartStep_eq_zero
    · positivity
    · linarith
  rw [hfirst, hsecond]
  norm_num

/-- The smooth bounded substitute for `(x + σ)^((d+2)/4)` on `[0,H]`. -/
noncomputable def nashPolynomialTimeFactor (H σ : ℝ) (x : ℝ) : ℝ :=
  nashCappedTimeShift H σ x ^ (((d : ℝ) + 2) / 4)

theorem nashPolynomialTimeFactor_contDiff_one {H σ : ℝ}
    (hH : 0 < H) (hσ : 0 < σ) :
    ContDiff ℝ 1 (nashPolynomialTimeFactor (d := d) H σ) := by
  have hcap : ContDiff ℝ 1 (nashCappedTimeShift H σ) := by
    unfold nashCappedTimeShift
    exact nashPositiveTimeShift_contDiff_one.sub
      (PDE.smoothPositivePartApprox_contDiff_one H (σ / 8))
  have hne : ∀ x, nashCappedTimeShift H σ x ≠ 0 := by
    intro x
    exact ne_of_gt (lt_of_lt_of_le (by positivity)
      (nashCappedTimeShift_bounds (H := H) (σ := σ) (x := x) hH hσ).1)
  change ContDiff ℝ 1 (fun x => nashCappedTimeShift H σ x ^ (((d : ℝ) + 2) / 4))
  exact hcap.rpow_const_of_ne hne

theorem nashPolynomialTimeFactor_bounds {H σ x : ℝ} (hH : 0 < H) (hσ : 0 < σ) :
    0 < nashPolynomialTimeFactor (d := d) H σ x ∧
      nashPolynomialTimeFactor (d := d) H σ x ≤
        (H + 2 * σ) ^ (((d : ℝ) + 2) / 4) := by
  have hcap := nashCappedTimeShift_bounds (H := H) (σ := σ) (x := x) hH hσ
  have hα : 0 < (((d : ℝ) + 2) / 4) := by positivity
  constructor
  · unfold nashPolynomialTimeFactor
    exact Real.rpow_pos_of_pos (lt_of_lt_of_le (by positivity) hcap.1) _
  · unfold nashPolynomialTimeFactor
    exact Real.rpow_le_rpow (le_of_lt (lt_of_lt_of_le (by positivity) hcap.1))
      hcap.2 hα.le

theorem nashPolynomialTimeFactor_deriv_bound {H σ x : ℝ}
    (hH : 0 < H) (hσ : 0 < σ) :
    |deriv (nashPolynomialTimeFactor (d := d) H σ) x| ≤
      (((d : ℝ) + 2) / 4) *
        ((σ / 2) ^ ((((d : ℝ) + 2) / 4) - 1) +
          (H + 2 * σ) ^ ((((d : ℝ) + 2) / 4) - 1)) := by
  let α : ℝ := ((d : ℝ) + 2) / 4
  let L : ℝ := σ / 2
  let U : ℝ := H + 2 * σ
  have hα : 0 < α := by dsimp [α]; positivity
  have hcap := nashCappedTimeShift_bounds (H := H) (σ := σ) (x := x) hH hσ
  have hL : 0 < L := by dsimp [L]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  have hcapPos : 0 < nashCappedTimeShift H σ x := lt_of_lt_of_le hL hcap.1
  have hcapDeriv := hasDerivAt_nashCappedTimeShift (H := H) (σ := σ) (x := x)
  have hpower := hcapDeriv.rpow_const (p := α) (Or.inl hcapPos.ne')
  have hcapDerivEq := hcapDeriv.deriv
  have hformula : deriv (nashPolynomialTimeFactor (d := d) H σ) x =
      deriv (nashCappedTimeShift H σ) x * α *
        nashCappedTimeShift H σ x ^ (α - 1) := by
    change deriv (fun y : ℝ => nashCappedTimeShift H σ y ^ α) x = _
    rw [hcapDerivEq]
    exact hpower.deriv
  have hpbound : nashCappedTimeShift H σ x ^ (α - 1) ≤ L ^ (α - 1) + U ^ (α - 1) := by
    by_cases hpow : 0 ≤ α - 1
    · have hu := Real.rpow_le_rpow (le_of_lt hcapPos) hcap.2 hpow
      exact hu.trans (le_add_of_nonneg_left (Real.rpow_nonneg (le_of_lt hL) _))
    · have hpow' : α - 1 ≤ 0 := le_of_not_ge hpow
      have hl := Real.rpow_le_rpow_of_nonpos hL hcap.1 hpow'
      exact hl.trans (le_add_of_nonneg_right (Real.rpow_nonneg (le_of_lt hU) _))
  have hderivCap : |deriv (nashCappedTimeShift H σ) x| ≤ 1 :=
    deriv_nashCappedTimeShift_abs_le_one
  have hpowNonneg : 0 ≤ nashCappedTimeShift H σ x ^ (α - 1) :=
    Real.rpow_nonneg hcapPos.le _
  have hαnonneg : 0 ≤ α := hα.le
  rw [hformula, abs_mul, abs_mul,
    abs_of_nonneg hαnonneg, abs_of_nonneg hpowNonneg]
  calc
    |deriv (nashCappedTimeShift H σ) x| * α *
        nashCappedTimeShift H σ x ^ (α - 1) ≤
      1 * α * (L ^ (α - 1) + U ^ (α - 1)) := by
        gcongr
    _ = α * (L ^ (α - 1) + U ^ (α - 1)) := by ring

theorem nashPolynomialTimeFactor_eq_rpow {H σ x : ℝ} (hH : 0 < H)
    (hσ : 0 < σ) (hx0 : 0 ≤ x) (hxH : x ≤ H) :
    nashPolynomialTimeFactor (d := d) H σ x =
      nashPositiveTimeShift σ x ^ (((d : ℝ) + 2) / 4) := by
  simp [nashPolynomialTimeFactor, nashCappedTimeShift_eq_shift hH hσ hx0 hxH]

theorem deriv_nashPolynomialTimeFactor_eq_rpow {H σ x : ℝ} (hH : 0 < H)
    (hσ : 0 < σ) (hx0 : 0 ≤ x) (hxH : x ≤ H) :
    deriv (nashPolynomialTimeFactor (d := d) H σ) x =
      (((d : ℝ) + 2) / 4) *
        nashPositiveTimeShift σ x ^ ((((d : ℝ) + 2) / 4) - 1) := by
  have hcapEq := nashCappedTimeShift_eq_shift hH hσ hx0 hxH
  have hcapD := deriv_nashCappedTimeShift_eq_one hσ hx0 hxH
  have hcapPos : 0 < nashCappedTimeShift H σ x :=
    lt_of_lt_of_le (by positivity)
      (nashCappedTimeShift_bounds (H := H) (σ := σ) (x := x) hH hσ).1
  have hcapBase := hasDerivAt_nashCappedTimeShift (H := H) (σ := σ) (x := x)
  have hpower := hcapBase.rpow_const
    (p := (((d : ℝ) + 2) / 4)) (Or.inl hcapPos.ne')
  have hfirst : PDE.smoothPositivePartStep (-σ / 4) (σ / 8) x = 1 := by
    apply PDE.smoothPositivePartStep_eq_one
    · positivity
    · linarith
  have hsecond : PDE.smoothPositivePartStep H (σ / 8) x = 0 := by
    apply PDE.smoothPositivePartStep_eq_zero
    · positivity
    · linarith
  change deriv (fun y : ℝ => nashCappedTimeShift H σ y ^ (((d : ℝ) + 2) / 4)) x = _
  rw [hpower.deriv, hcapEq, hfirst, hsecond]
  ring

end PDE.Parabolic.Cauchy.Weights
