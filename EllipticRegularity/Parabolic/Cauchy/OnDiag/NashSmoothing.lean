module

public import EllipticRegularity.Parabolic.Cauchy.Weights.DiagonalDecay
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Nash smoothing from an almost everywhere energy inequality

The energy of a weak Cauchy solution is only absolutely continuous in time.
This scalar lemma uses that regularity directly, so it does not impose pointwise
time differentiability on the solution.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.OnDiag

open MeasureTheory Set

/-- Nash's differential inequality gives the usual `L¹` to `L²` smoothing
bound when the energy is absolutely continuous and its differential
inequality holds almost everywhere. -/
theorem nashDiagonalDecay_of_ae_deriv {d : ℕ} (hd : 0 < d) {s T c B : ℝ}
    (hST : s < T) (hc : 0 < c) (hB : 0 < B) (E : ℝ → ℝ)
    (hEac : AbsolutelyContinuousOnInterval E s T)
    (hEnonneg : ∀ t ∈ Icc s T, 0 ≤ E t)
    (hderiv : ∀ᵐ t ∂volume, t ∈ Ioo s T → HasDerivAt E (deriv E t) t)
    (hdiss : ∀ᵐ t ∂volume, t ∈ Ioo s T →
      deriv E t ≤ -c * E t ^ (1 + (2 : ℝ) / d) * B ^ (-(4 : ℝ) / d)) :
    E T ≤ ((d : ℝ) / (2 * c * (T - s))) ^ ((d : ℝ) / 2) * B ^ 2 := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hBexp : 0 < B ^ (-(4 : ℝ) / d) := Real.rpow_pos_of_pos hB _
  have hderiv_nonpos : ∀ᵐ t ∂volume, t ∈ Ioo s T → deriv E t ≤ 0 := by
    filter_upwards [hdiss] with t ht
    intro hinterval
    have hpow : 0 ≤ E t ^ (1 + (2 : ℝ) / d) :=
      Real.rpow_nonneg (hEnonneg t ⟨le_of_lt hinterval.1, le_of_lt hinterval.2⟩) _
    have hprod := mul_nonneg hpow hBexp.le
    nlinarith [ht hinterval]
  have hanti : AntitoneOn E (Icc s T) := by
    intro x hx y hy hxy
    by_cases hxy' : x = y
    · simp [hxy']
    have hlt : x < y := lt_of_le_of_ne hxy hxy'
    have hsub : Icc x y ⊆ Icc s T := by
      intro z hz
      exact ⟨le_trans hx.1 hz.1, le_trans hz.2 hy.2⟩
    have hsub' : uIcc x y ⊆ uIcc s T := by
      rw [uIcc_of_le hxy, uIcc_of_le hST.le]
      exact hsub
    have hac := hEac.mono hsub'
    have hleInt : (∫ z in x..y, deriv E z) ≤ 0 := by
      let μ : Measure ℝ := volume.restrict (Icc x y)
      have hneg : 0 ≤ᵐ[μ] fun z : ℝ => -deriv E z := by
        filter_upwards [ae_restrict_of_ae hderiv_nonpos,
          ae_restrict_mem measurableSet_Icc, μ.ae_ne x, μ.ae_ne y]
          with z hz hzxy hxz hzy
        have hxz' : x < z := lt_of_le_of_ne hzxy.1 (Ne.symm hxz)
        have hzy' : z < y := lt_of_le_of_ne hzxy.2 hzy
        have hzI : z ∈ Ioo s T :=
          ⟨lt_of_le_of_lt hx.1 hxz', lt_of_lt_of_le hzy' hy.2⟩
        exact neg_nonneg.mpr (hz hzI)
      have hnonneg := intervalIntegral.integral_nonneg_of_ae_restrict hxy hneg
      simpa using hnonneg
    have hftc := hac.integral_deriv_eq_sub
    rw [hftc] at hleInt
    exact sub_nonpos.mp hleInt
  have hEt : 0 ≤ E T := hEnonneg T ⟨le_of_lt hST, le_rfl⟩
  by_cases hEt0 : E T = 0
  · rw [hEt0]
    positivity
  have hEtpos : 0 < E T := lt_of_le_of_ne hEt (Ne.symm hEt0)
  let q : ℝ := -(2 : ℝ) / d
  let F : ℝ → ℝ := fun t => E t ^ q
  have hEpositive : ∀ x ∈ Icc s T, 0 < E x := by
    intro x hx
    have hEtEx : E T ≤ E x := hanti hx ⟨le_of_lt hST, le_rfl⟩ hx.2
    exact lt_of_lt_of_le hEtpos hEtEx
  have hqneg : q < 0 := by
    dsimp [q]
    exact div_neg_of_neg_of_pos (by norm_num) hdR
  have hqne : q ≠ 0 := ne_of_lt hqneg
  have hpowCont : ContDiffOn ℝ 1 (fun r : ℝ => r ^ q) (Icc (E T) (E s)) := by
    intro r hr
    have hrne : r ≠ 0 := ne_of_gt (lt_of_lt_of_le hEtpos hr.1)
    exact (Real.contDiffAt_rpow_const_of_ne hrne).contDiffWithinAt
  obtain ⟨K, hLip⟩ := hpowCont.exists_lipschitzOnWith one_ne_zero
    (convex_Icc _ _) isCompact_Icc
  have hMaps : MapsTo E (uIcc s T) (Icc (E T) (E s)) := by
    intro x hx
    rw [uIcc_of_le hST.le] at hx
    exact ⟨hanti hx ⟨le_of_lt hST, le_rfl⟩ hx.2,
      hanti ⟨le_rfl, hST.le⟩ hx hx.1⟩
  have hFac : AbsolutelyContinuousOnInterval F s T := by
    change AbsolutelyContinuousOnInterval ((fun r : ℝ => r ^ q) ∘ E) s T
    exact hLip.comp_absolutelyContinuousOnInterval hMaps hEac
  have hFderivLower (x : ℝ) (hx : x ∈ Ioo s T)
      (hDx : HasDerivAt E (deriv E x) x)
      (hDiss : deriv E x ≤
        -c * E x ^ (1 + (2 : ℝ) / d) * B ^ (-(4 : ℝ) / d)) :
      (2 * c / d) * B ^ (-(4 : ℝ) / d) ≤ deriv F x := by
    have hEx : 0 < E x := hEpositive x ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have hformula : deriv F x = deriv E x * q * E x ^ (q - 1) := by
      have hcomp := hDx.rpow_const (p := q) (Or.inl hEx.ne')
      simpa [F, q] using hcomp.deriv
    have hexp : E x ^ (1 + (2 : ℝ) / d) * E x ^ (q - 1) = 1 := by
      rw [← Real.rpow_add hEx]
      have hs : (1 : ℝ) + 2 / d + (-(2 : ℝ) / d - 1) = 0 := by ring
      rw [show q = -(2 : ℝ) / d by rfl, hs, Real.rpow_zero]
    have hfactor : q * E x ^ (q - 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hqneg.le (Real.rpow_nonneg hEx.le _)
    have hmul := mul_le_mul_of_nonpos_left hDiss hfactor
    have hleft : q * E x ^ (q - 1) *
        (-c * E x ^ (1 + (2 : ℝ) / d) * B ^ (-(4 : ℝ) / d)) =
        (2 * c / d) * B ^ (-(4 : ℝ) / d) := by
      rw [show q = -(2 : ℝ) / d by rfl]
      calc
        _ = (q * (-c)) *
            (E x ^ (q - 1) * E x ^ (1 + (2 : ℝ) / d)) *
              B ^ (-(4 : ℝ) / d) := by ring
        _ = _ := by rw [mul_comm (E x ^ (q - 1)), hexp]; dsimp [q]; ring
    calc
      (2 * c / d) * B ^ (-(4 : ℝ) / d) =
          q * E x ^ (q - 1) *
            (-c * E x ^ (1 + (2 : ℝ) / d) * B ^ (-(4 : ℝ) / d)) := hleft.symm
      _ ≤ q * E x ^ (q - 1) * deriv E x := by
        nlinarith [hmul]
      _ = deriv F x := by rw [hformula]; ring
  have hFderivLowerAE : ∀ᵐ x ∂volume, x ∈ Ioo s T →
      (2 * c / d) * B ^ (-(4 : ℝ) / d) ≤ deriv F x := by
    filter_upwards [hderiv, hdiss] with x hx hd
    intro hxI
    exact hFderivLower x hxI (hx hxI) (hd hxI)
  have hFderivRestr : (fun _ : ℝ => (2 * c / d) * B ^ (-(4 : ℝ) / d)) ≤ᵐ[
      volume.restrict (Icc s T)] fun x => deriv F x := by
    filter_upwards [ae_restrict_of_ae hFderivLowerAE,
      ae_restrict_mem measurableSet_Icc,
      (volume.restrict (Icc s T)).ae_ne s,
      (volume.restrict (Icc s T)).ae_ne T] with x hbound hx hx0 hxT
    have hxI : x ∈ Ioo s T :=
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hxT⟩
    exact hbound hxI
  have hconstInt : IntervalIntegrable
      (fun _ : ℝ => (2 * c / d) * B ^ (-(4 : ℝ) / d)) volume s T :=
    intervalIntegrable_const
  have hderivInt := hFac.intervalIntegrable_deriv
  have hintLower := intervalIntegral.integral_mono_ae_restrict (le_of_lt hST)
    hconstInt hderivInt hFderivRestr
  have hftc := hFac.integral_deriv_eq_sub
  have hF0 : 0 ≤ F s := Real.rpow_nonneg (hEnonneg s ⟨le_rfl, hST.le⟩) _
  have hFbound : (2 * c / d) * B ^ (-(4 : ℝ) / d) * (T - s) ≤ F T := by
    have hconst : (∫ x in s..T,
        (2 * c / d) * B ^ (-(4 : ℝ) / d)) =
        (2 * c / d) * B ^ (-(4 : ℝ) / d) * (T - s) := by
      simp [intervalIntegral.integral_const]
      ring
    rw [hconst, hftc] at hintLower
    linarith
  have hduration : 0 < T - s := by linarith
  have htargetpos : 0 <
      ((d : ℝ) / (2 * c * (T - s))) ^ ((d : ℝ) / 2) * B ^ 2 := by positivity
  have htargetpow :=
    PDE.Parabolic.Cauchy.Weights.nashDiagonalBound_rpow hd hc hB hduration
  have htarget :
      (((d : ℝ) / (2 * c * (T - s))) ^ ((d : ℝ) / 2) * B ^ 2) ^ q ≤ F T := by
    calc
      _ = (2 * c / d) * B ^ (-(4 : ℝ) / d) * (T - s) := by simpa [q] using htargetpow
      _ ≤ F T := hFbound
  exact (Real.rpow_le_rpow_iff_of_neg htargetpos hEtpos hqneg).mp
    (by simpa [F, q] using htarget)

end PDE.Parabolic.Cauchy.OnDiag
