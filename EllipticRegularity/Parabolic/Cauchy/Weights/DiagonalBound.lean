module

public import EllipticRegularity.Parabolic.Cauchy.Energy.Global
public import EllipticRegularity.Parabolic.Cauchy.Energy.Exhaustion
public import EllipticRegularity.Parabolic.Cauchy.Energy.Density
public import EllipticRegularity.Parabolic.Cauchy.L1.Contraction
public import EllipticRegularity.Parabolic.Cauchy.Weights.DiagonalDecay
public import EllipticRegularity.Parabolic.Cauchy.Weights.NashDissipation
public import EllipticRegularity.Parabolic.Sobolev.ParabolicSlices
public import EllipticRegularity.Parabolic.WeakSlice.Product
public import PDEFoundation.Analysis.Inequalities.Nash.Main
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Nash diagonal decay for arbitrary Cauchy data

The L¹ contraction, the spatial Nash inequality, and the whole-space energy
identity imply the L¹-to-L² diagonal estimate.  This version permits signed
data and records an arbitrary positive upper bound for its L¹ norm.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Weights

open MeasureTheory Set Filter

/-- A fixed dimension-only constant in the whole-space Nash inequality. -/
noncomputable def nashInequalityConstant (d : ℕ) : ℝ :=
  if hd : 1 ≤ d then
    Classical.choose (PDE.Nash.exists_nash_constant_full d hd)
  else 1

theorem nashInequalityConstant_spec (d : ℕ) (hd : 0 < d) :
    0 < nashInequalityConstant d ∧
      ∀ u : H1Function (Set.univ : Set (Vec d)),
        Integrable u.toFun volume →
        ∫ x, u.toFun x ^ 2 ≤
          nashInequalityConstant d *
            (∫ x, vecEuclideanNorm (u.grad x) ^ 2) ^ ((d : ℝ) / (d + 2)) *
            (∫ x, |u.toFun x|) ^ ((4 : ℝ) / (d + 2)) := by
  have hd' : 1 ≤ d := by omega
  simpa [nashInequalityConstant, hd'] using
    (Classical.choose_spec (PDE.Nash.exists_nash_constant_full d hd'))

/-- The dimension-only coefficient in the Cauchy `L¹`-to-`L²` estimate. -/
noncomputable def nashDiagonalSmoothingConstant (d : ℕ) : ℝ :=
  ((d : ℝ) / (4 * nashInequalityConstant d ^ (-((d : ℝ) + 2) / d))) ^ ((d : ℝ) / 2)

theorem nashDiagonalSmoothingConstant_pos {d : ℕ} (hd : 0 < d) :
    0 < nashDiagonalSmoothingConstant d := by
  unfold nashDiagonalSmoothingConstant
  have hC := (nashInequalityConstant_spec d hd).1
  positivity

private noncomputable def diagonalEnergySlice {d : ℕ} {s T : ℝ}
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T)) (τ : ℝ) : ℝ :=
  ∫ x : Vec d, u.toFun (x, τ) ^ 2

private noncomputable def diagonalDissipationSlice {d : ℕ} {s T : ℝ}
    (a : ParCoeffField d) (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (τ : ℝ) : ℝ :=
  ∫ x : Vec d, PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u (x, τ)

private theorem diagonalEnergySlice_ac_deriv {d : ℕ} {lam Lam s T : ℝ}
    (hsT : s < T) (a : ParCoeffField d)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ)
    (hf : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) :
    AbsolutelyContinuousOnInterval (diagonalEnergySlice u) s T ∧
      ∀ᵐ τ ∂volume, τ ∈ Ioo s T →
        HasDerivAt (diagonalEnergySlice u)
          (-2 * diagonalDissipationSlice a u τ) τ := by
  let q : Vec d × ℝ → ℝ := PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u
  let D : ℝ → ℝ := fun τ => ∫ x in (univ : Set (Vec d)), q (x, τ)
  let E : ℝ → ℝ := diagonalEnergySlice u
  let P : ℝ → ℝ := fun τ => ∫ r in s..τ, D r
  let F : ℝ → ℝ := fun τ => E s - 2 * P τ
  have hqInt : IntegrableOn q ((univ : Set (Vec d)) ×ˢ Icc s T) :=
    PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity_integrable ha u
  have hqFub := PDE.Parabolic.WeakSlice.integral_prod_slices hqInt
  have hDInt : IntegrableOn D (Icc s T) := by simpa only [D] using hqFub.1
  have hDInterval : IntervalIntegrable D volume s T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hsT.le]
    exact hDInt
  have hDae := hDInterval.ae_hasDerivAt_integral
  have hPac : AbsolutelyContinuousOnInterval P s T := by
    dsimp [P]
    exact hDInterval.absolutelyContinuousOnInterval_intervalIntegral (by
      rw [uIcc_of_le hsT.le]
      exact ⟨le_rfl, hsT.le⟩)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => E s) s T := by
    exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => E s)).contDiffOn
      |> ContDiffOn.absolutelyContinuousOnInterval
  have hFac : AbsolutelyContinuousOnInterval F s T := by
    change AbsolutelyContinuousOnInterval
      ((fun _ : ℝ => E s) - (fun τ => 2 * P τ)) s T
    exact hconst.sub (hPac.const_mul 2)
  have hbulk (τ : ℝ) (hτ : τ ∈ Icc s T) :
      ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s τ, q z = ∫ r in Ioc s τ, D r := by
    have hsub : (univ : Set (Vec d)) ×ˢ Ioc s τ ⊆
        (univ : Set (Vec d)) ×ˢ Icc s T :=
      prod_mono subset_rfl fun r hr => ⟨hr.1.le, hr.2.trans hτ.2⟩
    have hFub := PDE.Parabolic.WeakSlice.integral_prod_slices (hqInt.mono_set hsub)
    simpa only [D, q, setIntegral_univ] using hFub.2
  have hIocEq (τ : ℝ) (hτ : τ ∈ Icc s T) :
      (∫ r in Ioc s τ, D r) = ∫ r in s..τ, D r :=
    (intervalIntegral.integral_of_le hτ.1).symm
  have hEF (τ : ℝ) (hτ : τ ∈ Icc s T) : E τ = F τ := by
    have hId := PDE.Parabolic.Cauchy.Energy.cauchy_energy_identity_real
      hsT ha f hf u hu hτ
    change (∫ x : Vec d, u.toFun (x, τ) ^ 2) +
      2 * ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s τ, q z =
      ∫ x : Vec d, f x ^ 2 at hId
    have hsId : E s = ∫ x : Vec d, f x ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hu.2] with x hx
      rw [hx]
    rw [hbulk τ hτ, hIocEq τ hτ, ← hsId] at hId
    change E τ + 2 * P τ = E s at hId
    change E τ = E s - 2 * P τ
    linarith [hId]
  have hEac : AbsolutelyContinuousOnInterval E s T := by
    apply hFac.congr
    intro τ hτ
    rw [uIcc_of_le hsT.le] at hτ
    exact (hEF τ hτ).symm
  have hderiv : ∀ᵐ τ ∂volume, τ ∈ Ioo s T → HasDerivAt E (-2 * D τ) τ := by
    filter_upwards [hDae] with τ hτ
    intro hτI
    have hτU : τ ∈ uIcc s T := by
      rw [uIcc_of_le hsT.le]
      exact ⟨hτI.1.le, hτI.2.le⟩
    have hP : HasDerivAt P (D τ) τ := by
      dsimp [P]
      exact hτ hτU s (by rw [uIcc_of_le hsT.le]; exact ⟨le_rfl, hsT.le⟩)
    have hF : HasDerivAt F (-2 * D τ) τ := by
      have hc : HasDerivAt (fun _ : ℝ => E s) 0 τ := hasDerivAt_const τ (E s)
      have hsub := hc.sub (hP.const_mul 2)
      change HasDerivAt ((fun _ : ℝ => E s) - fun r => 2 * P r) (-2 * D τ) τ
      simpa using hsub
    have hev : E =ᶠ[nhds τ] F := by
      filter_upwards [Ioo_mem_nhds hτI.1 hτI.2] with r hr
      exact hEF r ⟨hr.1.le, hr.2.le⟩
    exact hF.congr_of_eventuallyEq hev
  refine ⟨hEac, ?_⟩
  filter_upwards [hderiv] with τ hτ
  intro hτI
  simpa [E, D, q, diagonalEnergySlice, diagonalDissipationSlice,
    setIntegral_univ] using hτ hτI

private theorem nash_diagonal_ae_decay {d : ℕ} (hd : 0 < d) {s T c B : ℝ}
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
      (hDiss : deriv E x ≤ -c * E x ^ (1 + (2 : ℝ) / d) * B ^ (-(4 : ℝ) / d)) :
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
        _ = (q * (-c)) * (E x ^ (q - 1) * E x ^ (1 + (2 : ℝ) / d)) *
            B ^ (-(4 : ℝ) / d) := by ring
        _ = _ := by rw [mul_comm (E x ^ (q - 1)), hexp]; dsimp [q]; ring
    calc
      (2 * c / d) * B ^ (-(4 : ℝ) / d) =
          q * E x ^ (q - 1) *
            (-c * E x ^ (1 + (2 : ℝ) / d) * B ^ (-(4 : ℝ) / d)) := hleft.symm
      _ ≤ q * E x ^ (q - 1) * deriv E x := by nlinarith [hmul]
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
    have hconst : (∫ x in s..T, (2 * c / d) * B ^ (-(4 : ℝ) / d)) =
        (2 * c / d) * B ^ (-(4 : ℝ) / d) * (T - s) := by
      simp [intervalIntegral.integral_const]
      ring
    rw [hconst, hftc] at hintLower
    linarith
  have hduration : 0 < T - s := by linarith
  have htargetpos : 0 <
      ((d : ℝ) / (2 * c * (T - s))) ^ ((d : ℝ) / 2) * B ^ 2 := by positivity
  have htargetpow := nashDiagonalBound_rpow hd hc hB hduration
  have htarget :
      (((d : ℝ) / (2 * c * (T - s))) ^ ((d : ℝ) / 2) * B ^ 2) ^ q ≤ F T := by
    calc
      _ = (2 * c / d) * B ^ (-(4 : ℝ) / d) * (T - s) := by
        simpa [q] using htargetpow
      _ ≤ F T := hFbound
  exact (Real.rpow_le_rpow_iff_of_neg htargetpos hEtpos hqneg).mp
    (by simpa [F, q] using htarget)

private theorem eLpNorm_one_eq_ofReal_integral_abs {d : ℕ} {f : Vec d → ℝ}
    (hf : Integrable f volume) :
    eLpNorm f 1 volume = ENNReal.ofReal (∫ x : Vec d, |f x|) := by
  rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
  rw [lintegral_congr_ae]
  · rw [← ofReal_integral_eq_lintegral_ofReal hf.norm
      (ae_of_all _ fun x : Vec d => abs_nonneg (f x))]
    congr 1
  · filter_upwards [] with x
    simp [Real.enorm_eq_ofReal_abs]

/-- L¹-to-L² smoothing for any whole-space energy solution.  `B` may be any
positive upper bound on the L¹ norm of the initial datum. -/
theorem cauchy_nash_diagonal_bound {d : ℕ} (hd : 0 < d) {Lam s T : ℝ}
    (hsT : s < T) (_hLam : 1 ≤ Lam) (a : ParCoeffField d)
    (ha : IsParabolicCoeff 1 Lam a univ (Icc s T)) (f : Vec d → ℝ)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) {B t : ℝ}
    (hB : 0 < B) (hBf : ∫ x : Vec d, |f x| ≤ B)
    (ht : t ∈ Icc s T) (hst : s < t) :
    ∫ x : Vec d, u.toFun (x, t) ^ 2 ≤
      nashDiagonalSmoothingConstant d * (t - s) ^ (-(d : ℝ) / 2) * B ^ 2 := by
  let C := nashInequalityConstant d
  have hNashSpec := nashInequalityConstant_spec d hd
  have hC : 0 < C := by simpa [C] using hNashSpec.1
  have hNash : ∀ u : H1Function (Set.univ : Set (Vec d)),
      Integrable u.toFun volume →
      ∫ x, u.toFun x ^ 2 ≤
        C * (∫ x, vecEuclideanNorm (u.grad x) ^ 2) ^ ((d : ℝ) / (d + 2)) *
          (∫ x, |u.toFun x|) ^ ((4 : ℝ) / (d + 2)) := by
    simpa [C] using hNashSpec.2
  let E : ℝ → ℝ := diagonalEnergySlice u
  let D : ℝ → ℝ := diagonalDissipationSlice a u
  have hED := diagonalEnergySlice_ac_deriv hsT a ha f hf2 u hu
  have hEac : AbsolutelyContinuousOnInterval E s t := by
    have hsub : uIcc s t ⊆ uIcc s T := by
      rw [uIcc_of_le hsT.le, uIcc_of_le hst.le]
      intro r hr
      exact ⟨hr.1, le_trans hr.2 ht.2⟩
    simpa [E, diagonalEnergySlice] using hED.1.mono hsub
  have hEnonneg : ∀ r ∈ Icc s t, 0 ≤ E r := by
    intro r hr
    dsimp [E, diagonalEnergySlice]
    exact integral_nonneg_of_ae (ae_of_all _ fun x => sq_nonneg (u.toFun (x, r)))
  have hderiv : ∀ᵐ r ∂volume, r ∈ Ioo s t →
      HasDerivAt E (deriv E r) r := by
    filter_upwards [hED.2] with r hr
    intro hrI
    have hrT : r ∈ Ioo s T := ⟨hrI.1, lt_of_lt_of_le hrI.2 ht.2⟩
    have h := hr hrT
    have hh : HasDerivAt E (-2 * D r) r := by
      simpa [E, D] using h
    have hval := hh.deriv
    exact hh.congr_deriv hval.symm
  have hderivVal : ∀ᵐ r ∂volume, r ∈ Ioo s t → deriv E r = -2 * D r := by
    filter_upwards [hED.2] with r hr
    intro hrI
    have hrT : r ∈ Ioo s T := ⟨hrI.1, lt_of_lt_of_le hrI.2 ht.2⟩
    have hh : HasDerivAt E (-2 * D r) r := by
      simpa [E, D] using hr hrT
    exact hh.deriv
  have hqInt : IntegrableOn (PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u)
      ((univ : Set (Vec d)) ×ˢ Icc s T) :=
    PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity_integrable ha u
  have hqProd : Integrable
      (PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u)
      ((volume.restrict (univ : Set (Vec d))).prod (volume.restrict (Icc s T))) := by
    rw [← PDE.Parabolic.Energy.volume_restrict_prod]
    exact hqInt
  have hqSlices := hqProd.prod_left_ae
  have hEllProd : ∀ᵐ z ∂((volume.restrict (univ : Set (Vec d))).prod
      (volume.restrict (Icc s T))),
      vecNormSq (u.grad z) ≤
        PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z := by
    rw [← PDE.Parabolic.Energy.volume_restrict_prod]
    filter_upwards [ha.elliptic] with z hz
    have h := hz.coercive (u.grad z)
    simpa [PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity] using h
  have hEllSlices := PDE.Parabolic.Energy.ae_ae_swap hEllProd
  have hH1Slices := PDE.Parabolic.ae_parH1_slice_h1 isOpen_univ u
  have hNashTime : ∀ᵐ r ∂(volume.restrict (Icc s T)),
      E r ≤ C * D r ^ ((d : ℝ) / (d + 2)) * B ^ ((4 : ℝ) / (d + 2)) := by
    filter_upwards [hH1Slices, hqSlices, hEllSlices,
      ae_restrict_mem measurableSet_Icc] with r hrH1 hrq hrEll hrIcc
    obtain ⟨v, hv, hgrad⟩ := hrH1
    have hcon := PDE.Parabolic.Cauchy.L1.cauchyL1Contraction
      d 1 Lam a s T hsT ha f hf1 hf2 u hu r hrIcc
    have hv1 : Integrable v.toFun volume := by
      simpa [hv] using hcon.1
    have hvabs : ∫ x : Vec d, |v.toFun x| ≤ B := by
      have hsliceNorm := eLpNorm_one_eq_ofReal_integral_abs hcon.1
      have hfNorm := eLpNorm_one_eq_ofReal_integral_abs hf1
      have hnorm : ENNReal.ofReal (∫ x : Vec d, |parSlice u.toFun r x|) ≤
          ENNReal.ofReal (∫ x : Vec d, |f x|) := by
        rw [← hsliceNorm, ← hfNorm]
        exact hcon.2
      have hmass : ∫ x : Vec d, |parSlice u.toFun r x| ≤ B :=
        ((ENNReal.ofReal_le_ofReal_iff
          (integral_nonneg_of_ae (ae_of_all _ fun x : Vec d => abs_nonneg (f x)))).mp
          hnorm).trans hBf
      simpa [hv] using hmass
    have hgMem : MemLp (fun x : Vec d => vecEuclideanNorm (v.grad x)) 2 volume := by
      have hg := v.gradMemL2.memLp_vecEuclideanNorm
      simpa only [GradMemLpOn, GradMemL2On, MemLpOn, volumeOn,
        Measure.restrict_univ] using hg
    have hgint : Integrable (fun x : Vec d => vecEuclideanNorm (v.grad x) ^ 2) volume :=
      hgMem.integrable_sq
    have hDint : Integrable (fun x : Vec d =>
        PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u (x, r)) volume := by
      simpa only [Measure.restrict_univ] using hrq
    have hGleD : (∫ x : Vec d, vecEuclideanNorm (v.grad x) ^ 2) ≤ D r := by
      have hpoint' : ∀ᵐ x ∂(volume.restrict univ),
          vecEuclideanNorm (v.grad x) ^ 2 ≤
            PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u (x, r) := by
        filter_upwards [hrEll] with x hx
        rw [hgrad]
        simpa [parSlice, vecEuclideanNorm_sq] using hx
      have hpoint : ∀ᵐ x ∂volume,
          vecEuclideanNorm (v.grad x) ^ 2 ≤
            PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u (x, r) := by
        simpa only [Measure.restrict_univ] using hpoint'
      calc
        _ ≤ ∫ x : Vec d, PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u (x, r) :=
          integral_mono_ae hgint hDint hpoint
        _ = D r := by rfl
    have hN := hNash v hv1
    have hEeq : E r = ∫ x : Vec d, v.toFun x ^ 2 := by
      dsimp [E, diagonalEnergySlice]
      apply integral_congr_ae
      filter_upwards [] with x
      simp [hv, parSlice]
    rw [hEeq]
    have hGnonneg : 0 ≤ ∫ x : Vec d, vecEuclideanNorm (v.grad x) ^ 2 :=
      integral_nonneg_of_ae (ae_of_all _ fun x => sq_nonneg _)
    have hDnonneg : 0 ≤ D r := by
      have hqnonneg : 0 ≤ᵐ[volume.restrict univ] fun x : Vec d =>
          PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u (x, r) := by
        filter_upwards [hrEll] with x hx
        have hx' : vecNormSq (v.grad x) ≤
            PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u (x, r) := by
          rw [hgrad]
          exact hx
        exact (vecNormSq_nonneg (v.grad x)).trans hx'
      dsimp [D, diagonalDissipationSlice]
      simpa [setIntegral_univ] using setIntegral_nonneg_of_ae_restrict hqnonneg
    have hgradpow : (∫ x : Vec d, vecEuclideanNorm (v.grad x) ^ 2) ^
          ((d : ℝ) / (d + 2)) ≤ D r ^ ((d : ℝ) / (d + 2)) :=
      Real.rpow_le_rpow hGnonneg hGleD (by positivity)
    have hmasspow : (∫ x : Vec d, |v.toFun x|) ^ ((4 : ℝ) / (d + 2)) ≤
        B ^ ((4 : ℝ) / (d + 2)) := by
      have hbase : 0 ≤ ∫ x : Vec d, |v.toFun x| :=
        integral_nonneg_of_ae (ae_of_all _ fun x => abs_nonneg _)
      exact Real.rpow_le_rpow hbase hvabs (by positivity)
    calc
      ∫ x : Vec d, v.toFun x ^ 2 ≤
          C * (∫ x : Vec d, vecEuclideanNorm (v.grad x) ^ 2) ^
            ((d : ℝ) / (d + 2)) * (∫ x : Vec d, |v.toFun x|) ^
              ((4 : ℝ) / (d + 2)) := hN
      _ ≤ C * D r ^ ((d : ℝ) / (d + 2)) * B ^ ((4 : ℝ) / (d + 2)) := by
        have hbase : 0 ≤ ∫ x : Vec d, |v.toFun x| :=
          integral_nonneg_of_ae (ae_of_all _ fun x => abs_nonneg _)
        have hprod := mul_le_mul hgradpow hmasspow
          (Real.rpow_nonneg hbase _) (Real.rpow_nonneg hDnonneg _)
        have hscale := mul_le_mul_of_nonneg_left hprod hC.le
        simpa only [mul_assoc] using hscale
      _ = C * D r ^ ((d : ℝ) / (d + 2)) * B ^ ((4 : ℝ) / (d + 2)) := rfl
  have hNashAll : ∀ᵐ r ∂volume, r ∈ Ioo s t →
      E r ≤ C * D r ^ ((d : ℝ) / (d + 2)) * B ^ ((4 : ℝ) / (d + 2)) := by
    have hrestrict : ∀ᵐ r ∂(volume.restrict (Icc s T)),
        E r ≤ C * D r ^ ((d : ℝ) / (d + 2)) * B ^ ((4 : ℝ) / (d + 2)) := hNashTime
    rw [ae_restrict_iff' measurableSet_Icc] at hrestrict
    filter_upwards [hrestrict] with r hr hrt
    exact hr ⟨le_of_lt hrt.1, le_trans hrt.2.le ht.2⟩
  have hDnonnegAE : ∀ᵐ r ∂volume, r ∈ Ioo s t → 0 ≤ D r := by
    have hnonnegProd := PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity_nonneg_ae ha u
    have hnonnegSwap := PDE.Parabolic.Energy.ae_ae_swap (by
      rw [← PDE.Parabolic.Energy.volume_restrict_prod]
      exact hnonnegProd)
    have hnonnegTime : ∀ᵐ r ∂(volume.restrict (Icc s T)), 0 ≤ D r := by
      filter_upwards [hnonnegSwap] with r hr
      dsimp [D, diagonalDissipationSlice]
      simpa [setIntegral_univ] using setIntegral_nonneg_of_ae_restrict hr
    rw [ae_restrict_iff' measurableSet_Icc] at hnonnegTime
    filter_upwards [hnonnegTime] with r hr hrt
    exact hr ⟨le_of_lt hrt.1, le_trans hrt.2.le ht.2⟩
  have hDiss : ∀ᵐ r ∂volume, r ∈ Ioo s t →
      deriv E r ≤ -(2 * C ^ (-((d : ℝ) + 2) / d)) *
        E r ^ (1 + (2 : ℝ) / d) * B ^ (-(4 : ℝ) / d) := by
    filter_upwards [hderiv, hderivVal, hNashAll, hDnonnegAE]
      with r hder hderVal hNashr hDr
    intro hrI
    have hder' := hder hrI
    have hNash' := hNashr hrI
    have hDr' := hDr hrI
    have hEr : 0 ≤ E r := hEnonneg r ⟨le_of_lt hrI.1, le_of_lt hrI.2⟩
    have hED : deriv E r = -2 * D r := hderVal hrI
    have hEDineq : deriv E r ≤ -2 * D r := by rw [hED]
    have hbound := PDE.Parabolic.Cauchy.Weights.nash_energy_derivative_bound
      hd hC hB hEr hDr' hNash' hEDineq
    simpa [mul_assoc] using hbound
  have hc : 0 < 2 * C ^ (-((d : ℝ) + 2) / d) := by positivity
  have hfinal := nash_diagonal_ae_decay
    hd hst hc hB E hEac hEnonneg hderiv hDiss
  have hraw := hfinal
  let p : ℝ := (d : ℝ) / 2
  let c₀ : ℝ := (d : ℝ) / (4 * C ^ (-((d : ℝ) + 2) / d))
  have hpow : ((d : ℝ) / (4 * C ^ (-((d : ℝ) + 2) / d) * (t - s))) ^ p =
      c₀ ^ p * (t - s) ^ (-p) := by
    have hden : 0 < 4 * C ^ (-((d : ℝ) + 2) / d) := by positivity
    have htime : 0 < t - s := by linarith
    calc
      _ = (c₀ / (t - s)) ^ p := by
        rw [show (d : ℝ) /
          (4 * C ^ (-((d : ℝ) + 2) / d) * (t - s)) =
          ((d : ℝ) / (4 * C ^ (-((d : ℝ) + 2) / d))) / (t - s) by
            field_simp]
      _ = c₀ ^ p * (t - s) ^ (-p) := by
        rw [Real.div_rpow (by positivity) (by positivity)]
        rw [Real.rpow_neg (by positivity) p]
        rw [div_eq_mul_inv]
  have hc₀ : 0 < c₀ := by
    dsimp [c₀]
    positivity
  have hraw' : ∫ x : Vec d, u.toFun (x, t) ^ 2 ≤
      ((d : ℝ) / (2 * (2 * C ^ (-((d : ℝ) + 2) / d)) * (t - s))) ^ p * B ^ 2 := by
    simpa [E, diagonalEnergySlice, p] using hraw
  rw [show 2 * (2 * C ^ (-((d : ℝ) + 2) / d)) =
      4 * C ^ (-((d : ℝ) + 2) / d) by ring, hpow] at hraw'
  have hexp : -((d : ℝ) / 2) = -(d : ℝ) / 2 := by ring
  have hconstant : c₀ ^ p = nashDiagonalSmoothingConstant d := by
    dsimp [c₀, C, p, nashDiagonalSmoothingConstant, nashInequalityConstant]
  calc
    ∫ x : Vec d, u.toFun (x, t) ^ 2 ≤
        c₀ ^ p * (t - s) ^ (-(d : ℝ) / 2) * B ^ 2 := by
          simpa only [p, hexp, mul_assoc] using hraw'
    _ = nashDiagonalSmoothingConstant d *
        (t - s) ^ (-(d : ℝ) / 2) * B ^ 2 := by
          rw [hconstant]

end PDE.Parabolic.Cauchy.Weights
