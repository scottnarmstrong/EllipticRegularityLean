module

public import EllipticRegularity.Parabolic.Cauchy.L1.Contraction
public import EllipticRegularity.Parabolic.Cauchy.Energy.Global
public import EllipticRegularity.Parabolic.Cauchy.Energy.Density
public import EllipticRegularity.Parabolic.WeakSlice.Product
public import EllipticRegularity.Parabolic.Sobolev.ParabolicSlices
public import EllipticRegularity.Parabolic.Cauchy.Weights.NashDissipation
public import EllipticRegularity.Parabolic.Cauchy.OnDiag.NashSmoothing
public import PDEFoundation.Analysis.Inequalities.Nash.Main
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Whole-space Nash smoothing for a Cauchy solution

The energy identity gives an absolutely continuous time representative of the
whole-space square integral.  The spatial Nash inequality and the L¹
contraction then give its almost everywhere differential inequality.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.OnDiag

open MeasureTheory Set Filter

noncomputable def cauchyEnergySlice {d : ℕ} {s T : ℝ}
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T)) (τ : ℝ) : ℝ :=
  ∫ x : Vec d, u.toFun (x, τ) ^ 2

noncomputable def cauchyDissipationSlice {d : ℕ} {s T : ℝ}
    (a : ParCoeffField d) (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (τ : ℝ) : ℝ :=
  ∫ x : Vec d, PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u (x, τ)

/-- A fixed dimensional constant in the whole-space Nash inequality. -/
noncomputable def nashSpatialConstant (d : ℕ) (hd : 0 < d) : ℝ :=
  Classical.choose (PDE.Nash.exists_nash_constant_full d (by omega))

/-- Positivity and the Nash inequality for the selected dimensional constant. -/
theorem nashSpatialConstant_spec (d : ℕ) (hd : 0 < d) :
    0 < nashSpatialConstant d hd ∧
      ∀ u : H1Function (Set.univ : Set (Vec d)),
        Integrable u.toFun volume →
        ∫ x, u.toFun x ^ 2 ≤
          nashSpatialConstant d hd *
            (∫ x, vecEuclideanNorm (u.grad x) ^ 2) ^ ((d : ℝ) / (d + 2)) *
              (∫ x, |u.toFun x|) ^ ((4 : ℝ) / (d + 2)) := by
  dsimp [nashSpatialConstant]
  exact Classical.choose_spec (PDE.Nash.exists_nash_constant_full d (by omega))

/-- The dimensional coefficient in the unit-mass `L¹` to `L²` Nash decay. -/
noncomputable def cauchyUnitMassNashConstant (d : ℕ) (hd : 0 < d) : ℝ :=
  ((d : ℝ) / (4 * nashSpatialConstant d hd ^ (-((d : ℝ) + 2) / d))) ^ ((d : ℝ) / 2)

/-- The fixed smoothing coefficient is positive. -/
theorem cauchyUnitMassNashConstant_pos (d : ℕ) (hd : 0 < d) :
    0 < cauchyUnitMassNashConstant d hd := by
  have hC := (nashSpatialConstant_spec d hd).1
  unfold cauchyUnitMassNashConstant
  positivity

/-- The whole-space energy identity makes the slice energy absolutely
continuous, with derivative minus twice the slice dissipation almost
everywhere. -/
theorem cauchyEnergySlice_ac_deriv {d : ℕ} {lam Lam s T : ℝ}
    (hsT : s < T) (a : ParCoeffField d)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ)
    (hf : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) :
    AbsolutelyContinuousOnInterval (cauchyEnergySlice u) s T ∧
      ∀ᵐ τ ∂volume, τ ∈ Ioo s T →
        HasDerivAt (cauchyEnergySlice u) (-2 * cauchyDissipationSlice a u τ) τ := by
  let q : Vec d × ℝ → ℝ := PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u
  let D : ℝ → ℝ := fun τ => ∫ x in (univ : Set (Vec d)), q (x, τ)
  let E : ℝ → ℝ := cauchyEnergySlice u
  let P : ℝ → ℝ := fun τ => ∫ r in s..τ, D r
  let F : ℝ → ℝ := fun τ => E s - 2 * P τ
  have hqInt : IntegrableOn q ((univ : Set (Vec d)) ×ˢ Icc s T) := by
    exact PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity_integrable ha u
  have hqFub := PDE.Parabolic.WeakSlice.integral_prod_slices hqInt
  have hDInt : IntegrableOn D (Icc s T) := by
    simpa only [D] using hqFub.1
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
    simpa only [D, cauchyDissipationSlice, q, setIntegral_univ] using hFub.2
  have hIocEq (τ : ℝ) (hτ : τ ∈ Icc s T) :
      (∫ r in Ioc s τ, D r) = ∫ r in s..τ, D r := by
    exact (intervalIntegral.integral_of_le hτ.1).symm
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
      have hsub : HasDerivAt ((fun _ : ℝ => E s) - fun r => 2 * P r)
          (0 - 2 * D τ) τ := hc.sub (hP.const_mul 2)
      change HasDerivAt ((fun _ : ℝ => E s) - fun r => 2 * P r)
        (-2 * D τ) τ
      simpa using hsub
    have hev : E =ᶠ[nhds τ] F := by
      filter_upwards [Ioo_mem_nhds hτI.1 hτI.2] with r hr
      exact hEF r ⟨hr.1.le, hr.2.le⟩
    exact hF.congr_of_eventuallyEq hev
  refine ⟨hEac, ?_⟩
  filter_upwards [hderiv] with τ hτ
  intro hτI
  simpa [E, D, cauchyDissipationSlice, cauchyEnergySlice, q,
    setIntegral_univ] using hτ hτI

private theorem eLpNorm_one_eq_ofReal_integral_abs {d : ℕ} {g : Vec d → ℝ}
    (hg : Integrable g volume) :
    eLpNorm g 1 volume = ENNReal.ofReal (∫ x : Vec d, |g x|) := by
  rw [eLpNorm_one_eq_lintegral_enorm hg.aestronglyMeasurable]
  rw [lintegral_congr_ae]
  · rw [← ofReal_integral_eq_lintegral_ofReal hg.norm
      (ae_of_all _ fun x : Vec d => abs_nonneg (g x))]
    congr 1
  · filter_upwards [] with x
    simp [Real.enorm_eq_ofReal_abs]

/-- A unit-mass nonnegative datum keeps its `L¹` norm at most one on every
time slice of the Cauchy solution. -/
theorem cauchy_unit_mass_slice_L1_le_one {d : ℕ} {Lam s T : ℝ}
    (hsT : s < T) (a : ParCoeffField d)
    (ha : IsParabolicCoeff 1 Lam a univ (Icc s T)) (f : Vec d → ℝ)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (hfnonneg : 0 ≤ᵐ[volume] f) (hfmass : ∫ x, f x = 1)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) {t : ℝ} (ht : t ∈ Icc s T) :
    ∫ x : Vec d, |u.toFun (x, t)| ≤ 1 := by
  let g : Vec d → ℝ := parSlice u.toFun t
  have hcon := PDE.Parabolic.Cauchy.L1.cauchyL1Contraction d 1 Lam a s T
    hsT ha f hf1 hf2 u hu t ht
  have hfabs : ∫ x : Vec d, |f x| = 1 := by
    calc
      ∫ x : Vec d, |f x| = ∫ x : Vec d, f x := by
        apply integral_congr_ae
        filter_upwards [hfnonneg] with x hx
        exact abs_of_nonneg hx
      _ = 1 := hfmass
  have hfNorm : eLpNorm f 1 volume = ENNReal.ofReal 1 := by
    rw [eLpNorm_one_eq_ofReal_integral_abs hf1, hfabs]
  have hgNorm : eLpNorm g 1 volume ≤ ENNReal.ofReal 1 := by
    simpa only [g, parSlice] using hcon.2.trans_eq hfNorm
  rw [eLpNorm_one_eq_ofReal_integral_abs hcon.1] at hgNorm
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hgNorm

/-- Nash smoothing on a whole-space Cauchy solution with unit nonnegative
mass.  The proof uses the whole-space energy identity and the spatial Nash
inequality, with the differential inequality interpreted almost everywhere
in time. -/
theorem cauchy_unit_mass_nash_decay {d : ℕ} (hd : 0 < d) {Lam s T : ℝ}
    (hsT : s < T) (a : ParCoeffField d)
    (ha : IsParabolicCoeff 1 Lam a univ (Icc s T)) (f : Vec d → ℝ)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (hfnonneg : 0 ≤ᵐ[volume] f) (hfmass : ∫ x, f x = 1)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) {t : ℝ} (ht : t ∈ Icc s T)
    (hst : s < t) :
    ∫ x : Vec d, u.toFun (x, t) ^ 2 ≤
      cauchyUnitMassNashConstant d hd * (t - s) ^ (-(d : ℝ) / 2) := by
  let C : ℝ := nashSpatialConstant d hd
  have hCspec := nashSpatialConstant_spec d hd
  have hC : 0 < C := by simpa [C] using hCspec.1
  have hNash := hCspec.2
  let E : ℝ → ℝ := cauchyEnergySlice u
  let D : ℝ → ℝ := cauchyDissipationSlice a u
  have hED := cauchyEnergySlice_ac_deriv hsT a ha f hf2 u hu
  have hEac : AbsolutelyContinuousOnInterval E s t := by
    have hsub : uIcc s t ⊆ uIcc s T := by
      rw [uIcc_of_le hsT.le, uIcc_of_le hst.le]
      intro r hr
      exact ⟨hr.1, le_trans hr.2 ht.2⟩
    exact hED.1.mono hsub
  have hEnonneg : ∀ r ∈ Icc s t, 0 ≤ E r := by
    intro r hr
    dsimp [E, cauchyEnergySlice]
    exact integral_nonneg_of_ae (ae_of_all _ fun x => sq_nonneg (u.toFun (x, r)))
  have hderiv : ∀ᵐ r ∂volume, r ∈ Ioo s t →
      HasDerivAt E (deriv E r) r := by
    filter_upwards [hED.2] with r hr
    intro hrI
    have hrT : r ∈ Ioo s T := ⟨hrI.1, lt_of_lt_of_le hrI.2 ht.2⟩
    have h := hr hrT
    have h' : HasDerivAt E (-2 * D r) r := by simpa [E, D] using h
    exact h'.congr_deriv h'.deriv.symm
  have hderivVal : ∀ᵐ r ∂volume, r ∈ Ioo s t → deriv E r = -2 * D r := by
    filter_upwards [hED.2] with r hr
    intro hrI
    have hrT : r ∈ Ioo s T := ⟨hrI.1, lt_of_lt_of_le hrI.2 ht.2⟩
    have h := hr hrT
    have h' : HasDerivAt E (-2 * D r) r := by simpa [E, D] using h
    exact h'.deriv
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
      E r ≤ C * D r ^ ((d : ℝ) / (d + 2)) := by
    filter_upwards [hH1Slices, hqSlices, hEllSlices,
        ae_restrict_mem measurableSet_Icc] with r hrH1 hrq hrEll hrIcc
    obtain ⟨v, hv, hgrad⟩ := hrH1
    have hcon := PDE.Parabolic.Cauchy.L1.cauchyL1Contraction d 1 Lam a s T
      hsT ha f hf1 hf2 u hu r hrIcc
    have hv1 : Integrable v.toFun volume := by
      have heq : v.toFun =ᵐ[volume] parSlice u.toFun r :=
        Filter.Eventually.of_forall fun x => congrFun hv x
      exact hcon.1.congr heq.symm
    have hvabs : ∫ x : Vec d, |v.toFun x| ≤ 1 := by
      have h := cauchy_unit_mass_slice_L1_le_one hsT a ha f hf1 hf2
        hfnonneg hfmass u hu hrIcc
      have h' : ∫ x : Vec d, |parSlice u.toFun r x| ≤ 1 := by
        change ∫ x : Vec d, |u.toFun (x, r)| ≤ 1
        exact h
      rw [hv]
      exact h'
    have hgMem : MemLp (fun x : Vec d => vecEuclideanNorm (v.grad x)) 2 volume := by
      have hg := v.gradMemL2.memLp_vecEuclideanNorm
      simpa [GradMemLpOn, GradMemL2On, MemLpOn, volumeOn, Measure.restrict_univ] using hg
    have hgint : Integrable (fun x : Vec d => vecEuclideanNorm (v.grad x) ^ 2) volume :=
      hgMem.integrable_sq
    have hDint : Integrable (fun x : Vec d =>
        PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u (x, r)) volume := by
      simpa [Measure.restrict_univ] using hrq
    have hGleD : (∫ x : Vec d, vecEuclideanNorm (v.grad x) ^ 2) ≤ D r := by
      have hrEll' : ∀ᵐ x ∂volume,
          vecNormSq (u.grad (x, r)) ≤
            PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u (x, r) := by
        simpa using hrEll
      have hpoint : ∀ᵐ x ∂volume,
          vecEuclideanNorm (v.grad x) ^ 2 ≤
            PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u (x, r) := by
        filter_upwards [hrEll'] with x hx
        calc
          vecEuclideanNorm (v.grad x) ^ 2 = vecEuclideanNorm (u.grad (x, r)) ^ 2 := by
            rw [hgrad]
            rfl
          _ = vecNormSq (u.grad (x, r)) := vecEuclideanNorm_sq _
          _ ≤ PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u (x, r) := hx
      calc
        _ ≤ ∫ x : Vec d, PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u (x, r) :=
          integral_mono_ae hgint hDint hpoint
        _ = D r := by
          simp [D, cauchyDissipationSlice]
    have hN := hNash v hv1
    have hEeq : E r = ∫ x : Vec d, v.toFun x ^ 2 := by
      dsimp [E, cauchyEnergySlice]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hv]
      rfl
    rw [hEeq]
    have hGnonneg : 0 ≤ ∫ x : Vec d, vecEuclideanNorm (v.grad x) ^ 2 :=
      integral_nonneg_of_ae (ae_of_all _ fun x => sq_nonneg _)
    have hDnonneg : 0 ≤ D r := hGnonneg.trans hGleD
    have hp : 0 < (d : ℝ) / (d + 2) := by positivity
    have hpower : (∫ x : Vec d, vecEuclideanNorm (v.grad x) ^ 2) ^
          ((d : ℝ) / (d + 2)) ≤ D r ^ ((d : ℝ) / (d + 2)) :=
      Real.rpow_le_rpow hGnonneg hGleD (by positivity)
    have hmassPow : (∫ x : Vec d, |v.toFun x|) ^ ((4 : ℝ) / (d + 2)) ≤ 1 := by
      have hbase : 0 ≤ ∫ x : Vec d, |v.toFun x| :=
        integral_nonneg_of_ae (ae_of_all _ fun x => abs_nonneg _)
      have hp' : 0 ≤ (4 : ℝ) / (d + 2) := by positivity
      have hpow := Real.rpow_le_rpow hbase hvabs hp'
      simpa using hpow
    calc
      ∫ x : Vec d, v.toFun x ^ 2 ≤
          C * (∫ x : Vec d, vecEuclideanNorm (v.grad x) ^ 2) ^
            ((d : ℝ) / (d + 2)) *
            (∫ x : Vec d, |v.toFun x|) ^ ((4 : ℝ) / (d + 2)) := hN
      _ ≤ C * D r ^ ((d : ℝ) / (d + 2)) * 1 := by
        have hprod :
            (∫ x : Vec d, vecEuclideanNorm (v.grad x) ^ 2) ^
                ((d : ℝ) / (d + 2)) *
              (∫ x : Vec d, |v.toFun x|) ^ ((4 : ℝ) / (d + 2)) ≤
            D r ^ ((d : ℝ) / (d + 2)) * 1 := by
          exact mul_le_mul hpower hmassPow
            (Real.rpow_nonneg (integral_nonneg_of_ae
              (ae_of_all _ fun x => abs_nonneg (v.toFun x))) _)
            (Real.rpow_nonneg hDnonneg _)
        calc
          _ = C * ((∫ x : Vec d, vecEuclideanNorm (v.grad x) ^ 2) ^
              ((d : ℝ) / (d + 2)) *
                (∫ x : Vec d, |v.toFun x|) ^ ((4 : ℝ) / (d + 2))) := by ring
          _ ≤ C * (D r ^ ((d : ℝ) / (d + 2)) * 1) :=
            mul_le_mul_of_nonneg_left hprod hC.le
          _ = C * D r ^ ((d : ℝ) / (d + 2)) * 1 := by ring
      _ = C * D r ^ ((d : ℝ) / (d + 2)) := by ring
      _ = _ := rfl
  have hNashAll : ∀ᵐ r ∂volume, r ∈ Ioo s t →
      E r ≤ C * D r ^ ((d : ℝ) / (d + 2)) := by
    have hrestrict : ∀ᵐ r ∂(volume.restrict (Icc s T)),
        E r ≤ C * D r ^ ((d : ℝ) / (d + 2)) := hNashTime
    rw [ae_restrict_iff' measurableSet_Icc] at hrestrict
    filter_upwards [hrestrict] with r hr hrt
    exact hr ⟨le_of_lt hrt.1, le_trans hrt.2.le ht.2⟩
  have hDnonnegAE : ∀ᵐ r ∂volume, r ∈ Ioo s t → 0 ≤ D r := by
    have hnonnegProd := PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity_nonneg_ae ha u
    have hnonnegSwap := PDE.Parabolic.Energy.ae_ae_swap (by
      rw [← PDE.Parabolic.Energy.volume_restrict_prod]
      exact hnonnegProd)
    have hnonnegTime : ∀ᵐ r ∂(volume.restrict (Icc s T)),
        0 ≤ D r := by
      filter_upwards [hnonnegSwap] with r hr
      have h := setIntegral_nonneg_of_ae_restrict hr
      simpa [D, cauchyDissipationSlice, setIntegral_univ] using h
    rw [ae_restrict_iff' measurableSet_Icc] at hnonnegTime
    filter_upwards [hnonnegTime] with r hr hrt
    exact hr ⟨le_of_lt hrt.1, le_trans hrt.2.le ht.2⟩
  have hDiss : ∀ᵐ r ∂volume, r ∈ Ioo s t →
      deriv E r ≤ -(2 * C ^ (-((d : ℝ) + 2) / d)) *
        E r ^ (1 + (2 : ℝ) / d) * (1 : ℝ) ^ (-(4 : ℝ) / d) := by
    filter_upwards [hderiv, hderivVal, hNashAll, hDnonnegAE] with r hder hderVal hNashr hDr
    intro hrI
    have hderVal' := hderVal hrI
    have hNash' := hNashr hrI
    have hDr' := hDr hrI
    have hEr : 0 ≤ E r := hEnonneg r ⟨le_of_lt hrI.1, le_of_lt hrI.2⟩
    have hED : deriv E r ≤ -2 * D r := by rw [hderVal']
    have hNash'' : E r ≤ C * D r ^ ((d : ℝ) / (d + 2)) *
        (1 : ℝ) ^ ((4 : ℝ) / (d + 2)) := by simpa using hNash'
    have hbound := PDE.Parabolic.Cauchy.Weights.nash_energy_derivative_bound
      hd hC (by norm_num : 0 < (1 : ℝ)) hEr hDr' hNash'' hED
    simpa [mul_assoc, Real.one_rpow] using hbound
  have hCneg : 0 < 2 * C ^ (-((d : ℝ) + 2) / d) := by positivity
  have hfinal := nashDiagonalDecay_of_ae_deriv (d := d) (s := s) (T := t)
    (c := 2 * C ^ (-((d : ℝ) + 2) / d)) (B := 1) hd hst hCneg
    (by norm_num) E hEac hEnonneg hderiv hDiss
  let C₀ : ℝ := ((d : ℝ) / (2 * (2 * C ^ (-((d : ℝ) + 2) / d)))) ^
    ((d : ℝ) / 2)
  have hΔ : 0 < t - s := by linarith
  have hC₀eq : C₀ = cauchyUnitMassNashConstant d hd := by
    dsimp [C₀, cauchyUnitMassNashConstant, C]
    ring_nf
  calc
    ∫ x : Vec d, u.toFun (x, t) ^ 2 ≤
        C₀ * (t - s) ^ (-(d : ℝ) / 2) := by
      have hscale :
          ((d : ℝ) / (2 * (2 * C ^ (-((d : ℝ) + 2) / d)) * (t - s))) ^
              ((d : ℝ) / 2) = C₀ * (t - s) ^ (-(d : ℝ) / 2) := by
        have hbase :
            (d : ℝ) / (2 * (2 * C ^ (-((d : ℝ) + 2) / d)) * (t - s)) =
              ((d : ℝ) / (2 * (2 * C ^ (-((d : ℝ) + 2) / d)))) * (t - s)⁻¹ := by
          field_simp
        rw [hbase, Real.mul_rpow (by positivity) (inv_nonneg.mpr hΔ.le),
          ← Real.rpow_neg_eq_inv_rpow]
        rw [show (-(d : ℝ) / 2) = -((d : ℝ) / 2) by ring]
      have h := hfinal
      dsimp [E, cauchyEnergySlice] at h
      rw [hscale] at h
      simpa [C₀, Real.one_rpow] using h
    _ = cauchyUnitMassNashConstant d hd * (t - s) ^ (-(d : ℝ) / 2) := by
      rw [hC₀eq]


end PDE.Parabolic.Cauchy.OnDiag
