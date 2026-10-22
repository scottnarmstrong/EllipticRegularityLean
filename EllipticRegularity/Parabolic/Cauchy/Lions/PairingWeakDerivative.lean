module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.Lions.TimePairingIdentity
public import PDEFoundation.Sobolev.OneDimensional.WeakPrimitiveRepresentation

/-! # Scalar weak derivatives of spatial pairings -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.Lions

private theorem cauchyPairingTimeDeriv_hasCompactSupport {θ : ℝ → ℝ}
    (hθc : HasCompactSupport θ) : HasCompactSupport (deriv θ) := by
  apply hasCompactSupport_of_zero_off hθc.isCompact
  intro t ht
  have hD : fderiv ℝ θ t = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => ht (tsupport_fderiv_subset ℝ h))
  simp [deriv, hD]

private theorem cauchyPairingSpaceGrad_hasCompactSupport {d : ℕ} {ψ : Vec d → ℝ}
    (hψc : HasCompactSupport ψ) (i : Fin d) :
    HasCompactSupport (fun x => spaceGradC1 ψ x i) := by
  apply hasCompactSupport_of_zero_off hψc.isCompact
  intro x hx
  have hD : fderiv ℝ ψ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_fderiv_subset ℝ h))
  simp [spaceGradC1, hD]

/-- The spatially tested value of the Lions field has weak time derivative equal to minus
the corresponding flux pairing. This is the interior-time consequence of the tensor identity. -/
theorem cauchyLions_pairing_hasWeakDerivOnIoo
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 (volume : Measure (Vec d)))
    (u : CauchyX d s T)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (ψ : Vec d → ℝ) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    PDE.HasWeakDerivOnIoo s T (cauchyValuePairing u ψ)
      (fun t => -cauchyFluxPairing a u ψ t) := by
  unfold PDE.HasWeakDerivOnIoo
  intro φ hφsmooth hφcompact hφsupport
  let θ : ℝ → ℝ := PDE.scalarPullbackOne φ
  have hθsmooth : ContDiff ℝ 1 θ := PDE.ContDiff.scalarPullbackOne (hφsmooth.of_le (by simp))
  have hθsupport : tsupport θ ⊆ Ioo s T :=
    PDE.tsupport_scalarPullbackOne_subset_Ioo hφsupport
  have hθcompact : HasCompactSupport θ := by
    refine HasCompactSupport.of_support_subset_isCompact (K := Icc s T) isCompact_Icc ?_
    intro t ht
    have ht' : t ∈ tsupport θ := subset_tsupport _ ht
    exact ⟨(hθsupport ht').1.le, (hθsupport ht').2.le⟩
  have hθT : θ T = 0 := by
    have hT : T ∉ tsupport θ := by
      intro hT
      exact (not_lt_of_ge le_rfl) (hθsupport hT).2
    exact image_eq_zero_of_notMem_tsupport hT
  have hθs : θ s = 0 := by
    have hs : s ∉ tsupport θ := by
      intro hs
      exact (not_lt_of_ge le_rfl) (hθsupport hs).1
    exact image_eq_zero_of_notMem_tsupport hs
  have hθdC : Continuous (deriv θ) := hθsmooth.continuous_deriv (by norm_num)
  have hθdcompact := cauchyPairingTimeDeriv_hasCompactSupport hθcompact
  have hψC : Continuous ψ := hψ.continuous
  have hψdC : Continuous (spaceGradC1 ψ) := by
    exact continuous_pi fun i => (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hψdcompact : ∀ i : Fin d, HasCompactSupport (fun x => spaceGradC1 ψ x i) :=
    fun i => cauchyPairingSpaceGrad_hasCompactSupport hψc i
  have htimeTestC : Continuous (fun z : Vec d × ℝ => deriv θ z.2 * ψ z.1) :=
    (hθdC.comp continuous_snd).mul (hψC.comp continuous_fst)
  have htimeTestK : HasCompactSupport (fun z : Vec d × ℝ => deriv θ z.2 * ψ z.1) :=
    PDE.Parabolic.WeakSlice.hasCompactSupport_prod hθdcompact hψc
  have htimeTest : MemLp (fun z : Vec d × ℝ => deriv θ z.2 * ψ z.1) 2
      (slabMeasure d s T) :=
    (htimeTestC.memLp_of_hasCompactSupport htimeTestK).mono_measure Measure.restrict_le_self
  have htimeInt : Integrable
      (fun z => cauchyEnergyValue u z * (deriv θ z.2 * ψ z.1)) (slabMeasure d s T) :=
    (cauchyEnergyValue_memLp u).integrable_mul htimeTest
  have hfluxTestMem : ∀ i : Fin d,
      MemLp (fun z : Vec d × ℝ => θ z.2 * spaceGradC1 ψ z.1 i) 2 (slabMeasure d s T) := by
    intro i
    have hc : Continuous (fun z : Vec d × ℝ => θ z.2 * spaceGradC1 ψ z.1 i) :=
      (hθsmooth.continuous.comp continuous_snd).mul
        ((continuous_apply i).comp (hψdC.comp continuous_fst))
    have hk : HasCompactSupport (fun z : Vec d × ℝ => θ z.2 * spaceGradC1 ψ z.1 i) := by
      let K : Set (Vec d × ℝ) := tsupport (fun x => spaceGradC1 ψ x i) ×ˢ tsupport θ
      have hK : IsCompact K := (hψdcompact i).isCompact.prod hθcompact.isCompact
      apply hasCompactSupport_of_zero_off hK
      intro z hz
      by_cases ht : z.2 ∈ tsupport θ
      · have hx : z.1 ∉ tsupport (fun x => spaceGradC1 ψ x i) := by
          intro hx
          exact hz ⟨hx, ht⟩
        simp [image_eq_zero_of_notMem_tsupport hx]
      · simp [image_eq_zero_of_notMem_tsupport ht]
    exact (hc.memLp_of_hasCompactSupport hk).mono_measure Measure.restrict_le_self
  have hfluxInt : Integrable
      (fun z => vecDot (matVecMul (a z) (cauchyEnergyGradient u z))
        (θ z.2 • spaceGradC1 ψ z.1)) (slabMeasure d s T) := by
    have hsum : Integrable (fun z => ∑ i : Fin d,
        matVecMul (a z) (cauchyEnergyGradient u z) i *
          (θ z.2 * spaceGradC1 ψ z.1 i)) (slabMeasure d s T) :=
      integrable_finsetSum Finset.univ fun i _ =>
        (cauchyEnergyFlux_coord_memLp ha u i).integrable_mul (hfluxTestMem i)
    exact hsum.congr (Filter.Eventually.of_forall fun z => by
      simp [vecDot, Pi.smul_apply, smul_eq_mul])
  have hmeasure : slabMeasure d s T =
      (volume : Measure (Vec d)).prod (volume.restrict (Icc s T)) := by
    rw [slabMeasure, PDE.Parabolic.Energy.volume_restrict_prod, Measure.restrict_univ]
  have htimeIntProd : Integrable
      (fun z : Vec d × ℝ => cauchyEnergyValue u z * (deriv θ z.2 * ψ z.1))
      ((volume : Measure (Vec d)).prod (volume.restrict (Icc s T))) := by
    rw [← hmeasure]
    exact htimeInt
  have hfluxIntProd : Integrable
      (fun z : Vec d × ℝ => vecDot (matVecMul (a z) (cauchyEnergyGradient u z))
        (θ z.2 • spaceGradC1 ψ z.1))
      ((volume : Measure (Vec d)).prod (volume.restrict (Icc s T))) := by
    rw [← hmeasure]
    exact hfluxInt
  have htimeFubini := integral_prod_symm _ htimeIntProd
  have hfluxFubini := integral_prod_symm _ hfluxIntProd
  have htimeFactor : ∀ t : ℝ,
      ∫ x, cauchyEnergyValue u (x, t) * (deriv θ t * ψ x) =
        deriv θ t * cauchyValuePairing u ψ t := by
    intro t
    rw [cauchyValuePairing, ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by ring
  have hfluxFactor : ∀ t : ℝ,
      ∫ x, vecDot (matVecMul (a (x, t)) (cauchyEnergyGradient u (x, t)))
        (θ t • spaceGradC1 ψ x) = θ t * cauchyFluxPairing a u ψ t := by
    intro t
    rw [cauchyFluxPairing, ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp only [vecDot, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
  have htimePairInt : Integrable
      (fun t : ℝ => deriv θ t * cauchyValuePairing u ψ t)
      (volume.restrict (Icc s T)) := by
    have h := htimeIntProd.integral_prod_right
    have heq : (fun t : ℝ =>
        ∫ x, cauchyEnergyValue u (x, t) * (deriv θ t * ψ x)) =
        fun t => deriv θ t * cauchyValuePairing u ψ t := by
      funext t
      exact htimeFactor t
    rw [heq] at h
    exact h
  have hfluxPairInt : Integrable
      (fun t : ℝ => θ t * cauchyFluxPairing a u ψ t)
      (volume.restrict (Icc s T)) := by
    have h := hfluxIntProd.integral_prod_right
    have heq : (fun t : ℝ =>
        ∫ x, vecDot (matVecMul (a (x, t)) (cauchyEnergyGradient u (x, t)))
          (θ t • spaceGradC1 ψ x)) =
        fun t => θ t * cauchyFluxPairing a u ψ t := by
      funext t
      exact hfluxFactor t
    rw [heq] at h
    exact h
  have htensor := cauchyLions_pairing_testIdentity ha f hf u hrep ψ hψ hψc
    θ hθsmooth hθcompact hθT
  have hzero : ∫ t in Icc s T,
      (-(cauchyValuePairing u ψ t * deriv θ t) +
        cauchyFluxPairing a u ψ t * θ t) = 0 := by
    simpa [hθs] using htensor
  have hpairEq : ∫ t in Icc s T, cauchyValuePairing u ψ t * deriv θ t =
      ∫ t in Icc s T, cauchyFluxPairing a u ψ t * θ t := by
    have hzeroSum :
        ∫ t in Icc s T, (-(deriv θ t * cauchyValuePairing u ψ t) +
          θ t * cauchyFluxPairing a u ψ t) =
          -(∫ t in Icc s T, deriv θ t * cauchyValuePairing u ψ t) +
            ∫ t in Icc s T, θ t * cauchyFluxPairing a u ψ t := by
      calc
        _ = (∫ t in Icc s T, -(deriv θ t * cauchyValuePairing u ψ t)) +
            ∫ t in Icc s T, θ t * cauchyFluxPairing a u ψ t :=
          integral_add htimePairInt.neg hfluxPairInt
        _ = _ := by rw [integral_neg]
    have heq :
        ∫ t in Icc s T, (-(cauchyValuePairing u ψ t * deriv θ t) +
          cauchyFluxPairing a u ψ t * θ t) =
          ∫ t in Icc s T, (-(deriv θ t * cauchyValuePairing u ψ t) +
            θ t * cauchyFluxPairing a u ψ t) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by ring
    rw [heq, hzeroSum] at hzero
    have hcomm : ∫ t in Icc s T, deriv θ t * cauchyValuePairing u ψ t =
        ∫ t in Icc s T, cauchyValuePairing u ψ t * deriv θ t := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by ring
    have hcomm' : ∫ t in Icc s T, θ t * cauchyFluxPairing a u ψ t =
        ∫ t in Icc s T, cauchyFluxPairing a u ψ t * θ t := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by ring
    rw [hcomm, hcomm'] at hzero
    linarith
  have hpairEqIoo : ∫ t in Ioo s T, cauchyValuePairing u ψ t * deriv θ t =
      ∫ t in Ioo s T, cauchyFluxPairing a u ψ t * θ t := by
    rw [Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact hpairEq
  have hφOne : ContDiff ℝ 1 φ := hφsmooth.of_le (by simp)
  have hleft :
      (fun x => PDE.liftOneDimensional (cauchyValuePairing u ψ) x *
        (fderiv ℝ φ x) (basisVec (0 : Fin 1))) =
      PDE.liftOneDimensional (fun t => cauchyValuePairing u ψ t * deriv θ t) := by
    funext x
    simp only [PDE.liftOneDimensional]
    rw [← PDE.scalarToVecOne_vecOneCoordinate x]
    dsimp [θ]
    rw [PDE.deriv_scalarPullbackOne_eq_native_directional hφOne
      (PDE.vecOneCoordinate x)]
  have hright :
      (fun x => PDE.liftOneDimensional (fun t => cauchyFluxPairing a u ψ t) x * φ x) =
        PDE.liftOneDimensional
          (fun t => cauchyFluxPairing a u ψ t * θ t) := by
    funext x
    simp only [PDE.liftOneDimensional, θ, PDE.scalarPullbackOne]
    rw [PDE.scalarToVecOne_vecOneCoordinate]
  calc
    (∫ x in PDE.oneDimensionalAxisBox s T,
        PDE.liftOneDimensional (cauchyValuePairing u ψ) x *
          (fderiv ℝ φ x) (basisVec (0 : Fin 1))) =
        ∫ t in Ioo s T, cauchyValuePairing u ψ t * deriv θ t := by
      rw [hleft]
      exact PDE.setIntegral_axisBox_one_eq_setIntegral_Ioo s T
    _ = ∫ t in Ioo s T, cauchyFluxPairing a u ψ t * θ t := hpairEqIoo
    _ = ∫ x in PDE.oneDimensionalAxisBox s T,
        PDE.liftOneDimensional
          (fun t => cauchyFluxPairing a u ψ t * θ t) x := by
      symm
      exact PDE.setIntegral_axisBox_one_eq_setIntegral_Ioo s T
    _ = ∫ x in PDE.oneDimensionalAxisBox s T,
        PDE.liftOneDimensional (fun t => cauchyFluxPairing a u ψ t) x * φ x := by
      congr 1
      funext x
      exact congrFun hright.symm x
    _ = -∫ x in PDE.oneDimensionalAxisBox s T,
        PDE.liftOneDimensional (fun t => -cauchyFluxPairing a u ψ t) x * φ x := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [PDE.liftOneDimensional]
        ring

end PDE.Parabolic.Lions
