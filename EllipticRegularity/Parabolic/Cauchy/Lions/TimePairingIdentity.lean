module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.Lions.EnergyFields

/-! # Tensor-test identities as scalar time identities -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.Lions

/-- The spatial pairing of a Lions energy value with a fixed spatial test. -/
noncomputable def cauchyValuePairing {d : ℕ} {s T : ℝ} (u : CauchyX d s T)
    (ψ : Vec d → ℝ) (t : ℝ) : ℝ :=
  ∫ x, cauchyEnergyValue u (x, t) * ψ x

/-- The spatial flux pairing of a Lions energy gradient with a fixed spatial test. -/
noncomputable def cauchyFluxPairing {d : ℕ} {s T : ℝ} (a : ParCoeffField d)
    (u : CauchyX d s T) (ψ : Vec d → ℝ) (t : ℝ) : ℝ :=
  ∫ x, vecDot (matVecMul (a (x, t)) (cauchyEnergyGradient u (x, t)))
    (spaceGradC1 ψ x)

private theorem cauchyTimeDeriv_hasCompactSupport {θ : ℝ → ℝ}
    (hθc : HasCompactSupport θ) :
    HasCompactSupport (deriv θ) := by
  apply hasCompactSupport_of_zero_off hθc.isCompact
  intro t ht
  have hD : fderiv ℝ θ t = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => ht (tsupport_fderiv_subset ℝ h))
  simp [deriv, hD]

private theorem cauchySpaceGrad_coord_hasCompactSupport {d : ℕ} {ψ : Vec d → ℝ}
    (hψc : HasCompactSupport ψ) (i : Fin d) :
    HasCompactSupport (fun x => spaceGradC1 ψ x i) := by
  apply hasCompactSupport_of_zero_off hψc.isCompact
  intro x hx
  have hD : fderiv ℝ ψ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_fderiv_subset ℝ h))
  simp [spaceGradC1, hD]

/-- For each smooth compactly supported spatial test, the Lions tensor-test identity is the
corresponding scalar weak time identity, including the initial datum. The integrals defining the
pairings are Bochner integrals; no choice of values on exceptional time slices is made here. -/
theorem cauchyLions_pairing_testIdentity {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 (volume : Measure (Vec d)))
    (u : CauchyX d s T)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (ψ : Vec d → ℝ) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (θ : ℝ → ℝ) (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hθT : θ T = 0) :
    ∫ t in Icc s T,
      (-(cauchyValuePairing u ψ t * deriv θ t) +
        cauchyFluxPairing a u ψ t * θ t) =
      θ s * ∫ x, f x * ψ x := by
  have hθdC : Continuous (deriv θ) := hθ.continuous_deriv (by norm_num)
  have hθdK := cauchyTimeDeriv_hasCompactSupport hθc
  have hψC : Continuous ψ := hψ.continuous
  have hψdC : Continuous (spaceGradC1 ψ) := by
    exact continuous_pi fun i => (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hψdK : ∀ i : Fin d, HasCompactSupport (fun x => spaceGradC1 ψ x i) :=
    fun i => cauchySpaceGrad_coord_hasCompactSupport hψc i
  have htimeTestC : Continuous (fun z : Vec d × ℝ => deriv θ z.2 * ψ z.1) :=
    (hθdC.comp continuous_snd).mul (hψC.comp continuous_fst)
  have htimeTestK : HasCompactSupport (fun z : Vec d × ℝ => deriv θ z.2 * ψ z.1) :=
    PDE.Parabolic.WeakSlice.hasCompactSupport_prod hθdK hψc
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
      (hθ.continuous.comp continuous_snd).mul
        ((continuous_apply i).comp (hψdC.comp continuous_fst))
    have hk : HasCompactSupport (fun z : Vec d × ℝ => θ z.2 * spaceGradC1 ψ z.1 i) := by
      let K : Set (Vec d × ℝ) := tsupport (fun x => spaceGradC1 ψ x i) ×ˢ tsupport θ
      have hK : IsCompact K := (hψdK i).isCompact.prod hθc.isCompact
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
      simp [vecDot, Pi.smul_apply, smul_eq_mul]
      )
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
  have htensor := cauchyLions_tensorTestIdentity ha f hf u hrep ψ hψ hψc θ hθ hθc hθT
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
  have htimeFubini' :
      ∫ z, cauchyEnergyValue u z * (deriv θ z.2 * ψ z.1) ∂slabMeasure d s T =
        ∫ t in Icc s T, deriv θ t * cauchyValuePairing u ψ t := by
    calc
      ∫ z, cauchyEnergyValue u z * (deriv θ z.2 * ψ z.1) ∂slabMeasure d s T =
          ∫ z, cauchyEnergyValue u z * (deriv θ z.2 * ψ z.1)
            ∂((volume : Measure (Vec d)).prod (volume.restrict (Icc s T))) := by rw [hmeasure]
      _ = ∫ t in Icc s T, ∫ x, cauchyEnergyValue u (x, t) * (deriv θ t * ψ x) := htimeFubini
      _ = ∫ t in Icc s T, deriv θ t * cauchyValuePairing u ψ t := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun t => by simpa using htimeFactor t
  have hfluxFubini' :
      ∫ z, vecDot (matVecMul (a z) (cauchyEnergyGradient u z))
        (θ z.2 • spaceGradC1 ψ z.1) ∂slabMeasure d s T =
        ∫ t in Icc s T, θ t * cauchyFluxPairing a u ψ t := by
    calc
      ∫ z, vecDot (matVecMul (a z) (cauchyEnergyGradient u z))
          (θ z.2 • spaceGradC1 ψ z.1) ∂slabMeasure d s T =
        ∫ z, vecDot (matVecMul (a z) (cauchyEnergyGradient u z))
          (θ z.2 • spaceGradC1 ψ z.1)
          ∂((volume : Measure (Vec d)).prod (volume.restrict (Icc s T))) := by rw [hmeasure]
      _ = ∫ t in Icc s T,
          ∫ x, vecDot (matVecMul (a (x, t)) (cauchyEnergyGradient u (x, t)))
            (θ t • spaceGradC1 ψ x) := hfluxFubini
      _ = ∫ t in Icc s T, θ t * cauchyFluxPairing a u ψ t := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun t => by simpa using hfluxFactor t
  have htimeNeg :
      ∫ z, -(cauchyEnergyValue u z * (deriv θ z.2 * ψ z.1)) ∂slabMeasure d s T =
        ∫ t in Icc s T, -(cauchyValuePairing u ψ t * deriv θ t) := by
    calc
      _ = -(∫ z, cauchyEnergyValue u z * (deriv θ z.2 * ψ z.1) ∂slabMeasure d s T) :=
        integral_neg _
      _ = -(∫ t in Icc s T, deriv θ t * cauchyValuePairing u ψ t) := by rw [htimeFubini']
      _ = _ := by rw [← integral_neg]; apply integral_congr_ae; exact Filter.Eventually.of_forall fun t => by ring
  have hslabIdentity :
      ∫ z in (univ : Set (Vec d)) ×ˢ Icc s T,
        (-(cauchyEnergyValue u z * (deriv θ z.2 * ψ z.1)) +
          vecDot (matVecMul (a z) (cauchyEnergyGradient u z))
            (θ z.2 • spaceGradC1 ψ z.1)) =
      ∫ t in Icc s T,
        (-(cauchyValuePairing u ψ t * deriv θ t) +
          cauchyFluxPairing a u ψ t * θ t) := by
    change ∫ z, _ ∂slabMeasure d s T = _
    have htimePair : Integrable (fun t : ℝ => cauchyValuePairing u ψ t * deriv θ t)
        (volume.restrict (Icc s T)) := by
      have h := htimeIntProd.integral_prod_right
      have heq : (fun t : ℝ =>
          ∫ x, cauchyEnergyValue u (x, t) * (deriv θ t * ψ x)) =
          fun t => deriv θ t * cauchyValuePairing u ψ t := by
        funext t
        exact htimeFactor t
      rw [heq] at h
      exact h.congr (Filter.Eventually.of_forall fun t => by ring)
    have hfluxPair : Integrable (fun t : ℝ => θ t * cauchyFluxPairing a u ψ t)
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
    calc
      ∫ z, (-(cauchyEnergyValue u z * (deriv θ z.2 * ψ z.1)) +
          vecDot (matVecMul (a z) (cauchyEnergyGradient u z))
            (θ z.2 • spaceGradC1 ψ z.1)) ∂slabMeasure d s T =
        (∫ z, -(cauchyEnergyValue u z * (deriv θ z.2 * ψ z.1)) ∂slabMeasure d s T) +
          ∫ z, vecDot (matVecMul (a z) (cauchyEnergyGradient u z))
            (θ z.2 • spaceGradC1 ψ z.1) ∂slabMeasure d s T :=
        integral_add htimeInt.neg hfluxInt
      _ = (∫ t in Icc s T, -(cauchyValuePairing u ψ t * deriv θ t)) +
          ∫ t in Icc s T, θ t * cauchyFluxPairing a u ψ t := by rw [htimeNeg, hfluxFubini']
      _ = ∫ t in Icc s T,
          (-(cauchyValuePairing u ψ t * deriv θ t) +
            cauchyFluxPairing a u ψ t * θ t) := by
        calc
          _ = ∫ t in Icc s T,
              (-(cauchyValuePairing u ψ t * deriv θ t) +
                θ t * cauchyFluxPairing a u ψ t) :=
              (integral_add htimePair.neg hfluxPair).symm
          _ = _ := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun t => by ring
  have htensor' :
      ∫ z in (univ : Set (Vec d)) ×ˢ Icc s T,
        (-(cauchyEnergyValue u z * (deriv θ z.2 * ψ z.1)) +
          vecDot (matVecMul (a z) (cauchyEnergyGradient u z))
            (θ z.2 • spaceGradC1 ψ z.1)) =
      θ s * ∫ x, f x * ψ x := by
    calc
      _ = ∫ x, f x * (θ s * ψ x) := by
        simpa only [PDE.Parabolic.WeakSlice.vecDot_smul_right'] using htensor
      _ = θ s * ∫ x, f x * ψ x := by
        calc
          ∫ x, f x * (θ s * ψ x) = ∫ x, θ s * (f x * ψ x) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x => by ring
          _ = θ s * ∫ x, f x * ψ x := integral_const_mul _ _
  rw [hslabIdentity] at htensor'
  exact htensor'

end PDE.Parabolic.Lions
