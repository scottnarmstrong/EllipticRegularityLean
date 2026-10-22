module

public import EllipticRegularity.Parabolic.Cauchy.Lions.KernelNorm
public import EllipticRegularity.Parabolic.Cauchy.Lions.PairingEstimate

/-! # Uniform time-integrability of centered mollifier flux pairings -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.Lions

/-- A coordinate derivative of a compactly supported `C¹` test is in spatial `L²`. -/
theorem cauchyGradientTest_memLp {d : ℕ} {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (i : Fin d) :
    MemLp (fun x => spaceGradC1 ψ x i) 2 (volume : Measure (Vec d)) := by
  have hcont : Continuous (spaceGradC1 ψ) := by
    exact continuous_pi fun j =>
      (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcompact : HasCompactSupport (fun x => spaceGradC1 ψ x i) := by
    apply hasCompactSupport_of_zero_off hψc.isCompact
    intro x hx
    have hD : fderiv ℝ ψ x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_fderiv_subset ℝ h))
    simp [spaceGradC1, hD]
  exact ((continuous_apply i).comp hcont).memLp_of_hasCompactSupport hcompact

/-- The `L²` element represented by one coordinate derivative of a test. -/
noncomputable def cauchyGradientTestLp {d : ℕ} {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (i : Fin d) :
    Lp ℝ 2 (volume : Measure (Vec d)) :=
  (cauchyGradientTest_memLp hψ hψc i).toLp (fun x => spaceGradC1 ψ x i)

/-- The absolute time integral of a flux pairing has an explicit coordinatewise bound. -/
theorem cauchyFluxPairing_integral_abs_le {d : ℕ} {lam Lam s T : ℝ}
    {a : ParCoeffField d} (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (u : CauchyX d s T) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    (∫ t, |cauchyFluxPairing a u ψ t| ∂(volume.restrict (Icc s T))) ≤
      ∑ i : Fin d,
        ‖cauchyGradientTestLp hψ hψc i‖ *
          ∫ t, Real.sqrt (∫ x, (matVecMul (a (x, t))
            (cauchyEnergyGradient u (x, t)) i) ^ 2) ∂(volume.restrict (Icc s T)) := by
  let μt : Measure ℝ := volume.restrict (Icc s T)
  let G : Vec d × ℝ → Vec d := fun z =>
    matVecMul (a z) (cauchyEnergyGradient u z)
  have hmeasure : slabMeasure d s T =
      (volume : Measure (Vec d)).prod μt := by
    rw [slabMeasure, PDE.Parabolic.Energy.volume_restrict_prod, Measure.restrict_univ]
  let : IsFiniteMeasure μt := by
    dsimp [μt]
    infer_instance
  have hgradmem : ∀ i : Fin d,
      MemLp (fun x => spaceGradC1 ψ x i) 2 (volume : Measure (Vec d)) := by
    intro i
    exact cauchyGradientTest_memLp hψ hψc i
  have hfluxmem : ∀ i : Fin d,
      MemLp (fun z => G z i) 2 (slabMeasure d s T) := by
    intro i
    exact cauchyEnergyFlux_coord_memLp ha u i
  let Pi : Fin d → ℝ → ℝ := fun i t =>
    ∫ x, G (x, t) i * spaceGradC1 ψ x i
  have hPi : ∀ i : Fin d, MemLp (Pi i) 2 μt := by
    intro i
    have h := cauchySpatialPairing_memLp (hfluxmem i) (hgradmem i)
    simpa [Pi, G, μt] using h
  have hpairAe : cauchyFluxPairing a u ψ =ᵐ[μt] fun t => ∑ i : Fin d, Pi i t := by
    have hproducts : ∀ i : Fin d, Integrable
        (fun z : Vec d × ℝ => G z i * spaceGradC1 ψ z.1 i)
        ((volume : Measure (Vec d)).prod μt) := by
      intro i
      have hprod : MemLp (fun z : Vec d × ℝ => G z i) 2
          ((volume : Measure (Vec d)).prod μt) := by
        rw [← hmeasure]
        exact hfluxmem i
      exact hprod.integrable_mul ((hgradmem i).comp_fst μt)
    have hsections : ∀ᵐ t ∂μt, ∀ i : Fin d,
        Integrable (fun x : Vec d => G (x, t) i * spaceGradC1 ψ x i)
          (volume : Measure (Vec d)) := by
      rw [ae_all_iff]
      intro i
      exact (hproducts i).prod_left_ae
    filter_upwards [hsections] with t ht
    have hsumInt : Integrable (fun x : Vec d => ∑ i : Fin d,
        G (x, t) i * spaceGradC1 ψ x i) (volume : Measure (Vec d)) :=
      integrable_finsetSum Finset.univ fun i _ => ht i
    have hdot : (fun x : Vec d => vecDot (G (x, t)) (spaceGradC1 ψ x)) =
        fun x => ∑ i : Fin d, G (x, t) i * spaceGradC1 ψ x i := by
      funext x
      rfl
    change (∫ x, vecDot (G (x, t)) (spaceGradC1 ψ x)) = _
    rw [hdot, integral_finsetSum Finset.univ (fun i hi => ht i)]
  have hpairsum : MemLp (fun t => ∑ i : Fin d, Pi i t) 2 μt :=
    memLp_finsetSum _ fun i _ => hPi i
  have hpairmem : MemLp (cauchyFluxPairing a u ψ) 2 μt :=
    (memLp_congr_ae hpairAe).2 hpairsum
  have hpairint : Integrable (cauchyFluxPairing a u ψ) μt :=
    hpairmem.integrable (by norm_num)
  have hsumabs : Integrable (fun t => ∑ i : Fin d, |Pi i t|) μt :=
    integrable_finsetSum _ fun i _ => ((hPi i).integrable (by norm_num)).abs
  have htriangle :
      (∫ t, |cauchyFluxPairing a u ψ t| ∂μt) ≤
        ∫ t, ∑ i : Fin d, |Pi i t| ∂μt := by
    apply integral_mono_ae hpairint.abs hsumabs
    filter_upwards [hpairAe] with t ht
    rw [ht]
    exact Finset.abs_sum_le_sum_abs _ _
  calc
    (∫ t, |cauchyFluxPairing a u ψ t| ∂μt) ≤
        ∑ i : Fin d, ∫ t, |Pi i t| ∂μt := by
          rw [integral_finsetSum Finset.univ (fun i hi =>
            ((hPi i).integrable (by norm_num)).abs)] at htriangle
          exact htriangle
    _ ≤ ∑ i : Fin d,
        ‖cauchyGradientTestLp hψ hψc i‖ *
          ∫ t, Real.sqrt (∫ x, (G (x, t) i) ^ 2) ∂μt := by
          apply Finset.sum_le_sum
          intro i hi
          have h := cauchySpatialPairing_integral_abs_le (hfluxmem i) (hgradmem i)
          simpa [Pi, G, μt, cauchyGradientTestLp] using h

/-- A centered mollifier-test flux has an absolute time-integral bound independent of its center.
The right side depends only on the spacetime flux and on the kernel at the origin. -/
theorem cauchyKernelFluxPairing_integral_abs_le {d : ℕ} {lam Lam s T a : ℝ}
    {A : ParCoeffField d} (ha : IsParabolicCoeff lam Lam A univ (Icc s T))
    (haε : 0 < a) (u : CauchyX d s T) (x : Vec d) :
    (∫ t, |cauchyFluxPairing A u (cauchyKernelTest a x) t|
        ∂(volume.restrict (Icc s T))) ≤
      ∑ i : Fin d,
        ‖cauchyGradientTestLp
          (cauchyKernelTest_contDiff_one a (0 : Vec d))
          (cauchyKernelTest_hasCompactSupport haε (0 : Vec d)) i‖ *
          ∫ t, Real.sqrt (∫ y, (matVecMul (A (y, t))
            (cauchyEnergyGradient u (y, t)) i) ^ 2)
            ∂(volume.restrict (Icc s T)) := by
  have hkernelx : ContDiff ℝ 1 (cauchyKernelTest a x) :=
    cauchyKernelTest_contDiff_one a x
  have hkernelcx : HasCompactSupport (cauchyKernelTest a x) :=
    cauchyKernelTest_hasCompactSupport haε x
  have hkernel0 : ContDiff ℝ 1 (cauchyKernelTest a (0 : Vec d)) :=
    cauchyKernelTest_contDiff_one a (0 : Vec d)
  have hkernelc0 : HasCompactSupport (cauchyKernelTest a (0 : Vec d)) :=
    cauchyKernelTest_hasCompactSupport haε (0 : Vec d)
  have h := cauchyFluxPairing_integral_abs_le ha u hkernelx hkernelcx
  have hnorm (i : Fin d) :
      ‖cauchyGradientTestLp hkernelx hkernelcx i‖ =
        ‖cauchyGradientTestLp hkernel0 hkernelc0 i‖ := by
    exact cauchyKernelTest_spaceGrad_norm_eq i x
      (cauchyGradientTest_memLp hkernelx hkernelcx i)
      (cauchyGradientTest_memLp hkernel0 hkernelc0 i)
  simpa [hnorm] using h

end PDE.Parabolic.Lions
