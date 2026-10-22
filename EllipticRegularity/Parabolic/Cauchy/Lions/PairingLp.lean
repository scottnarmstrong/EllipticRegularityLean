module

public import EllipticRegularity.Parabolic.Cauchy.Lions.TimePairingIdentity
public import PDEFoundation.Measure.LpPower
public import EllipticRegularity.Parabolic.Energy.Slab

/-! # Time `L²` bounds for spatial pairings -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.Lions

/-- Pairing a slab `L²` field with a fixed spatial `L²` function gives an `L²` function of time.
The estimate is the Hilbert-space Cauchy--Schwarz inequality on almost every spatial slice. -/
theorem cauchySpatialPairing_memLp {d : ℕ} {s T : ℝ}
    {F : Vec d × ℝ → ℝ} (hF : MemLp F 2 (slabMeasure d s T))
    {ψ : Vec d → ℝ} (hψ : MemLp ψ 2 (volume : Measure (Vec d))) :
    MemLp (fun t : ℝ => ∫ x, F (x, t) * ψ x)
      2 (volume.restrict (Icc s T)) := by
  let μt : Measure ℝ := volume.restrict (Icc s T)
  have hmeasure : slabMeasure d s T =
      (volume : Measure (Vec d)).prod μt := by
    rw [slabMeasure, PDE.Parabolic.Energy.volume_restrict_prod, Measure.restrict_univ]
  let Fprod : Vec d × ℝ → ℝ := F
  have hFprod : MemLp Fprod 2 ((volume : Measure (Vec d)).prod μt) := by
    rw [← hmeasure]
    exact hF
  let : IsFiniteMeasure μt := by
    dsimp [μt]
    infer_instance
  have hψprod : MemLp (fun z : Vec d × ℝ => ψ z.1) 2
      ((volume : Measure (Vec d)).prod μt) := hψ.comp_fst μt
  have hproduct : Integrable
      (fun z : Vec d × ℝ => Fprod z * ψ z.1)
      ((volume : Measure (Vec d)).prod μt) := hFprod.integrable_mul hψprod
  have hpairInt : Integrable (fun t : ℝ => ∫ x, Fprod (x, t) * ψ x) μt :=
    hproduct.integral_prod_right
  let S : ℝ → ℝ := fun t => ∫ x, Fprod (x, t) ^ 2
  have hFsq : Integrable (fun z : Vec d × ℝ => Fprod z ^ 2)
      ((volume : Measure (Vec d)).prod μt) := hFprod.integrable_sq
  have hS : Integrable S μt := by
    exact hFsq.integral_prod_right
  let N : ℝ → ℝ := fun t => Real.sqrt (S t)
  have hNmeas : AEStronglyMeasurable N μt := by
    exact Real.continuous_sqrt.comp_aestronglyMeasurable hS.aestronglyMeasurable
  have hSnonneg (t : ℝ) : 0 ≤ S t := by
    exact integral_nonneg fun x => sq_nonneg (Fprod (x, t))
  have hNsq (t : ℝ) : N t ^ 2 = S t := by
    simp [N, Real.sq_sqrt (hSnonneg t)]
  have hNsqInt : Integrable (fun t => N t ^ 2) μt := by
    exact hS.congr (Filter.Eventually.of_forall fun t => (hNsq t).symm)
  have hN : MemLp N 2 μt := (memLp_two_iff_integrable_sq hNmeas).2 hNsqInt
  have hSlice : ∀ᵐ t ∂μt, MemLp (fun x : Vec d => Fprod (x, t)) 2
      (volume : Measure (Vec d)) := by
    have h := PDE.Parabolic.Energy.ae_slice_memLp (d := d) (K1 := (univ : Set (Vec d)))
      (J := Icc s T) (g := Fprod) MeasurableSet.univ hF
    filter_upwards [h] with t ht
    simpa [μt, Fprod] using ht
  have hbound : ∀ᵐ t ∂μt,
      ‖∫ x, Fprod (x, t) * ψ x‖ ≤ ‖hψ.toLp ψ‖ * ‖N t‖ := by
    filter_upwards [hSlice] with t ht
    let ft : Lp ℝ 2 (volume : Measure (Vec d)) := ht.toLp (fun x => Fprod (x, t))
    have hinner :
        (∫ x, Fprod (x, t) * ψ x) = inner ℝ ft (hψ.toLp ψ) := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [ht.coeFn_toLp, hψ.coeFn_toLp] with x hx hψx
      rw [hx, hψx]
      change Fprod (x, t) * ψ x = ψ x * Fprod (x, t)
      ring
    have hnorm : ‖ft‖ = N t := by
      change ‖ht.toLp (fun x => Fprod (x, t))‖ = N t
      rw [Lp.norm_toLp]
      have hsq := PDE.toReal_eLpNorm_two_sq_eq_integral_sq ht
      have hnormnonneg :
          0 ≤ (eLpNorm (fun x => Fprod (x, t)) 2 volume).toReal := ENNReal.toReal_nonneg
      dsimp [N, S]
      symm
      rw [Real.sqrt_eq_iff_eq_sq
        (integral_nonneg fun x => sq_nonneg (Fprod (x, t))) hnormnonneg]
      exact hsq.symm
    rw [Real.norm_eq_abs, hinner]
    calc
      |inner ℝ ft (hψ.toLp ψ)| ≤ ‖ft‖ * ‖hψ.toLp ψ‖ := abs_real_inner_le_norm _ _
      _ = N t * ‖hψ.toLp ψ‖ := by rw [hnorm]
      _ = ‖hψ.toLp ψ‖ * ‖N t‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        ring
  exact hN.of_le_mul (c := ‖hψ.toLp ψ‖) hpairInt.aestronglyMeasurable hbound

/-- The flux pairing against a fixed smooth compactly supported spatial test is square integrable
in time. The proof expands the finite-dimensional dot product into scalar pairings. -/
theorem cauchyFluxPairing_memLp {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (u : CauchyX d s T)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    MemLp (cauchyFluxPairing a u ψ) 2 (volume.restrict (Icc s T)) := by
  let μt : Measure ℝ := volume.restrict (Icc s T)
  have hmeasure : slabMeasure d s T =
      (volume : Measure (Vec d)).prod μt := by
    rw [slabMeasure, PDE.Parabolic.Energy.volume_restrict_prod, Measure.restrict_univ]
  let : IsFiniteMeasure μt := by
    dsimp [μt]
    infer_instance
  have hψcont : Continuous (spaceGradC1 ψ) := by
    exact continuous_pi fun i => (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hψcomp : ∀ i : Fin d, HasCompactSupport (fun x => spaceGradC1 ψ x i) := by
    intro i
    apply hasCompactSupport_of_zero_off hψc.isCompact
    intro x hx
    have hD : fderiv ℝ ψ x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_fderiv_subset ℝ h))
    simp [spaceGradC1, hD]
  let Pi : Fin d → ℝ → ℝ := fun i t =>
    ∫ x, matVecMul (a (x, t)) (cauchyEnergyGradient u (x, t)) i * spaceGradC1 ψ x i
  have hPi : ∀ i : Fin d, MemLp (Pi i) 2 μt := by
    intro i
    have hψi : MemLp (fun x => spaceGradC1 ψ x i) 2 (volume : Measure (Vec d)) :=
      (continuous_apply i).comp hψcont |>.memLp_of_hasCompactSupport (hψcomp i)
    have hfluxi : MemLp
        (fun z => matVecMul (a z) (cauchyEnergyGradient u z) i) 2 (slabMeasure d s T) :=
      cauchyEnergyFlux_coord_memLp ha u i
    exact cauchySpatialPairing_memLp hfluxi hψi
  have hproducts : ∀ i : Fin d, Integrable
      (fun z : Vec d × ℝ =>
        matVecMul (a z) (cauchyEnergyGradient u z) i * spaceGradC1 ψ z.1 i)
      ((volume : Measure (Vec d)).prod μt) := by
    intro i
    have hψi : MemLp (fun x => spaceGradC1 ψ x i) 2 (volume : Measure (Vec d)) :=
      (continuous_apply i).comp hψcont |>.memLp_of_hasCompactSupport (hψcomp i)
    have hψiprod := hψi.comp_fst μt
    have hfluxi : MemLp
        (fun z => matVecMul (a z) (cauchyEnergyGradient u z) i) 2 (slabMeasure d s T) :=
      cauchyEnergyFlux_coord_memLp ha u i
    have hfluxiprod : MemLp
        (fun z => matVecMul (a z) (cauchyEnergyGradient u z) i) 2
          ((volume : Measure (Vec d)).prod μt) := by
      rw [← hmeasure]
      exact hfluxi
    exact hfluxiprod.integrable_mul hψiprod
  have hsections : ∀ᵐ t ∂μt, ∀ i : Fin d, Integrable
      (fun x : Vec d =>
        matVecMul (a (x, t)) (cauchyEnergyGradient u (x, t)) i * spaceGradC1 ψ x i)
      (volume : Measure (Vec d)) := by
    rw [ae_all_iff]
    intro i
    exact (hproducts i).prod_left_ae
  have hsum : MemLp (fun t => ∑ i : Fin d, Pi i t) 2 μt :=
    memLp_finsetSum _ fun i _ => hPi i
  have hpairAe : cauchyFluxPairing a u ψ =ᵐ[μt] fun t => ∑ i : Fin d, Pi i t := by
    filter_upwards [hsections] with t ht
    have hsumInt : Integrable (fun x : Vec d => ∑ i : Fin d,
        matVecMul (a (x, t)) (cauchyEnergyGradient u (x, t)) i * spaceGradC1 ψ x i)
        (volume : Measure (Vec d)) :=
      integrable_finsetSum Finset.univ fun i hi => ht i
    have hdot : (fun x : Vec d => vecDot
        (matVecMul (a (x, t)) (cauchyEnergyGradient u (x, t))) (spaceGradC1 ψ x)) =
        fun x => ∑ i : Fin d,
          matVecMul (a (x, t)) (cauchyEnergyGradient u (x, t)) i * spaceGradC1 ψ x i := by
      funext x
      rfl
    change (∫ x, vecDot
      (matVecMul (a (x, t)) (cauchyEnergyGradient u (x, t))) (spaceGradC1 ψ x)) = _
    rw [hdot, integral_finsetSum Finset.univ (fun i hi => ht i)]
  exact (memLp_congr_ae hpairAe).2 hsum

end PDE.Parabolic.Lions
