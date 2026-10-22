module

public import EllipticRegularity.Parabolic.Cauchy.Lions.PairingLp

/-! # Quantitative time-integrated spatial pairings -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.Lions

/-- The time integral of the absolute spatial pairing is bounded by the spatial test norm times
the time integral of the slice `L²` norm. This form keeps the field-dependent factor independent
of the test and is useful for translated mollifier kernels. -/
theorem cauchySpatialPairing_integral_abs_le {d : ℕ} {s T : ℝ}
    {F : Vec d × ℝ → ℝ} (hF : MemLp F 2 (slabMeasure d s T))
    {ψ : Vec d → ℝ} (hψ : MemLp ψ 2 (volume : Measure (Vec d))) :
    (∫ t, |∫ x, F (x, t) * ψ x| ∂(volume.restrict (Icc s T))) ≤
      ‖hψ.toLp ψ‖ *
        ∫ t, Real.sqrt (∫ x, F (x, t) ^ 2) ∂(volume.restrict (Icc s T)) := by
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
  have hS : Integrable S μt := hFsq.integral_prod_right
  let N : ℝ → ℝ := fun t => Real.sqrt (S t)
  have hNmeas : AEStronglyMeasurable N μt := by
    exact Real.continuous_sqrt.comp_aestronglyMeasurable hS.aestronglyMeasurable
  have hSnonneg (t : ℝ) : 0 ≤ S t := by
    exact integral_nonneg fun x => sq_nonneg (Fprod (x, t))
  have hNsq (t : ℝ) : N t ^ 2 = S t := by
    simp [N, Real.sq_sqrt (hSnonneg t)]
  have hN : MemLp N 2 μt := by
    have hNsqInt : Integrable (fun t => N t ^ 2) μt :=
      hS.congr (Filter.Eventually.of_forall fun t => (hNsq t).symm)
    exact (memLp_two_iff_integrable_sq hNmeas).2 hNsqInt
  have hSlice : ∀ᵐ t ∂μt, MemLp (fun x : Vec d => Fprod (x, t)) 2
      (volume : Measure (Vec d)) := by
    have h := PDE.Parabolic.Energy.ae_slice_memLp (d := d) (K1 := (univ : Set (Vec d)))
      (J := Icc s T) (g := Fprod) MeasurableSet.univ hF
    filter_upwards [h] with t ht
    simpa [μt, Fprod] using ht
  have hbound : ∀ᵐ t ∂μt,
      |∫ x, Fprod (x, t) * ψ x| ≤ ‖hψ.toLp ψ‖ * N t := by
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
    rw [hinner]
    calc
      |inner ℝ ft (hψ.toLp ψ)| ≤ ‖ft‖ * ‖hψ.toLp ψ‖ := abs_real_inner_le_norm _ _
      _ = N t * ‖hψ.toLp ψ‖ := by rw [hnorm]
      _ = ‖hψ.toLp ψ‖ * N t := by ring
  have hRHS : Integrable (fun t => ‖hψ.toLp ψ‖ * N t) μt := by
    exact (hN.integrable (by norm_num)).const_mul _
  calc
    (∫ t, |∫ x, F (x, t) * ψ x| ∂μt) ≤
        ∫ t, ‖hψ.toLp ψ‖ * N t ∂μt := by
          apply integral_mono_ae hpairInt.abs hRHS
          filter_upwards [hbound] with t ht
          simpa [Fprod] using ht
    _ = ‖hψ.toLp ψ‖ * ∫ t, N t ∂μt := by rw [integral_const_mul]
  
end PDE.Parabolic.Lions
