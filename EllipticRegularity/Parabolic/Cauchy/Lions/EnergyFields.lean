module

public import EllipticRegularity.Parabolic.Cauchy.Lions.WeakEquation

/-! # Energy-space fields after removing the Lions damping -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.Lions

private theorem cauchyWeight_bound_on_slab {d : ℕ} {s T : ℝ}
    {z : Vec d × ℝ} (hz : z ∈ (univ : Set (Vec d)) ×ˢ Icc s T) :
    ‖cauchyWeight (s := s) z‖ ≤ Real.exp (T - s) := by
  change |Real.exp (z.2 - s)| ≤ Real.exp (T - s)
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact sub_le_sub_right hz.2.2 s

/-- The exponentially rescaled value field is square integrable on the finite Cauchy slab. -/
theorem cauchyEnergyValue_memLp {d : ℕ} {s T : ℝ} (u : CauchyX d s T) :
    MemLp (cauchyEnergyValue u) 2 (slabMeasure d s T) := by
  have hbase := cauchyJointValue_memLp u
  have hweight : AEMeasurable (cauchyWeight (s := s)) (slabMeasure d s T) :=
    (Real.continuous_exp.comp (continuous_snd.sub continuous_const)).measurable.aemeasurable
  rw [show cauchyEnergyValue u = fun z =>
      cauchyWeight (s := s) z * cauchyJointValue u z by rfl]
  refine hbase.of_le_mul (c := Real.exp (T - s)) ?_ ?_
  · exact hweight.aestronglyMeasurable.mul hbase.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Icc)] with z hz
    rw [Real.norm_eq_abs, abs_mul]
    simpa only [Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_right (cauchyWeight_bound_on_slab hz)
        (norm_nonneg (cauchyJointValue u z))

/-- The rescaled value slices are globally `L²` for almost every time. -/
theorem cauchyEnergyValue_ae_sliceMemLp {d : ℕ} {s T : ℝ} (u : CauchyX d s T) :
    ∀ᵐ t ∂(volume.restrict (Icc s T)),
      MemLp (fun x : Vec d => cauchyEnergyValue u (x, t)) 2
        (volume : Measure (Vec d)) := by
  have h := PDE.Parabolic.Energy.ae_slice_memLp (d := d) (K1 := (univ : Set (Vec d)))
    (J := Icc s T) (g := cauchyEnergyValue u) MeasurableSet.univ
    (cauchyEnergyValue_memLp u)
  filter_upwards [h] with t ht
  simpa using ht

/-- Each coordinate of the exponentially rescaled spatial gradient is square integrable on the
finite Cauchy slab. -/
theorem cauchyEnergyGradient_coord_memLp {d : ℕ} {s T : ℝ}
    (u : CauchyX d s T) (i : Fin d) :
    MemLp (fun z => cauchyEnergyGradient u z i) 2 (slabMeasure d s T) := by
  have hbase := cauchyJointGradient_memLp u i
  have hweight : AEMeasurable (cauchyWeight (s := s)) (slabMeasure d s T) :=
    (Real.continuous_exp.comp (continuous_snd.sub continuous_const)).measurable.aemeasurable
  change MemLp (fun z => cauchyWeight (s := s) z * cauchyJointGradient u z i)
    2 (slabMeasure d s T)
  refine hbase.of_le_mul (c := Real.exp (T - s)) ?_ ?_
  · exact hweight.aestronglyMeasurable.mul hbase.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Icc)] with z hz
    rw [Real.norm_eq_abs, abs_mul]
    simpa only [Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_right (cauchyWeight_bound_on_slab hz)
        (norm_nonneg (cauchyJointGradient u z i))

/-- Bounded measurable coefficients preserve the slab `L²` bound of the energy gradient after
applying the coefficient matrix. -/
theorem cauchyEnergyFlux_coord_memLp {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (u : CauchyX d s T) (i : Fin d) :
    MemLp (fun z => matVecMul (a z) (cauchyEnergyGradient u z) i) 2
      (slabMeasure d s T) := by
  rw [show slabMeasure d s T = volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s T) by rfl]
  simp only [matVecMul]
  refine memLp_finsetSum _ fun j _ => ?_
  have hgrad := cauchyEnergyGradient_coord_memLp u j
  have hcoeff : AEMeasurable (fun z : Vec d × ℝ => a z i j)
      (volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s T)) := ha.measurable i j
  refine hgrad.of_le_mul (c := |Lam|)
    (hcoeff.aestronglyMeasurable.mul hgrad.aestronglyMeasurable) ?_
  filter_upwards [ha.elliptic] with z hz
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right
    ((PDE.Parabolic.WeakSlice.matrix_abs_entry_le hz i j).trans (le_abs_self Lam))
    (abs_nonneg _)

private theorem cauchyParTestTime_memLp {d : ℕ} {s T : ℝ}
    (φ : ParTestFunction (univ : Set (Vec d)) (interior (Icc s T))) :
    MemLp (parTimeDeriv φ.toFun) 2 (slabMeasure d s T) := by
  have hc : Continuous (parTimeDeriv φ.toFun) := continuous_parTimeDeriv φ.contDiff
  have hK : HasCompactSupport (parTimeDeriv φ.toFun) := by
    apply hasCompactSupport_of_zero_off φ.hasCompactSupport.isCompact
    intro z hz
    have hD : fderiv ℝ φ.toFun z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hmem => hz (tsupport_fderiv_subset ℝ hmem))
    simp [parTimeDeriv, hD]
  exact (hc.memLp_of_hasCompactSupport hK).mono_measure Measure.restrict_le_self

private theorem cauchyParTestSpaceGrad_coord_memLp {d : ℕ} {s T : ℝ}
    (φ : ParTestFunction (univ : Set (Vec d)) (interior (Icc s T))) (i : Fin d) :
    MemLp (fun z => parSpaceGrad φ.toFun z i) 2 (slabMeasure d s T) := by
  have hc : Continuous (fun z => parSpaceGrad φ.toFun z i) :=
    (continuous_apply i).comp (continuous_parSpaceGrad φ.contDiff)
  have hK : HasCompactSupport (fun z => parSpaceGrad φ.toFun z i) := by
    apply hasCompactSupport_of_zero_off φ.hasCompactSupport.isCompact
    intro z hz
    have hD : fderiv ℝ φ.toFun z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hmem => hz (tsupport_fderiv_subset ℝ hmem))
    simp [parSpaceGrad, hD]
  exact (hc.memLp_of_hasCompactSupport hK).mono_measure Measure.restrict_le_self

/-- The full undamped weak integrand for a compactly supported interior test is integrable. -/
theorem cauchyEnergy_weakIntegrand_integrable {d : ℕ} {lam Lam s T : ℝ}
    {a : ParCoeffField d} (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (u : CauchyX d s T) (φ : ParTestFunction (univ : Set (Vec d)) (interior (Icc s T))) :
    Integrable (fun z =>
      -(cauchyEnergyValue u z * parTimeDeriv φ.toFun z) +
        vecDot (matVecMul (a z) (cauchyEnergyGradient u z)) (parSpaceGrad φ.toFun z))
      (slabMeasure d s T) := by
  have htime : Integrable (fun z => cauchyEnergyValue u z * parTimeDeriv φ.toFun z)
      (slabMeasure d s T) :=
    (cauchyEnergyValue_memLp u).integrable_mul (cauchyParTestTime_memLp φ)
  have hflux : ∀ i : Fin d, Integrable
      (fun z => matVecMul (a z) (cauchyEnergyGradient u z) i * parSpaceGrad φ.toFun z i)
      (slabMeasure d s T) := fun i =>
    (cauchyEnergyFlux_coord_memLp ha u i).integrable_mul
      (cauchyParTestSpaceGrad_coord_memLp φ i)
  have hspace : Integrable
      (fun z => vecDot (matVecMul (a z) (cauchyEnergyGradient u z))
        (parSpaceGrad φ.toFun z)) (slabMeasure d s T) := by
    have hs : Integrable (fun z => ∑ i : Fin d,
        matVecMul (a z) (cauchyEnergyGradient u z) i * parSpaceGrad φ.toFun z i)
        (slabMeasure d s T) :=
      integrable_finsetSum Finset.univ fun i _ => hflux i
    exact hs.congr (Filter.Eventually.of_forall fun z => by simp [vecDot])
  exact htime.neg.add hspace

/-- The exponentially rescaled Lions fields satisfy the integrability and integral clauses of the
parabolic weak-solution definition for every interior test. -/
theorem cauchyLions_energyWeakForm {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 (volume : Measure (Vec d)))
    (u : CauchyX d s T)
    (hrep : ∀ ψ : CauchyTestSpace d s T,
      inner ℝ u (cauchyT (c := 1) ha ψ) =
        inner ℝ (hf.toLp f) (cauchyGamma ψ)) :
    ∀ φ : ParTestFunction (univ : Set (Vec d)) (interior (Icc s T)),
      IntegrableOn (fun z =>
        -(cauchyEnergyValue u z * parTimeDeriv φ.toFun z) +
          vecDot (matVecMul (a z) (cauchyEnergyGradient u z)) (parSpaceGrad φ.toFun z))
        ((univ : Set (Vec d)) ×ˢ Icc s T) ∧
      ∫ z in (univ : Set (Vec d)) ×ˢ Icc s T,
        -(cauchyEnergyValue u z * parTimeDeriv φ.toFun z) +
          vecDot (matVecMul (a z) (cauchyEnergyGradient u z)) (parSpaceGrad φ.toFun z) = 0 := by
  intro φ
  have hi := cauchyEnergy_weakIntegrand_integrable ha u φ
  have heq := cauchyLions_interiorWeakEquation hsT ha f hf u hrep φ
  exact ⟨by simpa only [IntegrableOn, slabMeasure] using hi,
    by simpa only [slabMeasure] using heq⟩

/-- The weak spatial-gradient identity survives the time-dependent exponential rescaling: its
multiplier is constant in space on each slice. -/
theorem cauchyClosure_ae_energySliceWeakGradient {d : ℕ} {s T : ℝ}
    {u : CauchyX d s T} {u₀ : CauchyY d}
    (hu : WithLp.toLp 2 (u, u₀) ∈
      (LinearMap.range (initialTraceMap (cauchyJ (d := d) (s := s) (T := T))
        (cauchyGamma (d := d) (s := s) (T := T)))).topologicalClosure) :
    ∀ᵐ t ∂(volume.restrict (Icc s T)),
      HasWeakGradientOn (univ : Set (Vec d))
        (fun x => cauchyEnergyValue u (x, t))
        (fun x => cauchyEnergyGradient u (x, t)) := by
  filter_upwards [cauchyClosure_ae_sliceWeakGradient hu] with t ht
  let c : ℝ := Real.exp (t - s)
  have h := ht.smul c
  have hval : (fun x => cauchyEnergyValue u (x, t)) =
      c • (fun x => cauchyJointValue u (x, t)) := by
    funext x
    simp [c, cauchyEnergyValue, cauchyWeight, cauchyJointValue]
  have hgrad : (fun x => cauchyEnergyGradient u (x, t)) =
      c • (fun x => cauchyJointGradient u (x, t)) := by
    funext x
    ext i
    simp [c, cauchyEnergyGradient, cauchyWeight, cauchyJointGradient]
  rw [hval, hgrad]
  exact h

/-- The concrete Lions construction supplies weighted energy fields with the full interior weak
equation and the almost-everywhere slice-gradient property. This is the space-time part of the
Cauchy existence construction; the every-time representative and its global slice bound are
separate requirements. -/
theorem exists_cauchy_lions_energyFields {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 (volume : Measure (Vec d))) :
    ∃ u : CauchyX d s T, ∃ u₀ : CauchyY d,
      WithLp.toLp 2 (u, u₀) ∈
        (LinearMap.range (initialTraceMap (cauchyJ (d := d) (s := s) (T := T))
          (cauchyGamma (d := d) (s := s) (T := T)))).topologicalClosure ∧
      (∀ ψ : CauchyTestSpace d s T,
        inner ℝ u (cauchyT (c := 1) ha ψ) =
          inner ℝ (hf.toLp f) (cauchyGamma ψ)) ∧
      MemLp (cauchyEnergyValue u) 2 (slabMeasure d s T) ∧
      (∀ i : Fin d, MemLp (fun z => cauchyEnergyGradient u z i) 2
        (slabMeasure d s T)) ∧
      (∀ᵐ t ∂(volume.restrict (Icc s T)),
        HasWeakGradientOn (univ : Set (Vec d))
          (fun x => cauchyEnergyValue u (x, t))
          (fun x => cauchyEnergyGradient u (x, t))) ∧
      (∀ φ : ParTestFunction (univ : Set (Vec d)) (interior (Icc s T)),
        IntegrableOn (fun z =>
          -(cauchyEnergyValue u z * parTimeDeriv φ.toFun z) +
            vecDot (matVecMul (a z) (cauchyEnergyGradient u z))
              (parSpaceGrad φ.toFun z)) ((univ : Set (Vec d)) ×ˢ Icc s T) ∧
        ∫ z in (univ : Set (Vec d)) ×ˢ Icc s T,
          -(cauchyEnergyValue u z * parTimeDeriv φ.toFun z) +
            vecDot (matVecMul (a z) (cauchyEnergyGradient u z))
              (parSpaceGrad φ.toFun z) = 0) := by
  obtain ⟨u, u₀, hu, hrep⟩ := exists_cauchy_lions_pair hsT ha f hf
  refine ⟨u, u₀, hu, hrep, cauchyEnergyValue_memLp u,
    (fun i => cauchyEnergyGradient_coord_memLp u i),
    cauchyClosure_ae_energySliceWeakGradient hu, ?_⟩
  exact cauchyLions_energyWeakForm hsT ha f hf u hrep

end PDE.Parabolic.Lions
