module

public import EllipticRegularity.Parabolic.Cauchy.Energy.Global
public import EllipticRegularity.Parabolic.Cauchy.Duality.AdjCoeff

/-! # Endpoint product integrability for Cauchy duality -/

@[expose] public section

namespace PDE.Parabolic.Duality

open MeasureTheory Set

private theorem cauchy_duality_time_reflection_measurePreserving (d : ℕ) (s t : ℝ) :
    MeasurePreserving
      (fun z : Vec d × ℝ => (z.1, s + t - z.2))
      (volume.restrict (univ ×ˢ Icc s t))
      (volume.restrict (univ ×ˢ Icc s t)) := by
  let ρ : ℝ → ℝ := fun τ => s + t - τ
  have hneg : MeasurePreserving (fun τ : ℝ => -τ) (volume : Measure ℝ) volume :=
    Measure.measurePreserving_neg volume
  have hadd : MeasurePreserving (fun τ : ℝ => (s + t) + τ) volume volume :=
    MeasureTheory.measurePreserving_add_left volume (s + t)
  have htime : MeasurePreserving ρ volume volume := by
    convert hadd.comp hneg using 1
    ext τ
    simp [ρ, sub_eq_add_neg, add_assoc]
  have hprod : MeasurePreserving
      (fun z : Vec d × ℝ => (z.1, ρ z.2))
      ((volume : Measure (Vec d)).prod volume)
      ((volume : Measure (Vec d)).prod volume) := by
    convert (MeasurePreserving.id (volume : Measure (Vec d))).prod htime using 1
    rfl
  have hfull : MeasurePreserving
      (fun z : Vec d × ℝ => (z.1, s + t - z.2)) volume volume := by
    simpa only [MeasureTheory.Measure.volume_eq_prod] using hprod
  let S : Set (Vec d × ℝ) := univ ×ˢ Icc s t
  have hpre : (fun z : Vec d × ℝ => (z.1, s + t - z.2)) ⁻¹' S = S := by
    ext ⟨x, τ⟩
    simp only [S, mem_preimage, mem_prod, mem_univ, true_and, mem_Icc]
    constructor
    · intro h
      constructor <;> linarith
    · intro h
      constructor <;> linarith
  have hrestrict := hfull.restrict_preimage
    (s := S) (MeasurableSet.prod MeasurableSet.univ measurableSet_Icc)
  rw [hpre] at hrestrict
  simpa [S] using hrestrict

private theorem cauchy_slice_aestronglyMeasurable {d : ℕ} {s T : ℝ}
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T)) {t : ℝ} (ht : t ∈ Icc s T) :
    AEStronglyMeasurable (parSlice u.toFun t) (volume : Measure (Vec d)) := by
  let K : ℕ → Set (Vec d) := fun n => euclideanClosedBall 0 ((n : ℝ) + 1)
  have hcover : (⋃ n, K n) = (univ : Set (Vec d)) := by
    ext x
    constructor
    · intro _
      exact mem_univ x
    · intro _
      obtain ⟨N, hN⟩ := exists_nat_gt (vecEuclideanNorm x)
      refine mem_iUnion.mpr ⟨N, ?_⟩
      change x ∈ euclideanClosedBall 0 ((N : ℝ) + 1)
      apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
      rw [sub_zero]
      linarith
  have hloc : ∀ n, AEStronglyMeasurable (parSlice u.toFun t)
      (volume.restrict (K n)) := by
    intro n
    exact (u.sliceL2loc t ht (K n)
      (isCompact_euclideanClosedBall 0 (by positivity)) (Set.subset_univ _)).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (parSlice u.toFun t)
      (volume.restrict (⋃ n, K n)) := AEStronglyMeasurable.iUnion hloc
  have hmeasure : volume.restrict (⋃ n, K n) = volume := by
    rw [hcover]
    exact Measure.restrict_univ
  rw [hmeasure] at hmeas
  exact hmeas

/-- The energy identity gives global `L²` slices at the terminal time, hence
the two products appearing in the duality conclusion are integrable. -/
theorem cauchy_duality_endpoint_products_integrable {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s t : ℝ} (hst : s < t)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s t)) (f g : Vec d → ℝ)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s t))
    (hu : IsCauchySolution a s t f u)
    (w : ParH1Function (univ : Set (Vec d)) (Icc s t))
    (hw : IsCauchySolution (parAdjCoeff a (s + t)) s t g w) :
    Integrable (fun x => g x * u.toFun (x, t)) volume ∧
      Integrable (fun x => f x * w.toFun (x, t)) volume := by
  have huSq := PDE.Parabolic.Cauchy.Energy.cauchy_slice_square_integrable
    hst ha f hf u hu ⟨le_of_lt hst, le_rfl⟩
  have hwAdj := parAdjCoeff_isParabolicCoeff_core d lam Lam a s t ha
  have hwSq := PDE.Parabolic.Cauchy.Energy.cauchy_slice_square_integrable
    hst hwAdj g hg w hw ⟨le_of_lt hst, le_rfl⟩
  have huMem : MemLp (fun x : Vec d => u.toFun (x, t)) 2 volume := by
    change MemLp (parSlice u.toFun t) 2 volume
    rw [memLp_two_iff_integrable_sq (cauchy_slice_aestronglyMeasurable u
      ⟨le_of_lt hst, le_rfl⟩)]
    simpa [parSlice] using huSq
  have hwMem : MemLp (fun x : Vec d => w.toFun (x, t)) 2 volume := by
    change MemLp (parSlice w.toFun t) 2 volume
    rw [memLp_two_iff_integrable_sq (cauchy_slice_aestronglyMeasurable w
      ⟨le_of_lt hst, le_rfl⟩)]
    simpa [parSlice] using hwSq
  exact ⟨hg.integrable_mul huMem, hf.integrable_mul hwMem⟩

/-- The mixed solution-flux terms in the duality product rule are integrable
on the whole spacetime slab. The second solution is viewed at reflected time,
so its flux is the transpose flux for the forward coefficient. -/
theorem cauchy_duality_mixed_flux_products_integrable {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s t : ℝ}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s t))
    (u : ParH1Function (univ : Set (Vec d)) (Icc s t))
    (w : ParH1Function (univ : Set (Vec d)) (Icc s t)) :
    ∀ i : Fin d,
      Integrable (fun z : Vec d × ℝ =>
        u.toFun z * PDE.Parabolic.Energy.flux (parAdjCoeff a (s + t)) w
          (z.1, s + t - z.2) i)
          (volume.restrict (univ ×ˢ Ioc s t)) ∧
      Integrable (fun z : Vec d × ℝ =>
        w.toFun (z.1, s + t - z.2) * PDE.Parabolic.Energy.flux a u z i)
          (volume.restrict (univ ×ˢ Ioc s t)) := by
  let Q : Set (Vec d × ℝ) := univ ×ˢ Ioc s t
  let Qc : Set (Vec d × ℝ) := univ ×ˢ Icc s t
  let μc : Measure (Vec d × ℝ) := volume.restrict Qc
  let μ : Measure (Vec d × ℝ) := volume.restrict Q
  let ρ : Vec d × ℝ → Vec d × ℝ := fun z => (z.1, s + t - z.2)
  have hρ := cauchy_duality_time_reflection_measurePreserving d s t
  have hQsub : Q ⊆ Qc := by
    intro z hz
    exact ⟨hz.1, ⟨hz.2.1.le, hz.2.2⟩⟩
  have hle : μ ≤ μc := Measure.restrict_mono hQsub le_rfl
  have hu2 : MemLp u.toFun 2 μc := u.memL2
  have hw2 : MemLp (fun z => w.toFun (ρ z)) 2 μc := by
    exact w.memL2.comp_measurePreserving hρ
  have haAdj := parAdjCoeff_isParabolicCoeff_core d lam Lam a s t ha
  have hFu i : MemLp (fun z => PDE.Parabolic.Energy.flux a u z i) 2 μc :=
    PDE.Parabolic.Energy.flux_memLp ha u i
  have hFw i : MemLp
      (fun z => PDE.Parabolic.Energy.flux (parAdjCoeff a (s + t)) w (ρ z) i) 2 μc :=
    (PDE.Parabolic.Energy.flux_memLp haAdj w i).comp_measurePreserving hρ
  intro i
  have h1 : Integrable (fun z : Vec d × ℝ =>
      u.toFun z * PDE.Parabolic.Energy.flux (parAdjCoeff a (s + t)) w (ρ z) i) μc :=
    hu2.integrable_mul (hFw i)
  have h2 : Integrable (fun z : Vec d × ℝ =>
      w.toFun (ρ z) * PDE.Parabolic.Energy.flux a u z i) μc :=
    hw2.integrable_mul (hFu i)
  refine ⟨?_, ?_⟩
  · exact h1.mono_measure hle
  · exact h2.mono_measure hle

end PDE.Parabolic.Duality
