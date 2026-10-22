module

public import EllipticRegularity.Parabolic.Cauchy.Lions.TestSpace
public import PDEFoundation.Sobolev.H1.GraphPairing
public import EllipticRegularity.Parabolic.WeakSlice.Flux

/-! # Concrete Lions maps for the parabolic Cauchy problem -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped InnerProductSpace

namespace PDE.Parabolic.Lions

/-- The space-time Hilbert space for the value and spatial gradient. -/
noncomputable abbrev CauchyX (d : ℕ) (s T : ℝ) :=
  Lp (WithLp 2 (ℝ × HilbertVec d)) 2 (slabMeasure d s T)

/-- The initial-data Hilbert space. -/
noncomputable abbrev CauchyY (d : ℕ) := Lp ℝ 2 (volume : Measure (Vec d))

/-- The pointwise graph pair `(φ, ∇ₓφ)`. -/
noncomputable def cauchyJFun {d : ℕ} (φ : Vec d × ℝ → ℝ) (z : Vec d × ℝ) :
    WithLp 2 (ℝ × HilbertVec d) :=
  WithLp.toLp 2 (φ z, Vec.toHilbertVec (parSpaceGrad φ z))

/-- The pointwise test operator `(cφ - ∂ₜφ, aᵀ∇ₓφ)`. -/
noncomputable def cauchyTFun {d : ℕ} (c : ℝ) (a : ParCoeffField d)
    (φ : Vec d × ℝ → ℝ) (z : Vec d × ℝ) : WithLp 2 (ℝ × HilbertVec d) :=
  WithLp.toLp 2 (c * φ z - parTimeDeriv φ z,
    Vec.toHilbertVec (matVecMul (matTranspose (a z)) (parSpaceGrad φ z)))

/-- The pointwise initial trace. -/
noncomputable def cauchyTraceFun {d : ℕ} (s : ℝ) (φ : Vec d × ℝ → ℝ) (x : Vec d) : ℝ :=
  φ (x, s)

private theorem parTimeDeriv_eq_zero_of_notMem_tsupport {d : ℕ} {φ : Vec d × ℝ → ℝ}
    (_hφ : ContDiff ℝ 1 φ) {z : Vec d × ℝ} (hz : z ∉ tsupport φ) :
    parTimeDeriv φ z = 0 := by
  have hD : fderiv ℝ φ z = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hz (tsupport_fderiv_subset ℝ h))
  simp [parTimeDeriv, hD]

private theorem parSpaceGrad_eq_zero_of_notMem_tsupport {d : ℕ} {φ : Vec d × ℝ → ℝ}
    (_hφ : ContDiff ℝ 1 φ) {z : Vec d × ℝ} (hz : z ∉ tsupport φ) :
    parSpaceGrad φ z = 0 := by
  have hD : fderiv ℝ φ z = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hz (tsupport_fderiv_subset ℝ h))
  funext i
  simp [parSpaceGrad, hD]

private theorem memLp_parSpaceGrad {d : ℕ} {s T : ℝ}
    {φ : CauchyTestSpace d s T} (i : Fin d) :
    MemLp (fun z => parSpaceGrad (φ : Vec d × ℝ → ℝ) z i) 2 (slabMeasure d s T) := by
  have hc : Continuous (fun z : Vec d × ℝ => parSpaceGrad (φ : Vec d × ℝ → ℝ) z i) :=
    (continuous_apply i).comp (continuous_parSpaceGrad φ.property.1)
  have hK : HasCompactSupport
      (fun z : Vec d × ℝ => parSpaceGrad (φ : Vec d × ℝ → ℝ) z i) := by
    apply hasCompactSupport_of_zero_off φ.property.2.1.isCompact
    intro z hz
    simp [parSpaceGrad_eq_zero_of_notMem_tsupport φ.property.1 hz]
  exact hc.memLp_of_hasCompactSupport hK

private noncomputable def hilbertVecCoord {d : ℕ} (i : Fin d) :
    ℝ →L[ℝ] HilbertVec d :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i)

/-- Finite coordinatewise `L²` control implies `L²` control in the internal Hilbert vector
realization. -/
theorem memLp_hilbertVec_sum {d : ℕ} {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → Vec d} (hf : ∀ i, MemLp (fun z => f z i) 2 μ) :
    MemLp (fun z => Vec.toHilbertVec (f z)) 2 μ := by
  have hs : MemLp (fun z => ∑ i : Fin d, hilbertVecCoord i (f z i)) 2 μ :=
    MeasureTheory.memLp_finsetSum Finset.univ fun i _ =>
      (hf i).continuousLinearMap_comp (hilbertVecCoord i)
  have hpoint : ∀ z, Vec.toHilbertVec (f z) =
      ∑ i : Fin d, hilbertVecCoord i (f z i) := by
    intro z
    ext i
    simp [hilbertVecCoord, Vec.toHilbertVec, ContinuousLinearMap.comp_apply]
  exact MeasureTheory.MemLp.ae_eq
    (Filter.Eventually.of_forall fun z => (hpoint z).symm) hs

private theorem memLp_parSpaceGrad_hilbert {d : ℕ} {s T : ℝ}
    {φ : CauchyTestSpace d s T} :
    MemLp (fun z => Vec.toHilbertVec (parSpaceGrad (φ : Vec d × ℝ → ℝ) z))
      2 (slabMeasure d s T) := by
  exact memLp_hilbertVec_sum
    (fun i => memLp_parSpaceGrad (s := s) (T := T) (φ := φ) i)

private theorem memLp_parTimeDeriv {d : ℕ} {s T : ℝ}
    {φ : CauchyTestSpace d s T} :
    MemLp (fun z => parTimeDeriv (φ : Vec d × ℝ → ℝ) z) 2 (slabMeasure d s T) := by
  have hc : Continuous (fun z : Vec d × ℝ => parTimeDeriv (φ : Vec d × ℝ → ℝ) z) :=
    continuous_parTimeDeriv φ.property.1
  have hK : HasCompactSupport
      (fun z : Vec d × ℝ => parTimeDeriv (φ : Vec d × ℝ → ℝ) z) := by
    apply hasCompactSupport_of_zero_off φ.property.2.1.isCompact
    intro z hz
    rw [parTimeDeriv_eq_zero_of_notMem_tsupport φ.property.1 hz]
  exact hc.memLp_of_hasCompactSupport hK

private theorem memLp_cauchyGradFlux {d : ℕ} {s T lam Lam : ℝ} {a : ParCoeffField d}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) {φ : CauchyTestSpace d s T}
    (i : Fin d) :
    MemLp (fun z => matVecMul (matTranspose (a z))
      (parSpaceGrad (φ : Vec d × ℝ → ℝ) z) i) 2 (slabMeasure d s T) := by
  have hgrad j := memLp_parSpaceGrad (s := s) (T := T) (φ := φ) j
  rw [show slabMeasure d s T = volume.restrict (univ ×ˢ Icc s T) by rfl]
  simp only [matVecMul, matTranspose]
  refine memLp_finsetSum _ fun j _ => ?_
  have hmeas : AEMeasurable (fun z : Vec d × ℝ => a z j i)
      (volume.restrict (univ ×ˢ Icc s T)) := ha.measurable j i
  refine (hgrad j).of_le_mul (c := Lam) (hmeas.aestronglyMeasurable.mul (hgrad j).aestronglyMeasurable) ?_
  filter_upwards [ha.elliptic] with z hz
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (PDE.Parabolic.WeakSlice.matrix_abs_entry_le hz j i)
    (abs_nonneg _)

private theorem memLp_cauchyGradFlux_hilbert {d : ℕ} {s T lam Lam : ℝ}
    {a : ParCoeffField d} (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    {φ : CauchyTestSpace d s T} :
    MemLp (fun z => Vec.toHilbertVec (matVecMul (matTranspose (a z))
      (parSpaceGrad (φ : Vec d × ℝ → ℝ) z))) 2 (slabMeasure d s T) := by
  exact memLp_hilbertVec_sum fun i => memLp_cauchyGradFlux ha i

theorem memLp_cauchyJFun {d : ℕ} {s T : ℝ}
    {φ : CauchyTestSpace d s T} :
    MemLp (cauchyJFun (φ : Vec d × ℝ → ℝ)) 2 (slabMeasure d s T) := by
  rw [MeasureTheory.memLp_prodLp_iff]
  constructor
  · simpa [cauchyJFun] using
      (memLp_slab_of_continuous_compact (s := s) (T := T)
        φ.property.1.continuous φ.property.2.1)
  · simpa [cauchyJFun] using memLp_parSpaceGrad_hilbert (s := s) (T := T) (φ := φ)

theorem memLp_cauchyTFun {d : ℕ} {s T c lam Lam : ℝ} {a : ParCoeffField d}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) {φ : CauchyTestSpace d s T} :
    MemLp (cauchyTFun c a (φ : Vec d × ℝ → ℝ)) 2 (slabMeasure d s T) := by
  rw [MeasureTheory.memLp_prodLp_iff]
  constructor
  · have hφ := memLp_slab_of_continuous_compact (s := s) (T := T)
      φ.property.1.continuous φ.property.2.1
    have hcφ : MemLp (fun z => c * (φ : Vec d × ℝ → ℝ) z) 2 (slabMeasure d s T) := by
      exact hφ.const_mul c
    change MemLp (fun z => c * (φ : Vec d × ℝ → ℝ) z -
      parTimeDeriv (φ : Vec d × ℝ → ℝ) z) 2 (slabMeasure d s T)
    exact hcφ.sub (memLp_parTimeDeriv (s := s) (T := T) (φ := φ))
  · change MemLp (fun z => Vec.toHilbertVec (matVecMul (matTranspose (a z))
      (parSpaceGrad (φ : Vec d × ℝ → ℝ) z))) 2 (slabMeasure d s T)
    exact memLp_cauchyGradFlux_hilbert (s := s) (T := T) (lam := lam) (Lam := Lam)
      (a := a) ha (φ := φ)

theorem memLp_cauchyTraceFun {d : ℕ} {s T : ℝ}
    {φ : CauchyTestSpace d s T} :
    MemLp (cauchyTraceFun s (φ : Vec d × ℝ → ℝ)) 2 (volume : Measure (Vec d)) := by
  obtain ⟨hc, hK⟩ := initialTrace_continuous_hasCompactSupport (s := s) (T := T) (φ := φ)
  exact memLp_space_of_continuous_compact hc hK

private theorem cauchyJFun_add {d : ℕ} {s T : ℝ} (φ ψ : CauchyTestSpace d s T)
    (z : Vec d × ℝ) :
    cauchyJFun ((φ + ψ : CauchyTestSpace d s T) : Vec d × ℝ → ℝ) z =
      cauchyJFun (φ : Vec d × ℝ → ℝ) z + cauchyJFun (ψ : Vec d × ℝ → ℝ) z := by
  apply (WithLp.equiv 2 (ℝ × HilbertVec d)).injective
  simp [cauchyJFun, Vec.toHilbertVec, WithLp.toLp_add, Submodule.coe_add,
    parSpaceGrad_add φ.property.1 ψ.property.1]

private theorem cauchyJFun_smul {d : ℕ} {s T : ℝ} (c : ℝ)
    (φ : CauchyTestSpace d s T) (z : Vec d × ℝ) :
    cauchyJFun ((c • φ : CauchyTestSpace d s T) : Vec d × ℝ → ℝ) z =
      c • cauchyJFun (φ : Vec d × ℝ → ℝ) z := by
  apply (WithLp.equiv 2 (ℝ × HilbertVec d)).injective
  simp [cauchyJFun, Vec.toHilbertVec, WithLp.toLp_smul,
    parSpaceGrad_smul]

private theorem cauchyTFun_add {d : ℕ} {s T c : ℝ} (a : ParCoeffField d)
    (φ ψ : CauchyTestSpace d s T) (z : Vec d × ℝ) :
    cauchyTFun c a ((φ + ψ : CauchyTestSpace d s T) : Vec d × ℝ → ℝ) z =
      cauchyTFun c a (φ : Vec d × ℝ → ℝ) z + cauchyTFun c a (ψ : Vec d × ℝ → ℝ) z := by
  apply (WithLp.equiv 2 (ℝ × HilbertVec d)).injective
  simp [cauchyTFun, Submodule.coe_add,
    parTimeDeriv_add φ.property.1 ψ.property.1, parSpaceGrad_add φ.property.1 ψ.property.1]
  constructor
  · ring
  · rw [show matVecMul (matTranspose (a z))
        (parSpaceGrad (φ : Vec d × ℝ → ℝ) z + parSpaceGrad (ψ : Vec d × ℝ → ℝ) z) =
      matVecMul (matTranspose (a z)) (parSpaceGrad (φ : Vec d × ℝ → ℝ) z) +
        matVecMul (matTranspose (a z)) (parSpaceGrad (ψ : Vec d × ℝ → ℝ) z) by
      ext i
      simp [matVecMul, Finset.sum_add_distrib, mul_add]]
    exact WithLp.toLp_add 2 _ _

private theorem cauchyTFun_smul {d : ℕ} {s T c : ℝ} (a : ParCoeffField d)
    (r : ℝ) (φ : CauchyTestSpace d s T) (z : Vec d × ℝ) :
    cauchyTFun c a ((r • φ : CauchyTestSpace d s T) : Vec d × ℝ → ℝ) z =
      r • cauchyTFun c a (φ : Vec d × ℝ → ℝ) z := by
  apply (WithLp.equiv 2 (ℝ × HilbertVec d)).injective
  simp [cauchyTFun, Vec.toHilbertVec,
    Pi.smul_apply, parTimeDeriv_smul, parSpaceGrad_smul]
  constructor
  · ring
  · rw [show matVecMul (matTranspose (a z))
        (r • parSpaceGrad (φ : Vec d × ℝ → ℝ) z) =
      r • matVecMul (matTranspose (a z)) (parSpaceGrad (φ : Vec d × ℝ → ℝ) z) by
      ext i
      simp only [matVecMul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring]
    exact WithLp.toLp_smul 2 r _

private theorem cauchyTraceFun_add {d : ℕ} {s T : ℝ}
    (φ ψ : CauchyTestSpace d s T) (x : Vec d) :
    cauchyTraceFun s ((φ + ψ : CauchyTestSpace d s T) : Vec d × ℝ → ℝ) x =
      cauchyTraceFun s (φ : Vec d × ℝ → ℝ) x + cauchyTraceFun s (ψ : Vec d × ℝ → ℝ) x := by
  rfl

private theorem cauchyTraceFun_smul {d : ℕ} {s T : ℝ}
    (c : ℝ) (φ : CauchyTestSpace d s T) (x : Vec d) :
    cauchyTraceFun s ((c • φ : CauchyTestSpace d s T) : Vec d × ℝ → ℝ) x =
      c • cauchyTraceFun s (φ : Vec d × ℝ → ℝ) x := by
  rfl

/-- Turn a pointwise linear family of `L²` functions into a linear map to the quotient space. -/
noncomputable def lpOfLinear {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : Type*} [AddCommGroup W] [Module ℝ W] {μ : Measure α}
    (F : W → α → E) (hF : ∀ w, MemLp (F w) 2 μ)
    (hadd : ∀ w w', F (w + w') = F w + F w')
    (hsmul : ∀ (c : ℝ) w, F (c • w) = c • F w) :
    W →ₗ[ℝ] Lp E 2 μ where
  toFun w := (hF w).toLp (F w)
  map_add' w w' := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => by rw [hadd])
  map_smul' c w := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => by rw [hsmul])

/-- Linear map `Jφ = (φ, ∇ₓφ)` into the space-time Hilbert space. -/
noncomputable def cauchyJ {d : ℕ} {s T : ℝ} :
    CauchyTestSpace d s T →ₗ[ℝ] CauchyX d s T :=
  lpOfLinear (fun φ z => cauchyJFun (φ : Vec d × ℝ → ℝ) z)
    (fun φ => memLp_cauchyJFun (φ := φ))
    (fun φ ψ => by funext z; exact cauchyJFun_add φ ψ z)
    (fun c φ => by funext z; exact cauchyJFun_smul c φ z)

/-- Linear map `Tφ = (cφ - ∂ₜφ, aᵀ∇ₓφ)` into the space-time Hilbert space. -/
noncomputable def cauchyT {d : ℕ} {s T c lam Lam : ℝ} {a : ParCoeffField d}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) :
    CauchyTestSpace d s T →ₗ[ℝ] CauchyX d s T :=
  lpOfLinear (fun φ z => cauchyTFun c a (φ : Vec d × ℝ → ℝ) z)
    (fun φ => memLp_cauchyTFun ha (c := c) (Lam := Lam) (lam := lam) (φ := φ))
    (fun φ ψ => by funext z; exact cauchyTFun_add a φ ψ z)
    (fun r φ => by funext z; exact cauchyTFun_smul a r φ z)

/-- Linear map taking a test function to its initial trace in `L²(ℝᵈ)`. -/
noncomputable def cauchyGamma {d : ℕ} {s T : ℝ} :
    CauchyTestSpace d s T →ₗ[ℝ] CauchyY d :=
  lpOfLinear (fun φ x => cauchyTraceFun s (φ : Vec d × ℝ → ℝ) x)
    (fun φ => memLp_cauchyTraceFun (s := s) (T := T) (φ := φ))
    (fun φ ψ => by funext x; exact cauchyTraceFun_add φ ψ x)
    (fun c φ => by funext x; exact cauchyTraceFun_smul c φ x)

/-- Integrability of the space-time value/gradient field of a test function. -/
theorem cauchyJFun_memLp {d : ℕ} {s T : ℝ} (φ : CauchyTestSpace d s T) :
    MemLp (cauchyJFun (φ : Vec d × ℝ → ℝ)) 2 (slabMeasure d s T) :=
  memLp_cauchyJFun

/-- Integrability of the coefficient test-operator field. -/
theorem cauchyTFun_memLp {d : ℕ} {s T c lam Lam : ℝ} {a : ParCoeffField d}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (φ : CauchyTestSpace d s T) :
    MemLp (cauchyTFun c a (φ : Vec d × ℝ → ℝ)) 2 (slabMeasure d s T) :=
  memLp_cauchyTFun ha

/-- Integrability of the initial spatial trace of a test function. -/
theorem cauchyTraceFun_memLp {d : ℕ} {s T : ℝ} (φ : CauchyTestSpace d s T) :
    MemLp (cauchyTraceFun s (φ : Vec d × ℝ → ℝ)) 2 (volume : Measure (Vec d)) :=
  memLp_cauchyTraceFun

@[simp]
theorem cauchyJ_apply {d : ℕ} {s T : ℝ} (φ : CauchyTestSpace d s T) :
    cauchyJ φ = (cauchyJFun_memLp φ).toLp _ := rfl

@[simp]
theorem cauchyT_apply {d : ℕ} {s T c lam Lam : ℝ} {a : ParCoeffField d}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (φ : CauchyTestSpace d s T) :
    cauchyT (c := c) ha φ = (cauchyTFun_memLp (c := c) ha φ).toLp _ := rfl

@[simp]
theorem cauchyGamma_apply {d : ℕ} {s T : ℝ} (φ : CauchyTestSpace d s T) :
    cauchyGamma φ = (cauchyTraceFun_memLp φ).toLp _ := rfl

end PDE.Parabolic.Lions
