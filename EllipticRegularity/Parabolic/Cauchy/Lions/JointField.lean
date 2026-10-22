module

public import EllipticRegularity.Parabolic.Cauchy.Lions.Existence
public import PDEFoundation.Analysis.CompactSupportLocalIBP

/-! # Representatives of a joint Lions limit -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.Lions

private theorem parSpaceGrad_zero_of_notMem_tsupport {d : ℕ}
    {ψ : Vec d × ℝ → ℝ} {z : Vec d × ℝ} (hz : z ∉ tsupport ψ) :
    parSpaceGrad ψ z = 0 := by
  have hD : fderiv ℝ ψ z = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hz (tsupport_fderiv_subset ℝ h))
  funext i
  simp [parSpaceGrad, hD]

private theorem parSpaceGrad_i_hasCompactSupport {d : ℕ} {ψ : Vec d × ℝ → ℝ}
    (hψc : HasCompactSupport ψ) (i : Fin d) :
    HasCompactSupport (fun z => parSpaceGrad ψ z i) := by
  apply hasCompactSupport_of_zero_off hψc
  intro z hz
  exact congrFun (parSpaceGrad_zero_of_notMem_tsupport hz) i

private theorem cauchy_vecDot_smul_right {d : ℕ} (c : ℝ) (x y : Vec d) :
    PDE.vecDot x (c • y) = c * PDE.vecDot x y := by
  simp only [PDE.vecDot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  ring

/-- The scalar value component of a space-time joint Lions limit. -/
noncomputable def cauchyJointValue {d : ℕ} {s T : ℝ}
    (z : CauchyX d s T) (x : Vec d × ℝ) : ℝ := (z x).fst

/-- The native-coordinate gradient component of a space-time joint Lions limit. -/
noncomputable def cauchyJointGradient {d : ℕ} {s T : ℝ}
    (z : CauchyX d s T) (x : Vec d × ℝ) : Vec d := ((z x).snd).toVec

theorem cauchyJointValue_memLp {d : ℕ} {s T : ℝ} (z : CauchyX d s T) :
    MemLp (cauchyJointValue z) 2 (slabMeasure d s T) := by
  change MemLp (fun x => (z x).fst) 2 (slabMeasure d s T)
  exact (Lp.memLp z).continuousLinearMap_comp
    (WithLp.fstL 2 ℝ ℝ (HilbertVec d))

theorem cauchyJointGradient_memLp {d : ℕ} {s T : ℝ} (z : CauchyX d s T)
    (i : Fin d) :
    MemLp (fun x => cauchyJointGradient z x i) 2 (slabMeasure d s T) := by
  let L : WithLp 2 (ℝ × HilbertVec d) →L[ℝ] ℝ :=
    (PiLp.proj 2 (fun _ : Fin d => ℝ) i).comp
      (WithLp.sndL 2 ℝ ℝ (HilbertVec d))
  change MemLp (fun x =>
    L (z x)) 2 (slabMeasure d s T)
  exact (Lp.memLp z).continuousLinearMap_comp L

/-- The test jet paired against a joint value/gradient field in the `i`th weak-gradient
identity. -/
noncomputable def cauchySpatialTestJet {d : ℕ} {s T : ℝ}
    (ψ : ParTestFunction (univ : Set (Vec d)) (interior (Icc s T)))
    (i : Fin d) (z : Vec d × ℝ) : WithLp 2 (ℝ × HilbertVec d) :=
  WithLp.toLp 2 (parSpaceGrad ψ.toFun z i,
    Vec.toHilbertVec (ψ.toFun z • basisVec i))

theorem cauchySpatialTestJetFun_memLp {d : ℕ} {s T : ℝ}
    (ψ : ParTestFunction (univ : Set (Vec d)) (interior (Icc s T))) (i : Fin d) :
    MemLp (cauchySpatialTestJet ψ i) 2 (slabMeasure d s T) := by
  rw [MeasureTheory.memLp_prodLp_iff]
  constructor
  · have hc : Continuous (fun z => parSpaceGrad ψ.toFun z i) :=
      (continuous_apply i).comp (continuous_parSpaceGrad ψ.contDiff)
    exact hc.memLp_of_hasCompactSupport
      (parSpaceGrad_i_hasCompactSupport ψ.hasCompactSupport i)
  · apply memLp_hilbertVec_sum
    intro j
    have hc : Continuous (fun z : Vec d × ℝ => ψ.toFun z • basisVec i j) :=
      ψ.contDiff.continuous.mul continuous_const
    have hK : HasCompactSupport (fun z : Vec d × ℝ => ψ.toFun z • basisVec i j) := by
      apply hasCompactSupport_of_zero_off ψ.hasCompactSupport
      intro z hz
      simp [image_eq_zero_of_notMem_tsupport hz]
    exact hc.memLp_of_hasCompactSupport hK

/-- The canonical `L²` class of a spatial test jet. -/
noncomputable def cauchySpatialTestJetLp {d : ℕ} {s T : ℝ}
    (ψ : ParTestFunction (univ : Set (Vec d)) (interior (Icc s T))) (i : Fin d) :
    CauchyX d s T :=
  (cauchySpatialTestJetFun_memLp ψ i).toLp _

private theorem cauchySpatialTestJet_apply {d : ℕ} {s T : ℝ}
    (ψ : ParTestFunction (univ : Set (Vec d)) (interior (Icc s T))) (i : Fin d) :
    cauchySpatialTestJetLp ψ i =
      (cauchySpatialTestJetFun_memLp ψ i).toLp _ := rfl

private theorem cauchyJ_spatialTestJet_inner_zero {d : ℕ} {s T : ℝ}
    (φ : CauchyTestSpace d s T)
    (ψ : ParTestFunction (univ : Set (Vec d)) (interior (Icc s T))) (i : Fin d) :
    inner ℝ (cauchyJ φ) (cauchySpatialTestJetLp ψ i) = 0 := by
  let f : Vec d × ℝ → ℝ := φ
  let g : Vec d × ℝ → ℝ := ψ.toFun
  let v : Vec d × ℝ := (basisVec i, 0)
  let Df : Vec d × ℝ → ℝ := fun z => fderiv ℝ f z v
  let Dg : Vec d × ℝ → ℝ := fun z => fderiv ℝ g z v
  have hDfc : Continuous Df := by
    exact (φ.property.1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDgc : Continuous Dg := by
    exact (ψ.contDiff.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDgK : HasCompactSupport Dg := ψ.hasCompactSupport.fderiv_apply ℝ v
  have hDfg : Integrable (fun z => Df z * g z) (volume : Measure (Vec d × ℝ)) :=
    (hDfc.mul ψ.contDiff.continuous).integrable_of_hasCompactSupport
      (ψ.hasCompactSupport.mul_left)
  have hfgD : Integrable (fun z => f z * Dg z) (volume : Measure (Vec d × ℝ)) :=
    (φ.property.1.continuous.mul hDgc).integrable_of_hasCompactSupport hDgK.mul_left
  have hfg : Integrable (fun z => f z * g z) (volume : Measure (Vec d × ℝ)) :=
    (φ.property.1.continuous.mul ψ.contDiff.continuous).integrable_of_hasCompactSupport
      (ψ.hasCompactSupport.mul_left)
  have hhaar : (volume : Measure (Vec d × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    exact Measure.prod.instIsAddHaarMeasure _ _
  let := hhaar
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (Vec d × ℝ))) (f := f) (g := g) (v := v)
    hDfg hfgD hfg
    (fun z hz => φ.property.1.differentiable (by norm_num) z)
    (fun z hz => ψ.contDiff.differentiable (by norm_num) z)
  let q : Vec d × ℝ → ℝ := fun z => f z * Dg z + Df z * g z
  have hzeroGlobal :
      ∫ z, q z ∂(volume : Measure (Vec d × ℝ)) = 0 := by
    dsimp only [q]
    rw [integral_add hfgD hDfg, hIBP]
    ring
  have hqZeroOutside : ∀ z, z ∉ (univ : Set (Vec d)) ×ˢ interior (Icc s T) → q z = 0 := by
    intro z hz
    have hzψ : z ∉ tsupport ψ.toFun := by
      intro hz'
      apply hz
      exact ⟨mem_univ _, (ψ.tsupport_subset hz').2⟩
    have hg0 : g z = 0 := image_eq_zero_of_notMem_tsupport hzψ
    have hDg0 : Dg z = 0 := by
      dsimp [Dg, g, v]
      rw [fderiv_of_notMem_tsupport ℝ hzψ]
      exact zero_apply _
    simp [q, Dg, Df, f, g, hg0, hDg0]
  have hrestrict :
      (∫ z, q z ∂slabMeasure d s T) =
        ∫ z, q z ∂(volume : Measure (Vec d × ℝ)) := by
    change (∫ z in (univ : Set (Vec d)) ×ˢ Icc s T, q z) = _
    have hzero : ∀ z, z ∉ (univ : Set (Vec d)) ×ˢ Icc s T → q z = 0 := by
      intro z hz
      apply hqZeroOutside z
      rintro ⟨_, ht⟩
      exact hz ⟨mem_univ _, (interior_subset ht)⟩
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  have hJ := cauchyJFun_memLp φ
  have hψmem := cauchySpatialTestJetFun_memLp ψ i
  rw [cauchyJ_apply, cauchySpatialTestJet_apply, MeasureTheory.L2.inner_def]
  calc
    (∫ z, inner ℝ ((cauchyJ φ) z) ((cauchySpatialTestJetLp ψ i) z)
        ∂slabMeasure d s T) = ∫ z, q z ∂slabMeasure d s T := by
      apply integral_congr_ae
      filter_upwards [hJ.coeFn_toLp, hψmem.coeFn_toLp] with z hzJ hzψ
      have hJ' : (cauchyJ φ) z = cauchyJFun (φ : Vec d × ℝ → ℝ) z := by
        rw [cauchyJ_apply]
        exact hzJ
      have hψ' : (cauchySpatialTestJetLp ψ i) z = cauchySpatialTestJet ψ i z := by
        rw [cauchySpatialTestJet_apply]
        exact hzψ
      rw [hJ', hψ', WithLp.prod_inner_apply]
      simp only [cauchyJFun, cauchySpatialTestJet]
      rw [PDE.inner_toHilbertVec_eq_vecDot]
      rw [cauchy_vecDot_smul_right, PDE.vecDot_basisVec_right]
      simp [q, f, g, Df, Dg, v, parSpaceGrad]
      ring
    _ = 0 := by rw [hrestrict, hzeroGlobal]

/-- A joint Lions limit is orthogonal to every compactly supported spatial test jet. -/
theorem cauchyClosure_testJet_orthogonal {d : ℕ} {s T : ℝ}
    {u : CauchyX d s T} {u₀ : CauchyY d}
    (hu : WithLp.toLp 2 (u, u₀) ∈
      (LinearMap.range (initialTraceMap (cauchyJ (d := d) (s := s) (T := T))
        (cauchyGamma (d := d) (s := s) (T := T)))).topologicalClosure)
    (ψ : ParTestFunction (univ : Set (Vec d)) (interior (Icc s T))) (i : Fin d) :
    inner ℝ u (cauchySpatialTestJetLp ψ i) = 0 := by
  let F : WithLp 2 (CauchyX d s T × CauchyY d) →L[ℝ] ℝ :=
    (innerSL ℝ (cauchySpatialTestJetLp ψ i)).comp
      (WithLp.fstL 2 ℝ (CauchyX d s T) (CauchyY d))
  have hrange :
      LinearMap.range (initialTraceMap (cauchyJ (d := d) (s := s) (T := T))
        (cauchyGamma (d := d) (s := s) (T := T))) ≤ F.ker := by
    rintro y ⟨φ, rfl⟩
    rw [LinearMap.mem_ker]
    change inner ℝ (cauchySpatialTestJetLp ψ i) (cauchyJ φ) = 0
    rw [real_inner_comm]
    exact cauchyJ_spatialTestJet_inner_zero φ ψ i
  have hsub :
      (LinearMap.range (initialTraceMap (cauchyJ (d := d) (s := s) (T := T))
        (cauchyGamma (d := d) (s := s) (T := T)))).topologicalClosure ≤ F.ker :=
    (LinearMap.range (initialTraceMap (cauchyJ (d := d) (s := s) (T := T))
      (cauchyGamma (d := d) (s := s) (T := T)))).topologicalClosure_minimal hrange
        (ContinuousLinearMap.isClosed_ker F)
  have hF := hsub hu
  change inner ℝ (cauchySpatialTestJetLp ψ i) u = 0 at hF
  rwa [real_inner_comm] at hF

/-- The value and gradient components of a joint Lions limit satisfy the spacetime weak-gradient
identity against every compactly supported `C¹` test. -/
theorem cauchyClosure_spacetimeWeakGradient {d : ℕ} {s T : ℝ}
    {u : CauchyX d s T} {u₀ : CauchyY d}
    (hu : WithLp.toLp 2 (u, u₀) ∈
      (LinearMap.range (initialTraceMap (cauchyJ (d := d) (s := s) (T := T))
        (cauchyGamma (d := d) (s := s) (T := T)))).topologicalClosure)
    (ψ : ParTestFunction (univ : Set (Vec d)) (interior (Icc s T))) (i : Fin d) :
    ∫ z, cauchyJointValue u z * parSpaceGrad ψ.toFun z i ∂slabMeasure d s T =
      -∫ z, cauchyJointGradient u z i * ψ.toFun z ∂slabMeasure d s T := by
  have horth := cauchyClosure_testJet_orthogonal hu ψ i
  rw [MeasureTheory.L2.inner_def] at horth
  have hjet := cauchySpatialTestJetFun_memLp ψ i
  have hsum :
      ∫ z, cauchyJointValue u z * parSpaceGrad ψ.toFun z i +
        cauchyJointGradient u z i * ψ.toFun z ∂slabMeasure d s T = 0 := by
    calc
      ∫ z, cauchyJointValue u z * parSpaceGrad ψ.toFun z i +
          cauchyJointGradient u z i * ψ.toFun z ∂slabMeasure d s T =
        ∫ z, inner ℝ (u z) (cauchySpatialTestJetLp ψ i z) ∂slabMeasure d s T := by
          apply integral_congr_ae
          filter_upwards [hjet.coeFn_toLp] with z hz
          have hrep : (cauchySpatialTestJetLp ψ i) z = cauchySpatialTestJet ψ i z := by
            rw [cauchySpatialTestJet_apply]
            exact hz
          rw [hrep, cauchySpatialTestJet, WithLp.prod_inner_apply]
          simp only [cauchyJointValue, cauchyJointGradient]
          rw [← PDE.Vec.toHilbertVec_toVec ((u z).ofLp.2),
            PDE.inner_toHilbertVec_eq_vecDot, cauchy_vecDot_smul_right,
            PDE.vecDot_basisVec_right]
          simp [parSpaceGrad]
          ring
      _ = 0 := horth
  have hleft : Integrable
      (fun z => cauchyJointValue u z * parSpaceGrad ψ.toFun z i) (slabMeasure d s T) := by
    have hc : Continuous (fun z => parSpaceGrad ψ.toFun z i) :=
      (continuous_apply i).comp (continuous_parSpaceGrad ψ.contDiff)
    have hg : MemLp (fun z => parSpaceGrad ψ.toFun z i) 2 (slabMeasure d s T) :=
      hc.memLp_of_hasCompactSupport (parSpaceGrad_i_hasCompactSupport ψ.hasCompactSupport i)
    exact (cauchyJointValue_memLp u).integrable_mul hg
  have hright : Integrable
      (fun z => cauchyJointGradient u z i * ψ.toFun z) (slabMeasure d s T) := by
    have hψmem' : MemLp ψ.toFun 2 (slabMeasure d s T) :=
      ψ.contDiff.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport
    exact (cauchyJointGradient_memLp u i).integrable_mul hψmem'
  rw [integral_add hleft hright] at hsum
  linarith

end PDE.Parabolic.Lions
