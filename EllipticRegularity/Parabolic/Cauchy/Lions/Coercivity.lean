module

public import EllipticRegularity.Parabolic.Cauchy.Lions.TestMaps
public import EllipticRegularity.Parabolic.Energy.Slab

/-! # Time integration by parts and Lions coercivity -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set intervalIntegral
open scoped InnerProductSpace

namespace PDE.Parabolic.Lions

private theorem cauchyTimeSlice_deriv {d : ℕ} {φ : Vec d × ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (x : Vec d) (t : ℝ) :
    deriv (fun τ : ℝ => φ (x, τ)) t = parTimeDeriv φ (x, t) := by
  have h1 : HasFDerivAt φ (fderiv ℝ φ (x, t)) (x, t) :=
    ((hφ.differentiable one_ne_zero (x, t)).hasFDerivAt)
  have h2 : HasDerivAt (fun τ : ℝ => ((x, τ) : Vec d × ℝ)) ((0 : Vec d), 1) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  exact (h1.comp_hasDerivAt t h2).deriv

private theorem cauchyTimeSlice_sq_deriv {d : ℕ} {φ : Vec d × ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (x : Vec d) (t : ℝ) :
    deriv (fun τ : ℝ => φ (x, τ) ^ 2) t =
      2 * φ (x, t) * parTimeDeriv φ (x, t) := by
  have hq : HasDerivAt (fun τ : ℝ => φ (x, τ)) (parTimeDeriv φ (x, t)) t := by
    have hqC : ContDiff ℝ 1 (fun τ : ℝ => φ (x, τ)) := by
      exact hφ.comp ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => x)).prodMk contDiff_id)
    have h := (hqC.differentiable one_ne_zero t).hasDerivAt
    rw [cauchyTimeSlice_deriv hφ x t] at h
    exact h
  have hmul := hq.mul hq
  have hmulFun : (fun τ : ℝ => φ (x, τ) * φ (x, τ)) =
      (fun τ : ℝ => φ (x, τ)) * (fun τ : ℝ => φ (x, τ)) := by
    funext τ
    rfl
  calc
    deriv (fun τ : ℝ => φ (x, τ) ^ 2) t =
        deriv (fun τ : ℝ => φ (x, τ) * φ (x, τ)) t := by
          congr 1
          funext τ
          ring
    _ = 2 * φ (x, t) * parTimeDeriv φ (x, t) := by
          rw [hmulFun]
          rw [hmul.deriv]
          ring

/-- One-dimensional integration by parts for a terminal-zero Cauchy test. -/
private theorem cauchyTimeSlice_ibp {d : ℕ} {s T : ℝ} (hsT : s < T)
    {φ : CauchyTestSpace d s T} (x : Vec d) :
    ∫ t in Icc s T, (φ : Vec d × ℝ → ℝ) (x, t) *
      parTimeDeriv (φ : Vec d × ℝ → ℝ) (x, t) =
      -(1 / 2 : ℝ) * (φ : Vec d × ℝ → ℝ) (x, s) ^ 2 := by
  let q : ℝ → ℝ := fun t => (φ : Vec d × ℝ → ℝ) (x, t)
  have hq : ContDiff ℝ 1 q := by
    exact φ.property.1.comp
      ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => x)).prodMk contDiff_id)
  have hqderiv : Continuous (deriv (fun t => q t ^ 2)) :=
    (hq.pow 2).continuous_deriv (by norm_num)
  have hchain (t : ℝ) : deriv (fun t => q t ^ 2) t =
      2 * q t * parTimeDeriv (φ : Vec d × ℝ → ℝ) (x, t) := by
    simpa [q] using cauchyTimeSlice_sq_deriv φ.property.1 x t
  have hFTC := intervalIntegral.integral_deriv_eq_sub (a := s) (b := T)
    (fun t _ => ((hq.pow 2).differentiable (by norm_num) t))
    (hqderiv.continuousOn.intervalIntegrable)
  calc
    ∫ t in Icc s T, q t * parTimeDeriv (φ : Vec d × ℝ → ℝ) (x, t) =
        ∫ t in s..T, q t * parTimeDeriv (φ : Vec d × ℝ → ℝ) (x, t) := by
          rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hsT.le]
    _ = (1 / 2 : ℝ) * ∫ t in s..T, deriv (fun t => q t ^ 2) t := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro t ht
          change q t * parTimeDeriv (φ : Vec d × ℝ → ℝ) (x, t) =
            (1 / 2 : ℝ) * deriv (fun t => q t ^ 2) t
          rw [hchain t]
          ring
    _ = (1 / 2 : ℝ) * (q T ^ 2 - q s ^ 2) := by rw [hFTC]
    _ = -(1 / 2 : ℝ) * q s ^ 2 := by
          have hT : q T = 0 := φ.property.2.2 x
          simp [q, hT]

/-- The space-time time-derivative term is the initial trace energy. -/
private theorem cauchyTimeIBP {d : ℕ} {s T : ℝ} (hsT : s < T)
    {φ : CauchyTestSpace d s T} :
    ∫ z in ((univ : Set (Vec d)) ×ˢ Icc s T),
      (φ : Vec d × ℝ → ℝ) z * parTimeDeriv (φ : Vec d × ℝ → ℝ) z =
      -(1 / 2 : ℝ) * ∫ x, (φ : Vec d × ℝ → ℝ) (x, s) ^ 2 := by
  let g : Vec d × ℝ → ℝ := fun z => (φ : Vec d × ℝ → ℝ) z *
    parTimeDeriv (φ : Vec d × ℝ → ℝ) z
  have hc : Continuous g := φ.property.1.continuous.mul (continuous_parTimeDeriv φ.property.1)
  have hK : HasCompactSupport g := by
    apply hasCompactSupport_of_zero_off φ.property.2.1.isCompact
    intro z hz
    have hφz : (φ : Vec d × ℝ → ℝ) z = 0 :=
      image_eq_zero_of_notMem_tsupport hz
    simp [g, hφz]
  have hglobal : Integrable g (volume : Measure (Vec d × ℝ)) :=
    hc.integrable_of_hasCompactSupport hK
  have hrestr : Integrable g (slabMeasure d s T) :=
    hglobal.mono_measure Measure.restrict_le_self
  have hmeasure : slabMeasure d s T =
      (volume : Measure (Vec d)).prod (volume.restrict (Icc s T)) := by
    rw [slabMeasure, PDE.Parabolic.Energy.volume_restrict_prod, Measure.restrict_univ]
  have hfubini : ∫ z, g z ∂slabMeasure d s T =
      ∫ x, ∫ t in Icc s T, g (x, t) := by
    rw [hmeasure]
    exact integral_prod g (by simpa [hmeasure] using hrestr)
  calc
    ∫ z in ((univ : Set (Vec d)) ×ˢ Icc s T),
        (φ : Vec d × ℝ → ℝ) z * parTimeDeriv (φ : Vec d × ℝ → ℝ) z =
        ∫ z, g z ∂slabMeasure d s T := by rfl
    _ = ∫ x, ∫ t in Icc s T, g (x, t) := hfubini
    _ = -(1 / 2 : ℝ) * ∫ x, (φ : Vec d × ℝ → ℝ) (x, s) ^ 2 := by
      rw [← MeasureTheory.integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      exact cauchyTimeSlice_ibp hsT x

private theorem inner_cauchyJ_T {d : ℕ} {s T c lam Lam : ℝ} {a : ParCoeffField d}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (φ : CauchyTestSpace d s T) :
    ⟪cauchyJ φ, cauchyT (c := c) ha φ⟫_ℝ =
      ∫ z, ((φ : Vec d × ℝ → ℝ) z *
        (c * (φ : Vec d × ℝ → ℝ) z - parTimeDeriv (φ : Vec d × ℝ → ℝ) z) +
        vecDot (parSpaceGrad (φ : Vec d × ℝ → ℝ) z)
          (matVecMul (matTranspose (a z)) (parSpaceGrad (φ : Vec d × ℝ → ℝ) z)))
        ∂slabMeasure d s T := by
  have hJ := cauchyJFun_memLp φ
  have hT := cauchyTFun_memLp (c := c) ha φ
  rw [cauchyJ_apply, cauchyT_apply, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hJ.coeFn_toLp, hT.coeFn_toLp] with z hzJ hzT
  rw [hzJ, hzT, WithLp.prod_inner_apply]
  simp [cauchyJFun, cauchyTFun, PDE.inner_toHilbertVec_eq_vecDot]
  ring

private theorem cauchyJ_norm_sq {d : ℕ} {s T : ℝ}
    (φ : CauchyTestSpace d s T) :
    ‖cauchyJ φ‖ ^ 2 =
      ∫ z, ((φ : Vec d × ℝ → ℝ) z ^ 2 +
        vecNormSq (parSpaceGrad (φ : Vec d × ℝ → ℝ) z)) ∂slabMeasure d s T := by
  have hJ := cauchyJFun_memLp φ
  rw [← real_inner_self_eq_norm_sq, cauchyJ_apply, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hJ.coeFn_toLp] with z hz
  rw [hz, WithLp.prod_inner_apply]
  simp [cauchyJFun, vecNormSq, vecDot]
  rw [← real_inner_self_eq_norm_sq, PDE.inner_toHilbertVec_eq_vecDot]
  simp [vecDot]

private theorem cauchyGamma_norm_sq {d : ℕ} {s T : ℝ}
    (φ : CauchyTestSpace d s T) :
    ‖cauchyGamma φ‖ ^ 2 =
      ∫ x, (φ : Vec d × ℝ → ℝ) (x, s) ^ 2 := by
  have hγ := cauchyTraceFun_memLp φ
  rw [← real_inner_self_eq_norm_sq, cauchyGamma_apply, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hγ.coeFn_toLp] with x hx
  rw [hx]
  simp [cauchyTraceFun]

private theorem cauchySlab_neZero {d : ℕ} {s T : ℝ} (hsT : s < T) :
    slabMeasure d s T ≠ 0 := by
  let B : Set (Vec d) := euclideanBall 0 1
  have hB : 0 < volume B := volume_euclideanBall_pos 0 (by norm_num)
  have hI : 0 < volume (Ioo s T) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hsT)
  have hrect : 0 < volume (B ×ˢ Ioo s T) := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_pos hB.ne' hI.ne'
  have hsub : B ×ˢ Ioo s T ⊆ (univ : Set (Vec d)) ×ˢ Icc s T := by
    intro z hz
    exact ⟨Set.mem_univ _, ⟨hz.2.1.le, hz.2.2.le⟩⟩
  have hdomain : 0 < volume ((univ : Set (Vec d)) ×ˢ Icc s T) :=
    lt_of_lt_of_le hrect (measure_mono hsub)
  intro hzero
  have hval := congrArg (fun μ : Measure (Vec d × ℝ) => μ univ) hzero
  rw [slabMeasure, Measure.restrict_apply_univ] at hval
  have hdomain0 : volume ((univ : Set (Vec d)) ×ˢ Icc s T) = 0 := by
    simpa using hval
  exact (ne_of_gt hdomain) hdomain0

private theorem cauchy_lam_pos {d : ℕ} {s T lam Lam : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) : 0 < lam := by
  let : NeZero (slabMeasure d s T) := ⟨cauchySlab_neZero hsT⟩
  obtain ⟨z, hz⟩ := ha.elliptic.exists
  exact hz.1

private theorem vecDot_matVecMul_transpose {d : ℕ} (x y : Vec d) (A : Mat d) :
    vecDot x (matVecMul (matTranspose A) y) = vecDot (matVecMul A x) y := by
  calc
    vecDot x (matVecMul (matTranspose A) y)
        = ∑ i, ∑ j, x i * (A j i * y j) := by
          unfold vecDot matVecMul matTranspose
          congr with i
          rw [Finset.mul_sum]
          simp only [Matrix.transpose_apply]
    _ = ∑ j, ∑ i, (A j i * x i) * y j := by
          rw [Finset.sum_comm]
          congr with j
          congr with i
          ring
    _ = ∑ j, (∑ i, A j i * x i) * y j := by
          congr with j
          exact (Finset.sum_mul Finset.univ (fun i => A j i * x i) (y j)).symm
    _ = vecDot (matVecMul A x) y := rfl

private theorem transpose_quadratic_eq {d : ℕ} (A : Mat d) (x : Vec d) :
    vecDot x (matVecMul (matTranspose A) x) = vecDot x (matVecMul A x) := by
  rw [vecDot_matVecMul_transpose]
  exact vecDot_comm _ _

private theorem cauchyTimeProduct_integrable {d : ℕ} {s T : ℝ}
    {φ : CauchyTestSpace d s T} :
    Integrable (fun z => (φ : Vec d × ℝ → ℝ) z *
      parTimeDeriv (φ : Vec d × ℝ → ℝ) z) (slabMeasure d s T) := by
  let g : Vec d × ℝ → ℝ := fun z => (φ : Vec d × ℝ → ℝ) z *
    parTimeDeriv (φ : Vec d × ℝ → ℝ) z
  have hc : Continuous g := φ.property.1.continuous.mul (continuous_parTimeDeriv φ.property.1)
  have hK : HasCompactSupport g := by
    apply hasCompactSupport_of_zero_off φ.property.2.1.isCompact
    intro z hz
    have hφz : (φ : Vec d × ℝ → ℝ) z = 0 :=
      image_eq_zero_of_notMem_tsupport hz
    simp [g, hφz]
  exact (hc.integrable_of_hasCompactSupport hK).mono_measure Measure.restrict_le_self

private theorem cauchyJ_T_pointwise {d : ℕ} {s T : ℝ}
    {a : ParCoeffField d} (φ : CauchyTestSpace d s T) (z : Vec d × ℝ) :
    inner ℝ (cauchyJFun (φ : Vec d × ℝ → ℝ) z)
        (cauchyTFun 1 a (φ : Vec d × ℝ → ℝ) z) =
      (φ : Vec d × ℝ → ℝ) z *
        ((φ : Vec d × ℝ → ℝ) z - parTimeDeriv (φ : Vec d × ℝ → ℝ) z) +
      vecDot (parSpaceGrad (φ : Vec d × ℝ → ℝ) z)
        (matVecMul (matTranspose (a z)) (parSpaceGrad (φ : Vec d × ℝ → ℝ) z)) := by
  rw [WithLp.prod_inner_apply]
  simp [cauchyJFun, cauchyTFun, PDE.inner_toHilbertVec_eq_vecDot]
  ring

private theorem cauchyJ_T_inner_ae {d : ℕ} {s T lam Lam : ℝ}
    {a : ParCoeffField d} (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (φ : CauchyTestSpace d s T) :
    (fun z => inner ℝ (cauchyJ φ z) (cauchyT (c := 1) ha φ z)) =ᵐ[slabMeasure d s T]
      (fun z => (φ : Vec d × ℝ → ℝ) z *
        ((φ : Vec d × ℝ → ℝ) z - parTimeDeriv (φ : Vec d × ℝ → ℝ) z) +
        vecDot (parSpaceGrad (φ : Vec d × ℝ → ℝ) z)
          (matVecMul (matTranspose (a z)) (parSpaceGrad (φ : Vec d × ℝ → ℝ) z))) := by
  have hJ := cauchyJFun_memLp φ
  have hT := cauchyTFun_memLp (c := 1) ha φ
  filter_upwards [hJ.coeFn_toLp, hT.coeFn_toLp] with z hzJ hzT
  rw [cauchyJ_apply, cauchyT_apply, hzJ, hzT]
  exact cauchyJ_T_pointwise φ z

private theorem cauchyJ_T_add_time_ae {d : ℕ} {s T lam Lam : ℝ}
    {a : ParCoeffField d} (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (φ : CauchyTestSpace d s T) :
    (fun z => inner ℝ (cauchyJ φ z) (cauchyT (c := 1) ha φ z) +
      (φ : Vec d × ℝ → ℝ) z * parTimeDeriv (φ : Vec d × ℝ → ℝ) z) =ᵐ[slabMeasure d s T]
      (fun z => (φ : Vec d × ℝ → ℝ) z ^ 2 +
        vecDot (parSpaceGrad (φ : Vec d × ℝ → ℝ) z)
          (matVecMul (matTranspose (a z)) (parSpaceGrad (φ : Vec d × ℝ → ℝ) z))) := by
  filter_upwards [cauchyJ_T_inner_ae ha φ] with z hz
  calc
    inner ℝ (cauchyJ φ z) (cauchyT (c := 1) ha φ z) +
        (φ : Vec d × ℝ → ℝ) z * parTimeDeriv (φ : Vec d × ℝ → ℝ) z =
      ((φ : Vec d × ℝ → ℝ) z *
          ((φ : Vec d × ℝ → ℝ) z - parTimeDeriv (φ : Vec d × ℝ → ℝ) z) +
        vecDot (parSpaceGrad (φ : Vec d × ℝ → ℝ) z)
          (matVecMul (matTranspose (a z)) (parSpaceGrad (φ : Vec d × ℝ → ℝ) z))) +
        (φ : Vec d × ℝ → ℝ) z * parTimeDeriv (φ : Vec d × ℝ → ℝ) z := by
        rw [hz]
    _ = (φ : Vec d × ℝ → ℝ) z ^ 2 +
        vecDot (parSpaceGrad (φ : Vec d × ℝ → ℝ) z)
          (matVecMul (matTranspose (a z)) (parSpaceGrad (φ : Vec d × ℝ → ℝ) z)) := by ring

private theorem cauchyJ_inner_self_ae {d : ℕ} {s T : ℝ}
    (φ : CauchyTestSpace d s T) :
    (fun z => inner ℝ (cauchyJ φ z) (cauchyJ φ z)) =ᵐ[slabMeasure d s T]
      (fun z => (φ : Vec d × ℝ → ℝ) z ^ 2 +
        vecNormSq (parSpaceGrad (φ : Vec d × ℝ → ℝ) z)) := by
  have hJ := cauchyJFun_memLp φ
  filter_upwards [hJ.coeFn_toLp] with z hz
  rw [cauchyJ_apply, hz, WithLp.prod_inner_apply]
  simp [cauchyJFun, vecNormSq, vecDot]
  rw [← real_inner_self_eq_norm_sq, PDE.inner_toHilbertVec_eq_vecDot]
  simp [vecDot]

private theorem cauchyG_integrable {d : ℕ} {s T lam Lam : ℝ}
    {a : ParCoeffField d} (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (φ : CauchyTestSpace d s T) :
    Integrable (fun z => (φ : Vec d × ℝ → ℝ) z ^ 2 +
      vecDot (parSpaceGrad (φ : Vec d × ℝ → ℝ) z)
        (matVecMul (matTranspose (a z)) (parSpaceGrad (φ : Vec d × ℝ → ℝ) z)))
      (slabMeasure d s T) := by
  have hInner : Integrable (fun z => inner ℝ (cauchyJ φ z)
      (cauchyT (c := 1) ha φ z)) (slabMeasure d s T) :=
    MeasureTheory.L2.integrable_inner _ _
  have hTime := cauchyTimeProduct_integrable (φ := φ)
  have hSum := hInner.add hTime
  have hEq := cauchyJ_T_add_time_ae ha φ
  exact (integrable_congr hEq).mp hSum

private theorem cauchyJ_integrand_integrable {d : ℕ} {s T : ℝ}
    (φ : CauchyTestSpace d s T) :
    Integrable (fun z => (φ : Vec d × ℝ → ℝ) z ^ 2 +
      vecNormSq (parSpaceGrad (φ : Vec d × ℝ → ℝ) z)) (slabMeasure d s T) := by
  have hInner : Integrable (fun z => inner ℝ (cauchyJ φ z) (cauchyJ φ z))
      (slabMeasure d s T) := MeasureTheory.L2.integrable_inner _ _
  exact (integrable_congr (cauchyJ_inner_self_ae φ)).mp hInner

theorem cauchy_coercivity {d : ℕ} {s T lam Lam : ℝ}
    {a : ParCoeffField d} (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) :
    let α := min lam (1 / 2 : ℝ)
    0 < α ∧ ∀ φ : CauchyTestSpace d s T,
      α * (‖cauchyJ φ‖ ^ 2 + ‖cauchyGamma φ‖ ^ 2) ≤
        inner ℝ (cauchyJ φ) (cauchyT (c := 1) ha φ) := by
  dsimp only
  let α : ℝ := min lam (1 / 2 : ℝ)
  have hαpos : 0 < α := lt_min (cauchy_lam_pos hsT ha) (by norm_num)
  have hαlam : α ≤ lam := min_le_left _ _
  have hαhalf : α ≤ 1 / 2 := min_le_right _ _
  have hαone : α ≤ 1 := hαhalf.trans (by norm_num)
  refine ⟨hαpos, ?_⟩
  intro φ
  have hFint := cauchyJ_integrand_integrable φ
  have hGint := cauchyG_integrable ha φ
  have hpoint : (fun z => α * ((φ : Vec d × ℝ → ℝ) z ^ 2 +
        vecNormSq (parSpaceGrad (φ : Vec d × ℝ → ℝ) z))) ≤ᵐ[slabMeasure d s T]
      (fun z => (φ : Vec d × ℝ → ℝ) z ^ 2 +
        vecDot (parSpaceGrad (φ : Vec d × ℝ → ℝ) z)
          (matVecMul (matTranspose (a z)) (parSpaceGrad (φ : Vec d × ℝ → ℝ) z))) := by
    filter_upwards [ha.elliptic] with z hz
    have hEll := hz.2.2.1 (parSpaceGrad (φ : Vec d × ℝ → ℝ) z)
    have htranspose := transpose_quadratic_eq (a z) (parSpaceGrad (φ : Vec d × ℝ → ℝ) z)
    rw [← htranspose] at hEll
    calc
      α * ((φ : Vec d × ℝ → ℝ) z ^ 2 +
          vecNormSq (parSpaceGrad (φ : Vec d × ℝ → ℝ) z)) =
        α * ((φ : Vec d × ℝ → ℝ) z ^ 2) + α * vecNormSq (parSpaceGrad (φ : Vec d × ℝ → ℝ) z) := by ring
      _ ≤ (φ : Vec d × ℝ → ℝ) z ^ 2 + lam * vecNormSq (parSpaceGrad (φ : Vec d × ℝ → ℝ) z) := by
        exact add_le_add
          (by simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hαone (sq_nonneg ((φ : Vec d × ℝ → ℝ) z)))
          (mul_le_mul_of_nonneg_right hαlam (vecNormSq_nonneg _))
      _ ≤ (φ : Vec d × ℝ → ℝ) z ^ 2 + vecDot (parSpaceGrad (φ : Vec d × ℝ → ℝ) z)
          (matVecMul (matTranspose (a z)) (parSpaceGrad (φ : Vec d × ℝ → ℝ) z)) := by
        exact add_le_add_right hEll _
  have hmono := MeasureTheory.integral_mono_ae (hFint.const_mul α) hGint hpoint
  have hGsplit :
      (∫ z, (φ : Vec d × ℝ → ℝ) z ^ 2 +
        vecDot (parSpaceGrad (φ : Vec d × ℝ → ℝ) z)
          (matVecMul (matTranspose (a z)) (parSpaceGrad (φ : Vec d × ℝ → ℝ) z))
        ∂slabMeasure d s T) =
      inner ℝ (cauchyJ φ) (cauchyT (c := 1) ha φ) +
        ∫ z, (φ : Vec d × ℝ → ℝ) z * parTimeDeriv (φ : Vec d × ℝ → ℝ) z
          ∂slabMeasure d s T := by
    calc
      _ = ∫ z, inner ℝ (cauchyJ φ z) (cauchyT (c := 1) ha φ z) +
          (φ : Vec d × ℝ → ℝ) z * parTimeDeriv (φ : Vec d × ℝ → ℝ) z
            ∂slabMeasure d s T := integral_congr_ae (cauchyJ_T_add_time_ae ha φ).symm
      _ = (∫ z, inner ℝ (cauchyJ φ z) (cauchyT (c := 1) ha φ z)
            ∂slabMeasure d s T) +
          ∫ z, (φ : Vec d × ℝ → ℝ) z * parTimeDeriv (φ : Vec d × ℝ → ℝ) z
            ∂slabMeasure d s T := integral_add
              (MeasureTheory.L2.integrable_inner _ _) cauchyTimeProduct_integrable
      _ = inner ℝ (cauchyJ φ) (cauchyT (c := 1) ha φ) +
          ∫ z, (φ : Vec d × ℝ → ℝ) z * parTimeDeriv (φ : Vec d × ℝ → ℝ) z
            ∂slabMeasure d s T := by rw [← MeasureTheory.L2.inner_def]
  have htrace : 0 ≤ ∫ x, (φ : Vec d × ℝ → ℝ) (x, s) ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have htime := cauchyTimeIBP hsT (φ := φ)
  have hnormJ := cauchyJ_norm_sq φ
  have hnormΓ := cauchyGamma_norm_sq φ
  have htraceScale := mul_le_mul_of_nonneg_right hαhalf htrace
  rw [← hnormΓ] at htraceScale
  rw [htime] at hGsplit
  have hfinal : inner ℝ (cauchyJ φ) (cauchyT (c := 1) ha φ) =
      (∫ z, (φ : Vec d × ℝ → ℝ) z ^ 2 +
        vecDot (parSpaceGrad (φ : Vec d × ℝ → ℝ) z)
          (matVecMul (matTranspose (a z)) (parSpaceGrad (φ : Vec d × ℝ → ℝ) z))
        ∂slabMeasure d s T) + (1 / 2 : ℝ) * ‖cauchyGamma φ‖ ^ 2 := by
    rw [hGsplit]
    rw [← hnormΓ]
    linarith
  have hmono' : α * (∫ z, (φ : Vec d × ℝ → ℝ) z ^ 2 +
        vecNormSq (parSpaceGrad (φ : Vec d × ℝ → ℝ) z) ∂slabMeasure d s T) ≤
      ∫ z, (φ : Vec d × ℝ → ℝ) z ^ 2 +
        vecDot (parSpaceGrad (φ : Vec d × ℝ → ℝ) z)
          (matVecMul (matTranspose (a z)) (parSpaceGrad (φ : Vec d × ℝ → ℝ) z))
        ∂slabMeasure d s T := by
    calc
      _ = ∫ z, α * ((φ : Vec d × ℝ → ℝ) z ^ 2 +
          vecNormSq (parSpaceGrad (φ : Vec d × ℝ → ℝ) z)) ∂slabMeasure d s T := by
        rw [← MeasureTheory.integral_const_mul]
      _ ≤ _ := hmono
  calc
    α * (‖cauchyJ φ‖ ^ 2 + ‖cauchyGamma φ‖ ^ 2) =
        α * ‖cauchyJ φ‖ ^ 2 + α * ‖cauchyGamma φ‖ ^ 2 := by ring
    _ ≤ α * (∫ z, (φ : Vec d × ℝ → ℝ) z ^ 2 +
          vecNormSq (parSpaceGrad (φ : Vec d × ℝ → ℝ) z) ∂slabMeasure d s T) +
        (1 / 2 : ℝ) * ‖cauchyGamma φ‖ ^ 2 := by
      exact add_le_add
        (by rw [hnormJ])
        htraceScale
    _ ≤ (∫ z, (φ : Vec d × ℝ → ℝ) z ^ 2 +
          vecDot (parSpaceGrad (φ : Vec d × ℝ → ℝ) z)
            (matVecMul (matTranspose (a z)) (parSpaceGrad (φ : Vec d × ℝ → ℝ) z))
          ∂slabMeasure d s T) + (1 / 2 : ℝ) * ‖cauchyGamma φ‖ ^ 2 := by
      exact add_le_add hmono' (le_of_eq rfl)
    _ = inner ℝ (cauchyJ φ) (cauchyT (c := 1) ha φ) := hfinal.symm

end PDE.Parabolic.Lions
