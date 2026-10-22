module

public import EllipticRegularity.Parabolic.Rescale.AffineMaps
public import EllipticRegularity.Parabolic.ParabolicDef

/-!
# Test functions and derivatives under the parabolic rescaling

For `φ ∈ C¹` the composition `φ ∘ Φ` has `∂ₛ(φ ∘ Φ) = r² (∂ₜφ) ∘ Φ` and
`∇(φ ∘ Φ) = r (∇φ) ∘ Φ`.  A unit-cylinder test function `φ̃` is pulled back to a test function
`φ̃ ∘ Φ⁻¹` on `B(c, r) × interior I'`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.Rescale

variable {d : ℕ}

/-- The linear part of `cylMap c r T₀`. -/
noncomputable def cylLin (d : ℕ) (r : ℝ) : Vec d × ℝ →L[ℝ] Vec d × ℝ :=
  (r • ContinuousLinearMap.fst ℝ (Vec d) ℝ).prod ((r ^ 2) • ContinuousLinearMap.snd ℝ (Vec d) ℝ)

theorem hasFDerivAt_cylMap (c : Vec d) (r T₀ : ℝ) (z : Vec d × ℝ) :
    HasFDerivAt (cylMap c r T₀) (cylLin d r) z := by
  have h1 : HasFDerivAt (fun z : Vec d × ℝ => c + r • z.1)
      (r • ContinuousLinearMap.fst ℝ (Vec d) ℝ) z :=
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := z)).const_smul r).const_add c
  have h2 : HasFDerivAt (fun z : Vec d × ℝ => T₀ + r ^ 2 * z.2)
      ((r ^ 2) • ContinuousLinearMap.snd ℝ (Vec d) ℝ) z :=
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := z)).const_smul (r ^ 2)).const_add T₀
  exact h1.prodMk h2

theorem parTimeDeriv_comp_cylMap (c : Vec d) (r T₀ : ℝ) {φ : Vec d × ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (z : Vec d × ℝ) :
    parTimeDeriv (φ ∘ cylMap c r T₀) z = r ^ 2 * parTimeDeriv φ (cylMap c r T₀ z) := by
  have hd : DifferentiableAt ℝ φ (cylMap c r T₀ z) :=
    (hφ.differentiable (by norm_num)).differentiableAt
  unfold parTimeDeriv
  rw [fderiv_comp z hd (hasFDerivAt_cylMap c r T₀ z).differentiableAt,
    (hasFDerivAt_cylMap c r T₀ z).fderiv]
  have : cylLin d r ((0 : Vec d), (1 : ℝ)) = (r ^ 2) • ((0 : Vec d), (1 : ℝ)) := by
    ext <;> simp [cylLin]
  simp only [ContinuousLinearMap.comp_apply, this, map_smul, smul_eq_mul]

theorem parSpaceGrad_comp_cylMap (c : Vec d) (r T₀ : ℝ) {φ : Vec d × ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (z : Vec d × ℝ) :
    parSpaceGrad (φ ∘ cylMap c r T₀) z = r • parSpaceGrad φ (cylMap c r T₀ z) := by
  have hd : DifferentiableAt ℝ φ (cylMap c r T₀ z) :=
    (hφ.differentiable (by norm_num)).differentiableAt
  funext i
  unfold parSpaceGrad
  rw [fderiv_comp z hd (hasFDerivAt_cylMap c r T₀ z).differentiableAt,
    (hasFDerivAt_cylMap c r T₀ z).fderiv]
  have : cylLin d r (basisVec i, (0 : ℝ)) = r • (basisVec i, (0 : ℝ)) := by
    ext <;> simp [cylLin]
  simp only [ContinuousLinearMap.comp_apply, this, map_smul, smul_eq_mul, Pi.smul_apply]

theorem vecDot_smul_smul' (x y : Vec d) (a b : ℝ) :
    vecDot (a • x) (b • y) = a * b * vecDot x y := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem matVecMul_smul' (A : Mat d) (a : ℝ) (x : Vec d) :
    matVecMul A (a • x) = a • matVecMul A x := by
  funext i
  simp only [matVecMul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The inverse rescaling `w ↦ (r⁻¹ • (w.1 - c), (w.2 - T₀) / r ^ 2)`. -/
noncomputable def cylInv (c : Vec d) (r T₀ : ℝ) : Vec d × ℝ → Vec d × ℝ :=
  fun w => (r⁻¹ • (w.1 - c), (w.2 - T₀) / r ^ 2)

/-- `cylMap` as a homeomorphism. -/
noncomputable def cylHomeo (c : Vec d) {r : ℝ} (hr : 0 < r) (T₀ : ℝ) :
    (Vec d × ℝ) ≃ₜ (Vec d × ℝ) :=
  Homeomorph.prodCongr
    ((Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft c))
    ((Homeomorph.mulLeft₀ (r ^ 2) (pow_pos hr 2).ne').trans (Homeomorph.addLeft T₀))

theorem cylHomeo_apply (c : Vec d) {r : ℝ} (hr : 0 < r) (T₀ : ℝ) (z : Vec d × ℝ) :
    cylHomeo c hr T₀ z = cylMap c r T₀ z := rfl

theorem cylMap_cylInv (c : Vec d) {r : ℝ} (hr : 0 < r) (T₀ : ℝ) (w : Vec d × ℝ) :
    cylMap c r T₀ (cylInv c r T₀ w) = w := by
  have hr2 : r ^ 2 ≠ 0 := (pow_pos hr 2).ne'
  refine Prod.ext ?_ ?_
  · ext i
    simp [cylMap_apply, cylInv, hr.ne']
  · simp [cylMap_apply, cylInv]
    field_simp
    ring

theorem cylHomeo_symm_apply (c : Vec d) {r : ℝ} (hr : 0 < r) (T₀ : ℝ) (w : Vec d × ℝ) :
    (cylHomeo c hr T₀).symm w = cylInv c r T₀ w :=
  (Homeomorph.symm_apply_eq _).2 (cylMap_cylInv c hr T₀ w).symm

theorem contDiff_cylInv (c : Vec d) (r T₀ : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (cylInv c r T₀) := by
  unfold cylInv
  refine ContDiff.prodMk ?_ ?_
  · exact (contDiff_const_smul r⁻¹).comp (contDiff_fst.sub contDiff_const)
  · exact (contDiff_snd.sub contDiff_const).div_const _

theorem tsupport_comp_cylInv_subset (c : Vec d) {r : ℝ} (hr : 0 < r) (T₀ : ℝ)
    (φ : ParTestFunction (euclideanBall (0 : Vec d) 1) (interior (Ioc (-1 : ℝ) 0))) :
    tsupport (φ.toFun ∘ cylInv c r T₀) ⊆ euclideanBall c r ×ˢ Ioo (T₀ - r ^ 2) T₀ := by
  have : φ.toFun ∘ cylInv c r T₀ = φ.toFun ∘ ⇑(cylHomeo c hr T₀).symm := by
    funext w; simp [cylHomeo_symm_apply]
  rw [this, tsupport_comp_eq_preimage]
  intro w hw
  have hz := φ.tsupport_subset hw
  set z := (cylHomeo c hr T₀).symm w with hzdef
  have hwz : w = cylMap c r T₀ z := by
    rw [← cylHomeo_apply c hr T₀, hzdef, Homeomorph.apply_symm_apply]
  obtain ⟨hz1, hz2⟩ := hz
  rw [interior_Ioc] at hz2
  refine ⟨?_, ?_⟩
  · have hmem : spaceMap c r z.1 ∈ euclideanBall c r := by
      rw [← spaceMap_image_unitBall c hr]
      exact mem_image_of_mem _ hz1
    rw [hwz]
    exact hmem
  · have hr2 : 0 < r ^ 2 := pow_pos hr 2
    rw [hwz, cylMap_apply]
    constructor
    · have := mul_lt_mul_of_pos_left hz2.1 hr2
      simp only [mul_neg, mul_one] at this
      linarith only [this]
    · have := mul_neg_of_pos_of_neg hr2 hz2.2
      linarith only [this]

/-- Pull a unit-cylinder test function back to `B(c, r) × interior I'`. -/
noncomputable def pullbackTest (c : Vec d) {r : ℝ} (hr : 0 < r) (T₀ : ℝ) {I' : Set ℝ}
    (hI' : Ioc (T₀ - r ^ 2) T₀ ⊆ I')
    (φ : ParTestFunction (euclideanBall (0 : Vec d) 1) (interior (Ioc (-1 : ℝ) 0))) :
    ParTestFunction (euclideanBall c r) (interior I') where
  toFun := φ.toFun ∘ cylInv c r T₀
  contDiff := φ.contDiff.comp (contDiff_cylInv c r T₀)
  hasCompactSupport := by
    have : φ.toFun ∘ cylInv c r T₀ = φ.toFun ∘ ⇑(cylHomeo c hr T₀).symm := by
      funext w; simp [cylHomeo_symm_apply]
    rw [this]
    exact φ.hasCompactSupport.comp_homeomorph _
  tsupport_subset := by
    intro w hw
    obtain ⟨h1, h2⟩ := tsupport_comp_cylInv_subset c hr T₀ φ hw
    refine ⟨h1, ?_⟩
    have hIoo : Ioo (T₀ - r ^ 2) T₀ ⊆ interior I' :=
      isOpen_Ioo.subset_interior_iff.2 (fun t ht => hI' ⟨ht.1, ht.2.le⟩)
    exact hIoo h2

theorem tsupport_pullbackTest_subset (c : Vec d) {r : ℝ} (hr : 0 < r) (T₀ : ℝ) {I' : Set ℝ}
    (hI' : Ioc (T₀ - r ^ 2) T₀ ⊆ I')
    (φ : ParTestFunction (euclideanBall (0 : Vec d) 1) (interior (Ioc (-1 : ℝ) 0))) :
    tsupport (pullbackTest c hr T₀ hI' φ).toFun ⊆
      euclideanBall c r ×ˢ Ioc (T₀ - r ^ 2) T₀ := fun _ hw =>
  let h := tsupport_comp_cylInv_subset c hr T₀ φ hw
  ⟨h.1, ⟨h.2.1, h.2.2.le⟩⟩

theorem pullbackTest_comp_cylMap (c : Vec d) {r : ℝ} (hr : 0 < r) (T₀ : ℝ) {I' : Set ℝ}
    (hI' : Ioc (T₀ - r ^ 2) T₀ ⊆ I')
    (φ : ParTestFunction (euclideanBall (0 : Vec d) 1) (interior (Ioc (-1 : ℝ) 0))) :
    (pullbackTest c hr T₀ hI' φ).toFun ∘ cylMap c r T₀ = φ.toFun := by
  funext z
  have : cylInv c r T₀ (cylMap c r T₀ z) = z := by
    have h := cylMap_cylInv c hr T₀ (cylMap c r T₀ z)
    exact (cylHomeo c hr T₀).injective h
  simp [pullbackTest, this]

end PDE.Parabolic.Rescale
