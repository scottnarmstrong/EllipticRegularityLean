module

public import PDEFoundation.PDE.WeakDivergenceForm
public import PDEFoundation.Sobolev.H1.Affine

/-!
# Translation and positive dilation of divergence-form equations

The existing representative-level affine `H¹` constructors are transported
through the actual smooth-test weak formulation, including every required
integrability field.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

variable {d : ℕ}

private noncomputable def translatedTest {U : Set (Vec d)} (z : Vec d)
    (φ : WeakTestFunction (translateSet z U)) : WeakTestFunction U where
  toFun := fun x => φ (x + z)
  contDiff := φ.contDiff.comp (contDiff_id.add contDiff_const)
  hasCompactSupport := by
    show HasCompactSupport (φ.toFun ∘ Homeomorph.addRight z)
    exact φ.hasCompactSupport.comp_homeomorph (Homeomorph.addRight z)
  tsupport_subset := by
    intro x hx
    have hx' : x + z ∈ tsupport φ.toFun := by
      rw [show (fun y => φ (y + z)) = φ.toFun ∘ Homeomorph.addRight z by rfl,
        tsupport_comp_eq_preimage φ.toFun (Homeomorph.addRight z)] at hx
      exact hx
    simpa using (mem_translateSet_iff_sub_mem.mp (φ.tsupport_subset hx'))

private theorem translatedTest_grad {U : Set (Vec d)} (z : Vec d)
    (φ : WeakTestFunction (translateSet z U)) (x : Vec d) :
    (translatedTest z φ).grad x = φ.grad (x + z) := by
  ext i
  simp only [WeakTestFunction.grad_apply, WeakTestFunction.partialDeriv]
  rw [show (translatedTest z φ).toFun = fun y => φ.toFun (y + z) by rfl,
    fderiv_comp_add_right]

private noncomputable def dilatedTest {U : Set (Vec d)} {r : ℝ}
    (hr : 0 < r) (φ : WeakTestFunction (r • U)) : WeakTestFunction U where
  toFun := fun x => φ (r • x)
  contDiff := φ.contDiff.comp (contDiff_const_smul r)
  hasCompactSupport := by
    show HasCompactSupport (φ.toFun ∘ Homeomorph.smulOfNeZero r hr.ne')
    exact φ.hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero r hr.ne')
  tsupport_subset := by
    intro x hx
    have hx' : r • x ∈ tsupport φ.toFun := by
      rw [show (fun y => φ (r • y)) =
          φ.toFun ∘ Homeomorph.smulOfNeZero r hr.ne' by rfl,
        tsupport_comp_eq_preimage φ.toFun
          (Homeomorph.smulOfNeZero r hr.ne')] at hx
      exact hx
    have hxV : r • x ∈ r • U := φ.tsupport_subset hx'
    simpa [Set.mem_smul_set_iff_inv_smul_mem, hr.ne'] using hxV

private theorem dilatedTest_grad {U : Set (Vec d)} {r : ℝ} (hr : 0 < r)
    (φ : WeakTestFunction (r • U)) (x : Vec d) :
    (dilatedTest hr φ).grad x = r • φ.grad (r • x) := by
  ext i
  simp only [WeakTestFunction.grad_apply, WeakTestFunction.partialDeriv,
    Pi.smul_apply, smul_eq_mul]
  rw [show (dilatedTest hr φ).toFun = fun y => φ.toFun (r • y) by rfl,
    fderiv_comp_smul]
  simp only [smul_eq_mul, smul_apply]

private theorem integrableOn_translate_of_comp_add
    {U : Set (Vec d)} (z : Vec d) {g : Vec d → ℝ}
    (hg : IntegrableOn (fun x => g (x + z)) U volume) :
    IntegrableOn g (translateSet z U) volume := by
  have hmap : Integrable g
      (Measure.map (fun x : Vec d => x + z) (volumeOn U)) :=
    (Homeomorph.addRight z).measurableEmbedding.integrable_map_iff.mpr hg
  rw [(measurePreserving_addRight_restrict_translateSet z U).map_eq] at hmap
  exact hmap

private theorem integrableOn_smul_of_comp_smul
    {U : Set (Vec d)} {r : ℝ} (hr : 0 < r) {g : Vec d → ℝ}
    (hg : IntegrableOn (fun x => g (r • x)) U volume) :
    IntegrableOn g (r • U) volume := by
  have hmap : Integrable g
      (Measure.map (fun x : Vec d => r • x) (volumeOn U)) :=
    (Homeomorph.smulOfNeZero r hr.ne').measurableEmbedding.integrable_map_iff.mpr hg
  rw [map_smul_volumeOn_of_pos hr U] at hmap
  have hc0 : ENNReal.ofReal ((r ^ d)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hr d))).ne'
  exact (integrable_smul_measure hc0 ENNReal.ofReal_ne_top).mp hmap

/-- Translation preserves an actual divergence-form weak equation exactly. -/
theorem IsWeakDivergenceFormSolutionOn.translate
    {U : Set (Vec d)} {a : CoeffField d} {u : H1Function U}
    {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hu : IsWeakDivergenceFormSolutionOn a U u f F) (z : Vec d) :
    IsWeakDivergenceFormSolutionOn
      (fun x => a (x - z)) (translateSet z U) (u.translate z)
      (fun x => f (x - z)) (fun x => F (x - z)) := by
  intro φ
  let ψ : WeakTestFunction U := translatedTest z φ
  have hold := hu ψ
  have hgrad : ∀ x, ψ.grad x = φ.grad (x + z) := translatedTest_grad z φ
  have hfluxComp : IntegrableOn
      (fun x => vecDot (matVecMul (a x) (u.grad x)) (φ.grad (x + z))) U volume :=
    hold.1.flux_integrable.congr
      (Filter.Eventually.of_forall fun x => by
        change vecDot (matVecMul (a x) (u.grad x)) (ψ.grad x) = _
        rw [hgrad x])
  have hsourceComp : IntegrableOn (fun x => f x * φ (x + z)) U volume := by
    simpa only [ψ, translatedTest] using hold.1.source_integrable
  have hforcingComp : IntegrableOn
      (fun x => vecDot (F x) (φ.grad (x + z))) U volume :=
    hold.1.forcing_integrable.congr
      (Filter.Eventually.of_forall fun x => by
        change vecDot (F x) (ψ.grad x) = _
        rw [hgrad x])
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact integrableOn_translate_of_comp_add z (by
      simpa only [H1Function.translate_grad, add_sub_cancel_right] using hfluxComp)
  · exact integrableOn_translate_of_comp_add z (by
      simpa only [add_sub_cancel_right] using hsourceComp)
  · exact integrableOn_translate_of_comp_add z (by
      simpa only [add_sub_cancel_right] using hforcingComp)
  · have hfluxChange := setIntegral_comp_addRight_translateSet z U
      (fun x => vecDot
        (matVecMul (a (x - z)) ((u.translate z).grad x)) (φ.grad x))
    have hsourceChange := setIntegral_comp_addRight_translateSet z U
      (fun x => f (x - z) * φ x)
    have hforcingChange := setIntegral_comp_addRight_translateSet z U
      (fun x => vecDot (F (x - z)) (φ.grad x))
    rw [← hfluxChange, ← hsourceChange, ← hforcingChange]
    simpa only [H1Function.translate_grad, add_sub_cancel_right, hgrad] using! hold.2

/-- Positive dilation with the amplitude-normalized `H¹` representative
preserves the coefficient and forcing scales and introduces the exact
`r⁻¹` scalar-source factor. -/
theorem IsWeakDivergenceFormSolutionOn.dilate_of_pos
    {U : Set (Vec d)} {a : CoeffField d} {u : H1Function U}
    {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hu : IsWeakDivergenceFormSolutionOn a U u f F)
    {r : ℝ} (hr : 0 < r) :
    IsWeakDivergenceFormSolutionOn
      (fun x => a (r⁻¹ • x)) (r • U) (u.dilate hr)
      (fun x => r⁻¹ * f (r⁻¹ • x)) (fun x => F (r⁻¹ • x)) := by
  intro φ
  let ψ : WeakTestFunction U := dilatedTest hr φ
  have hold := hu ψ
  have hgrad : ∀ x, ψ.grad x = r • φ.grad (r • x) := dilatedTest_grad hr φ
  have hrNe : r ≠ 0 := hr.ne'
  have hfluxComp : IntegrableOn
      (fun x => vecDot (matVecMul (a x) (u.grad x)) (φ.grad (r • x))) U volume := by
    have h := hold.1.flux_integrable.const_mul r⁻¹
    apply h.congr
    filter_upwards with x
    rw [hgrad x]
    unfold vecDot
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    field_simp
  have hsourceComp : IntegrableOn
      (fun x => r⁻¹ * f x * φ (r • x)) U volume := by
    simpa only [ψ, dilatedTest, mul_assoc] using! hold.1.source_integrable.const_mul r⁻¹
  have hforcingComp : IntegrableOn
      (fun x => vecDot (F x) (φ.grad (r • x))) U volume := by
    have h := hold.1.forcing_integrable.const_mul r⁻¹
    apply h.congr
    filter_upwards with x
    rw [hgrad x]
    unfold vecDot
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    field_simp
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact integrableOn_smul_of_comp_smul hr (by
      simpa only [H1Function.dilate_grad, inv_smul_smul₀ hrNe] using hfluxComp)
  · exact integrableOn_smul_of_comp_smul hr (by
      simpa only [inv_smul_smul₀ hrNe] using hsourceComp)
  · exact integrableOn_smul_of_comp_smul hr (by
      simpa only [inv_smul_smul₀ hrNe] using hforcingComp)
  · have hfluxScale :
        (∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (ψ.grad x) ∂volume) =
          r * ∫ x in U,
            vecDot (matVecMul (a x) (u.grad x)) (φ.grad (r • x)) ∂volume := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      rw [hgrad x]
      unfold vecDot
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    have hsourceScale :
        (∫ x in U, f x * ψ x ∂volume) =
          r * ∫ x in U, r⁻¹ * f x * φ (r • x) ∂volume := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      simp only [ψ, dilatedTest]
      change f x * φ (r • x) = r * (r⁻¹ * f x * φ (r • x))
      field_simp
    have hforcingScale :
        (∫ x in U, vecDot (F x) (ψ.grad x) ∂volume) =
          r * ∫ x in U, vecDot (F x) (φ.grad (r • x)) ∂volume := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      rw [hgrad x]
      unfold vecDot
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    have hbase :
        (∫ x in U, vecDot (matVecMul (a x) (u.grad x))
          (φ.grad (r • x)) ∂volume) =
          (∫ x in U, r⁻¹ * f x * φ (r • x) ∂volume) -
            ∫ x in U, vecDot (F x) (φ.grad (r • x)) ∂volume := by
      rw [hfluxScale, hsourceScale, hforcingScale] at hold
      exact (mul_left_cancel₀ hrNe (by linear_combination hold.2))
    have hfluxChange := setIntegral_comp_smul_of_pos hr U
      (fun y => vecDot
        (matVecMul (a (r⁻¹ • y)) ((u.dilate hr).grad y)) (φ.grad y))
    have hsourceChange := setIntegral_comp_smul_of_pos hr U
      (fun y => r⁻¹ * f (r⁻¹ • y) * φ y)
    have hforcingChange := setIntegral_comp_smul_of_pos hr U
      (fun y => vecDot (F (r⁻¹ • y)) (φ.grad y))
    have hfluxChange' :
        (∫ x in U, vecDot (matVecMul (a x) (u.grad x))
          (φ.grad (r • x)) ∂volume) =
          (r ^ d)⁻¹ * ∫ y in r • U, vecDot
            (matVecMul (a (r⁻¹ • y)) ((u.dilate hr).grad y))
            (φ.grad y) ∂volume := by
      simpa only [H1Function.dilate_grad, inv_smul_smul₀ hrNe,
        smul_eq_mul] using hfluxChange
    have hsourceChange' :
        (∫ x in U, r⁻¹ * f x * φ (r • x) ∂volume) =
          (r ^ d)⁻¹ * ∫ y in r • U,
            r⁻¹ * f (r⁻¹ • y) * φ y ∂volume := by
      simpa only [inv_smul_smul₀ hrNe, smul_eq_mul] using hsourceChange
    have hforcingChange' :
        (∫ x in U, vecDot (F x) (φ.grad (r • x)) ∂volume) =
          (r ^ d)⁻¹ * ∫ y in r • U,
            vecDot (F (r⁻¹ • y)) (φ.grad y) ∂volume := by
      simpa only [inv_smul_smul₀ hrNe, smul_eq_mul] using hforcingChange
    have hscaleNe : (r ^ d)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero d hrNe)
    apply mul_left_cancel₀ hscaleNe
    rw [← hfluxChange', hbase, hsourceChange', hforcingChange']
    ring

end

end PDE
