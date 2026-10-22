module

public import EllipticRegularity.Parabolic.Rescale.AffineWeakGradient
public import EllipticRegularity.Parabolic.ParabolicDef

/-!
# The rescaled parabolic energy function

For `u ∈ H¹_par(B(c, r) × I')` and `Ioc (T₀ - r²) T₀ ⊆ I'`, the function
`ũ = u ∘ Φ` with spatial gradient `r • (∇u) ∘ Φ` is a parabolic energy function on the unit
cylinder `B₁ × (-1, 0]`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.Rescale

variable {d : ℕ}

theorem map_restrict_unitCylinder (c : Vec d) {r : ℝ} (hr : 0 < r) (T₀ : ℝ) :
    ((volume : Measure (Vec d × ℝ)).restrict
        (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)).map (cylMap c r T₀) =
      ENNReal.ofReal ((r ^ (d + 2))⁻¹) •
        (volume : Measure (Vec d × ℝ)).restrict
          (euclideanBall c r ×ˢ Ioc (T₀ - r ^ 2) T₀) := by
  rw [map_restrict_cylMap c hr T₀, cylMap_image_prod, spaceMap_image_unitBall c hr,
    timeMap_image_Ioc T₀ hr]

/-- Spatial `L²_c` transfer: `ψ̃ ∈ L²_c(B₁)` gives `ψ̃ ∘ Ψ⁻¹ ∈ L²_c(B(c,r))`. -/
theorem isL2c_comp_spaceMap_inv (c : Vec d) {r : ℝ} (hr : 0 < r) {ψ : Vec d → ℝ}
    (hψ : IsL2c (euclideanBall (0 : Vec d) 1) ψ) :
    IsL2c (euclideanBall c r) (fun x => ψ (r⁻¹ • (x - c))) := by
  obtain ⟨hL2, K, hK, hKU, hK0⟩ := hψ
  have hcomp : (fun x : Vec d => ψ (r⁻¹ • (x - c))) ∘ spaceMap c r = ψ := by
    funext y
    simp [spaceMap_apply, hr.ne']
  refine ⟨?_, spaceMap c r '' K, ?_, ?_, ?_⟩
  · refine memLp_of_comp_of_map_eq_smul (spaceMap_measurableEmbedding c hr)
      (ofReal_inv_pow_ne_zero hr d) ENNReal.ofReal_ne_top
      (by rw [map_restrict_spaceMap c hr, spaceMap_image_unitBall c hr]) ?_
    rw [hcomp]
    exact hL2
  · exact hK.image (continuous_spaceMap c r)
  · rw [← spaceMap_image_unitBall c hr]
    exact image_mono hKU
  · intro x hx
    by_contra hne
    apply hx
    refine ⟨r⁻¹ • (x - c), ?_, ?_⟩
    · by_contra hxK
      exact hne (hK0 _ hxK)
    · ext i
      simp [spaceMap_apply, hr.ne']

/-- The rescaled parabolic energy function `ũ = u ∘ Φ`, with gradient `r • (∇u) ∘ Φ`. -/
noncomputable def rescaleParH1 (c : Vec d) {r : ℝ} (hr : 0 < r) (T₀ : ℝ) {I' : Set ℝ}
    (hI' : Ioc (T₀ - r ^ 2) T₀ ⊆ I') (u : ParH1Function (euclideanBall c r) I') :
    ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) where
  toFun := fun z => u.toFun (cylMap c r T₀ z)
  grad := fun z => r • u.grad (cylMap c r T₀ z)
  memL2 := memLp_comp_of_map_eq_smul (cylMap_measurableEmbedding c hr T₀)
    ENNReal.ofReal_ne_top (map_restrict_unitCylinder c hr T₀)
    (u.memL2.mono_measure (Measure.restrict_mono (prod_mono subset_rfl hI') le_rfl))
  gradMemL2 i := (memLp_comp_of_map_eq_smul (cylMap_measurableEmbedding c hr T₀)
    ENNReal.ofReal_ne_top (map_restrict_unitCylinder c hr T₀)
    ((u.gradMemL2 i).mono_measure
      (Measure.restrict_mono (prod_mono subset_rfl hI') le_rfl))).const_mul r
  sliceWeakGradient := by
    have hae : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioc (T₀ - r ^ 2) T₀)),
        HasWeakGradientOn (euclideanBall c r) (parSlice u.toFun t) (parSlice u.grad t) :=
      ae_mono (Measure.restrict_mono hI' le_rfl) u.sliceWeakGradient
    have h := ae_comp_of_map_eq_smul (timeMap_measurableEmbedding T₀ hr)
      (by rw [map_restrict_timeMap T₀ hr, timeMap_image_Ioc T₀ hr]) hae
    filter_upwards [h] with s hs
    exact hasWeakGradientOn_comp_spaceMap c hr hs
  sliceL2loc t ht K hK hKU := by
    have htI : timeMap T₀ r t ∈ I' := by
      apply hI'
      rw [← timeMap_image_Ioc T₀ hr]
      exact mem_image_of_mem _ ht
    have hsub : spaceMap c r '' K ⊆ euclideanBall c r := by
      rw [← spaceMap_image_unitBall c hr]
      exact image_mono hKU
    exact memLp_comp_of_map_eq_smul (spaceMap_measurableEmbedding c hr)
      ENNReal.ofReal_ne_top (map_restrict_spaceMap c hr K)
      (u.sliceL2loc _ htI _ (hK.image (continuous_spaceMap c r)) hsub)
  weakCont ψ hψ := by
    have h := u.weakCont _ (isL2c_comp_spaceMap_inv c hr hψ)
    have hmaps : MapsTo (timeMap T₀ r) (Ioc (-1 : ℝ) 0) I' := by
      intro t ht
      apply hI'
      rw [← timeMap_image_Ioc T₀ hr]
      exact mem_image_of_mem _ ht
    have hc := (h.comp (continuous_timeMap T₀ r).continuousOn hmaps).const_smul
      (ENNReal.ofReal ((r ^ d)⁻¹)).toReal
    refine hc.congr fun s _ => ?_
    have hmap : ((volume : Measure (Vec d)).restrict (euclideanBall (0 : Vec d) 1)).map
        (spaceMap c r) = ENNReal.ofReal ((r ^ d)⁻¹) •
          (volume : Measure (Vec d)).restrict (euclideanBall c r) := by
      rw [map_restrict_spaceMap c hr, spaceMap_image_unitBall c hr]
    have key := integral_comp_of_map_eq_smul (spaceMap_measurableEmbedding c hr) hmap
      (fun y => u.toFun (y, timeMap T₀ r s) * ψ (r⁻¹ • (y - c)))
    have hpt : ∀ x : Vec d, u.toFun (spaceMap c r x, timeMap T₀ r s) *
        ψ (r⁻¹ • (spaceMap c r x - c)) = u.toFun (spaceMap c r x, timeMap T₀ r s) * ψ x := by
      intro x
      simp [spaceMap_apply, hr.ne']
    simp only [hpt] at key
    exact key

end PDE.Parabolic.Rescale
