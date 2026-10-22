module

public import PDEFoundation.Sobolev.Inequalities.ConvexSobolevPoincareNormalizedStep3
public import PDEFoundation.Sobolev.W1p.LinearChangeAffine
public import PDEFoundation.Geometry.ConvexNormalization

/-!
# Step 4: the Sobolev--Poincaré inequality on general convex domains

Transfer of the normalized estimate through the affine normalization of a bounded open convex
set. The constant depends only on the dimension, the factor `γ_p`, and the diameter.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE

variable {d : ℕ}

/-- Affine images of open bounded convex sets are open bounded convex sets. -/
theorem IsOpenBoundedConvexDomain.affineImage {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (e : Vec d ≃L[ℝ] Vec d) (b : Vec d) :
    IsOpenBoundedConvexDomain ((fun x => e x + b) '' V) := by
  have hhomeo : (fun x => e x + b) '' V = (fun y => e.symm (y - b)) ⁻¹' V := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨e.symm (y - b), hy, by simp⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hhomeo]
    exact hV.isOpen.preimage (e.symm.continuous.comp (continuous_id.sub continuous_const))
  · have hb : Bornology.IsBounded V := hV.isBoundedDomain.isBounded
    have hmap : Bornology.IsBounded ((fun x => e x + b) '' V) := by
      have h1 : Bornology.IsBounded ((e : Vec d →L[ℝ] Vec d) '' V) :=
        Bornology.IsBounded.image (e : Vec d →L[ℝ] Vec d) hb
      have h2 : (fun x => e x + b) '' V = (fun z => z + b) '' ((e : Vec d →L[ℝ] Vec d) '' V) := by
        ext y; simp only [Set.mem_image]; constructor
        · rintro ⟨x, hx, rfl⟩; exact ⟨e x, ⟨x, hx, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩
      rw [h2]
      exact (isometry_add_right b).lipschitzWith.isBounded_image h1
    exact Bornology.IsBounded.isBoundedDomain hmap
  · have hlin : Convex ℝ ((e : Vec d →ₗ[ℝ] Vec d) '' V) := hV.convex.linear_image _
    have h3 : (fun x => e x + b) '' V = (fun z => b + z) '' ((e : Vec d →ₗ[ℝ] Vec d) '' V) := by
      ext y; simp only [Set.mem_image]; constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨e x, ⟨x, hx, rfl⟩, add_comm _ _⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, add_comm _ _⟩
    rw [h3]
    exact hlin.translate b


/-- A nonempty open bounded set has positive finite volume. -/
theorem volume_pos_lt_top_of_isOpenBoundedConvexDomain {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty) :
    0 < volume V ∧ volume V < ∞ := by
  refine ⟨hV.isOpen.measure_pos volume hne, ?_⟩
  exact hV.isBoundedDomain.isBounded.measure_lt_top

/-- Sobolev--Poincaré on a general bounded convex domain, with the diameter factor. -/
theorem exists_convexSobolevPoincare_of_normalized (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 1 ≤ p → p < d → ∀ (V : Set (Vec d)) (D : ℝ),
      IsOpenBoundedConvexDomain V → V.Nonempty → HasEuclideanDiameterLE V D →
      ∀ u : W1pFunction V (ENNReal.ofReal p),
        eLpMeanNormOn V (ENNReal.ofReal (sobolevConjugate d p))
            (fun x => u.toFun x - integralAverage V u.toFun) ≤
          ENNReal.ofReal (C * (p * ((d : ℝ) - 1) / ((d : ℝ) - p)) * D) *
            euclideanFieldELpMeanNormOn V (ENNReal.ofReal p) u.grad := by
  obtain ⟨C₀, hC₀, hnorm⟩ := exists_normalizedSobolevPoincare_constant (d := d) hd
  refine ⟨C₀ / 2, by positivity, ?_⟩
  intro p hp hpd V D hV hne hD u
  have hd1 : 1 ≤ d := by omega
  have hp' : 1 ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  obtain ⟨A, b, h1, hR, hA⟩ := exists_affine_normalization hd1 hV hne hD
  set W : Set (Vec d) := (fun x => A x + b) '' V with hW
  have hWdom := hV.affineImage A b
  obtain ⟨hVpos, hVtop⟩ := volume_pos_lt_top_of_isOpenBoundedConvexDomain hV hne
  set w : W1pFunction W (ENNReal.ofReal p) := u.affinePush hp' A b with hw
  have hnormal := hnorm p hp hpd W hWdom h1 hR w
  have hD0 : 0 ≤ D := by
    obtain ⟨x, hx⟩ := hne
    have := hD hx hx
    have h0 : 0 ≤ vecEuclideanNorm (x - x) := Real.sqrt_nonneg _
    linarith
  have hL : ∀ z, vecEuclideanNorm (transposeAction A.symm z) ≤ D / 2 * vecEuclideanNorm z :=
    vecEuclideanNorm_transposeAction_le A.symm hA
  have hfun : (fun x => w.toFun x - integralAverage W w.toFun) =
      fun y => (u.toFun (A.symm (y - b)) - integralAverage V u.toFun) := by
    funext y
    have hto : w.toFun = fun y => u.toFun (A.symm (y - b)) :=
      funext (W1pFunction.affinePush_toFun hp' u A b)
    rw [hto, integralAverage_comp_affine_symm A b hVpos hVtop]
  have hleft : eLpMeanNormOn W (ENNReal.ofReal (sobolevConjugate d p))
      (fun x => w.toFun x - integralAverage W w.toFun) =
      eLpMeanNormOn V (ENNReal.ofReal (sobolevConjugate d p))
        (fun x => u.toFun x - integralAverage V u.toFun) := by
    rw [hfun]
    exact eLpMeanNormOn_comp_affine_symm A b V _ (fun x => u.toFun x - integralAverage V u.toFun)
  have hgrad := W1pFunction.euclideanFieldELpMeanNormOn_affinePush_grad_le hp' u A b
    (by linarith : 0 ≤ D / 2) hL
  rw [← hleft]
  refine hnormal.trans ?_
  calc ENNReal.ofReal (C₀ * (p * ((d : ℝ) - 1) / ((d : ℝ) - p))) *
        euclideanFieldELpMeanNormOn W (ENNReal.ofReal p) w.grad
      ≤ ENNReal.ofReal (C₀ * (p * ((d : ℝ) - 1) / ((d : ℝ) - p))) *
          (ENNReal.ofReal (D / 2) *
            euclideanFieldELpMeanNormOn V (ENNReal.ofReal p) u.grad) :=
        mul_le_mul_right hgrad _
    _ = ENNReal.ofReal (C₀ / 2 * (p * ((d : ℝ) - 1) / ((d : ℝ) - p)) * D) *
          euclideanFieldELpMeanNormOn V (ENNReal.ofReal p) u.grad := by
        have hdp : 0 < (d : ℝ) - p := by linarith
        have hγ : 0 ≤ p * ((d : ℝ) - 1) / ((d : ℝ) - p) := by
          apply div_nonneg _ hdp.le
          have : (1 : ℝ) ≤ d := by exact_mod_cast hd1
          nlinarith
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

end PDE
