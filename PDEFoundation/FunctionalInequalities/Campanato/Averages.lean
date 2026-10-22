module

public import PDEFoundation.Sobolev.Mean
public import PDEFoundation.Measure.BallVolume

/-!
# Averages over nested round balls

Elementary comparison of integral averages over nested sets and nested round balls, used in the
Campanato characterisation of Hölder spaces.
-/

@[expose] public section

namespace PDE.CampanatoProof

open MeasureTheory

variable {d : ℕ}

/-- The distance of an average to a constant is controlled by the average of the distance. -/
theorem abs_integralAverage_sub_le {A : Set (Vec d)} {g : Vec d → ℝ} (m : ℝ)
    (hg : IntegrableOn g A) (hpos : 0 < volume A) (hfin : volume A ≠ ⊤) :
    |integralAverage A g - m| ≤ integralAverage A (fun y => |g y - m|) := by
  have hv : 0 < (volume A).toReal := ENNReal.toReal_pos hpos.ne' hfin
  have hconst : IntegrableOn (fun _ : Vec d => m) A volume := integrableOn_const hfin
  have h1 : integralAverage A g - m =
      (volume A).toReal⁻¹ * ∫ y in A, (g y - m) ∂volume := by
    rw [integral_sub hg hconst, setIntegral_const]
    unfold integralAverage
    change _ = (volume A).toReal⁻¹ * ((∫ y in A, g y ∂volume) - (volume A).toReal * m)
    field_simp
  rw [h1, abs_mul, abs_of_pos (inv_pos.mpr hv)]
  unfold integralAverage
  exact mul_le_mul_of_nonneg_left (by simpa using norm_integral_le_integral_norm (μ := volume.restrict A) (fun y => g y - m)) (inv_pos.mpr hv).le

/-- Averages of a nonnegative function over a subset are controlled by the average over the
larger set, with the ratio of volumes. -/
theorem integralAverage_le_of_subset {A B : Set (Vec d)} (hAB : A ⊆ B)
    (hApos : 0 < volume A) (hBfin : volume B ≠ ⊤) {h : Vec d → ℝ}
    (hh : IntegrableOn h B) (h0 : ∀ y, 0 ≤ h y) :
    integralAverage A h ≤
      ((volume B).toReal / (volume A).toReal) * integralAverage B h := by
  have hAfin : volume A ≠ ⊤ := ne_top_of_le_ne_top hBfin (measure_mono hAB)
  have hvA : 0 < (volume A).toReal := ENNReal.toReal_pos hApos.ne' hAfin
  have hvAB : (volume A).toReal ≤ (volume B).toReal :=
    ENNReal.toReal_mono hBfin (measure_mono hAB)
  have hvB : 0 < (volume B).toReal := lt_of_lt_of_le hvA hvAB
  have hint : ∫ y in A, h y ∂volume ≤ ∫ y in B, h y ∂volume :=
    setIntegral_mono_set hh (Filter.Eventually.of_forall h0) (Filter.Eventually.of_forall hAB)
  unfold integralAverage
  calc (volume A).toReal⁻¹ * ∫ y in A, h y ∂volume
      ≤ (volume A).toReal⁻¹ * ∫ y in B, h y ∂volume :=
        mul_le_mul_of_nonneg_left hint (inv_pos.mpr hvA).le
    _ = ((volume B).toReal / (volume A).toReal) *
        ((volume B).toReal⁻¹ * ∫ y in B, h y ∂volume) := by
        field_simp

/-- Comparison of the averages over a subset and the full set, relative to the full average. -/
theorem abs_integralAverage_sub_le_of_subset {A B : Set (Vec d)} (hAB : A ⊆ B)
    (hApos : 0 < volume A) (hBfin : volume B ≠ ⊤) {g : Vec d → ℝ}
    (hg : IntegrableOn g B) :
    |integralAverage A g - integralAverage B g| ≤
      ((volume B).toReal / (volume A).toReal) *
        integralAverage B (fun y => |g y - integralAverage B g|) := by
  have hAfin : volume A ≠ ⊤ := ne_top_of_le_ne_top hBfin (measure_mono hAB)
  refine (abs_integralAverage_sub_le _ (hg.mono_set hAB) hApos hAfin).trans ?_
  exact integralAverage_le_of_subset hAB hApos hBfin
    ((hg.sub (integrableOn_const hBfin)).abs) (fun _ => abs_nonneg _)

/-- Round-ball version: a ball of radius `r` inside a ball of radius `R`. -/
theorem abs_integralAverage_sub_le_of_euclideanBall_subset {x y : Vec d} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hsub : euclideanBall x r ⊆ euclideanBall y R) {g : Vec d → ℝ}
    (hg : IntegrableOn g (euclideanBall y R)) :
    |integralAverage (euclideanBall x r) g - integralAverage (euclideanBall y R) g| ≤
      (R / r) ^ d * integralAverage (euclideanBall y R)
        (fun z => |g z - integralAverage (euclideanBall y R) g|) := by
  have := abs_integralAverage_sub_le_of_subset hsub (volume_euclideanBall_pos x hr)
    (volume_euclideanBall_ne_top y hR.le) hg
  rwa [volume_euclideanBall_toReal_div_eq_div_pow y x hr hR] at this

end PDE.CampanatoProof
