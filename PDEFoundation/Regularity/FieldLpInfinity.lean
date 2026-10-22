module

public import PDEFoundation.Measure.NormalizedLp
public import PDEFoundation.Sobolev.H1.Pairing

/-!
# Euclidean essential-supremum bounds for native vector fields

A pointwise bounded representative supplies both actual `L∞` membership and
the corresponding guarded Euclidean field norm bound.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- An almost-everywhere equal, pointwise bounded representative gives an
actual guarded Euclidean `L∞` norm bound for a native vector field. -/
theorem exists_memLp_top_euclideanFieldLpNormOn_le_of_ae_representative
    {U : Set (Vec d)} (hU : MeasurableSet U) {g G : Vec d → Vec d}
    (hg : MemVectorL2On U g) (hG : G =ᵐ[volumeOn U] g)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x ∈ U, vecEuclideanNorm (G x) ≤ B) :
    ∃ htop : MemLp (fun x => vecEuclideanNorm (g x)) ∞ (volumeOn U),
      euclideanFieldLpNormOn U ∞ g htop ≤ B := by
  let f : Vec d → ℝ := fun x => vecEuclideanNorm (g x)
  have hfmeas : AEStronglyMeasurable f (volumeOn U) :=
    hg.memLp_vecEuclideanNorm.aestronglyMeasurable
  have hfae : ∀ᵐ x ∂volumeOn U, ‖f x‖ ≤ B := by
    filter_upwards [hG, ae_restrict_mem hU] with x hxG hxU
    have hx := hbound x hxU
    rw [hxG] at hx
    simpa only [f, Real.norm_eq_abs,
      abs_of_nonneg (vecEuclideanNorm_nonneg (g x))] using hx
  have htop : MemLp f ∞ (volumeOn U) :=
    memLp_top_of_bound hfmeas B hfae
  refine ⟨htop, ?_⟩
  rw [euclideanFieldLpNormOn, lpNormOn_eq_toReal]
  change (eLpNorm f ∞ (volumeOn U)).toReal ≤ B
  rw [eLpNorm_exponent_top hfmeas]
  have hess : eLpNormEssSup f (volumeOn U) ≤ ENNReal.ofReal B :=
    eLpNormEssSup_le_of_ae_bound hfae
  calc
    (eLpNormEssSup f (volumeOn U)).toReal ≤ (ENNReal.ofReal B).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hess
    _ = B := ENNReal.toReal_ofReal hB

end PDE
