module

public import PDEFoundation.PDE.HarmonicMollified
public import PDEFoundation.PDE.HarmonicReproductionConvolution

/-! # Commuting two compact scalar convolutions -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped Convolution

noncomputable section

variable {d : ℕ}

private theorem lsmul_flip_self :
    (ContinuousLinearMap.lsmul ℝ ℝ).flip = ContinuousLinearMap.lsmul ℝ ℝ := by
  ext
  simp

/-- Scalar convolution on native vectors is commutative. -/
theorem harmonicScalarConvolution_comm (f g : Vec d → ℝ) :
    f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure (Vec d))] g =
      g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f := by
  have h := MeasureTheory.convolution_flip (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := (volume : Measure (Vec d))) (f := g) (g := f)
  rwa [lsmul_flip_self] at h

/-- Associativity when the first two convolution factors are continuous and
compactly supported and the third is locally integrable. -/
theorem harmonicScalarConvolution_assoc_compactSupport {K b g : Vec d → ℝ}
    (hK_supp : HasCompactSupport K) (hKc : Continuous K)
    (hb_supp : HasCompactSupport b) (hbc : Continuous b)
    (hg : LocallyIntegrable g volume) (x₀ : Vec d) :
    ((K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] b)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x₀ =
      (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (b ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g)) x₀ := by
  have hgn : LocallyIntegrable (fun x => ‖g x‖) volume := by
    rw [← locallyIntegrableOn_univ] at hg ⊢
    exact hg.norm
  refine MeasureTheory.convolution_assoc (ContinuousLinearMap.lsmul ℝ ℝ)
    (ContinuousLinearMap.lsmul ℝ ℝ) (ContinuousLinearMap.lsmul ℝ ℝ)
    (ContinuousLinearMap.lsmul ℝ ℝ) (fun x y z => by simp [mul_assoc])
    hKc.aestronglyMeasurable hbc.aestronglyMeasurable hg.aestronglyMeasurable ?_ ?_ ?_
  · filter_upwards with y
    exact hK_supp.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (hf := hKc) (hg := hbc.locallyIntegrable) y
  · filter_upwards with x
    exact hb_supp.norm.convolutionExists_left (L := ContinuousLinearMap.mul ℝ ℝ)
      (hf := hbc.norm) (hg := hgn) x
  · exact hK_supp.norm.convolutionExists_left (L := ContinuousLinearMap.mul ℝ ℝ)
      (hf := hKc.norm)
      (hg := (hb_supp.norm.continuous_convolution_left (L := ContinuousLinearMap.mul ℝ ℝ)
        hbc.norm hgn).locallyIntegrable) x₀

/-- Two continuous compact scalar kernels commute when applied to a locally
integrable field. -/
theorem harmonicScalarConvolution_double_comm {K b g : Vec d → ℝ}
    (hK_supp : HasCompactSupport K) (hKc : Continuous K)
    (hb_supp : HasCompactSupport b) (hbc : Continuous b)
    (hg : LocallyIntegrable g volume) (x₀ : Vec d) :
    (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (b ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g)) x₀ =
      (b ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g)) x₀ := by
  rw [← harmonicScalarConvolution_assoc_compactSupport hK_supp hKc hb_supp hbc hg x₀,
    harmonicScalarConvolution_comm K b,
    harmonicScalarConvolution_assoc_compactSupport hb_supp hbc hK_supp hKc hg x₀]

end

end PDE
