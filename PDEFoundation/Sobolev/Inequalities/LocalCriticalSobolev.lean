module

public import PDEFoundation.Sobolev.Cutoff.Ball
public import PDEFoundation.Sobolev.H1.ZeroBoundaryCutoff
public import PDEFoundation.Sobolev.Inequalities.ZeroBoundarySobolev

/-!
# Local critical integrability from the zero-boundary Sobolev inequality

This module records the PDE-independent localization step behind the
De Giorgi iteration.  A quantitative cutoff converts a positive-part
truncation to `H¹₀`; critical Sobolev integrability of that product then
passes back to the inner Euclidean ball through the cutoff plateau.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open Filter MeasureTheory

namespace H1Function

/-- A positive-part truncation of an `H¹` function is locally critical
integrable on every concentric Euclidean ball compactly contained in its
bounded open convex domain.  This contains no PDE or coefficient hypothesis. -/
theorem memLp_positivePartSubConst_sobolevConjugate_two_on_euclideanBall
    {d : ℕ} {U : Set (Vec d)} {u : H1Function U}
    {x₀ : Vec d} {k r R : ℝ}
    (hd : 3 ≤ d) (hU : IsOpenBoundedConvexDomain U)
    (hr : 0 < r) (hrR : r < R)
    (hball : euclideanBall x₀ R ⊆ U) :
    MemLp (fun x => max (u x - k) 0)
      (ENNReal.ofReal (sobolevConjugate d 2))
      (volume.restrict (euclideanBall x₀ r)) := by
  let η : QuantitativeSmoothCutoff
      (euclideanBall x₀ r) (euclideanBall x₀ R) (32 / (R - r)) :=
    quantitativeBallCutoff x₀ hr.le hrR
  let w : H1Function U := u.positivePartSubConst hU k
  let v : H10Function U := w.mulCutoffToH10 hU η hball
  have hGradMem :
      MemLp (fun x => vecEuclideanNorm (v.grad x)) 2 (volumeOn U) :=
    v.gradMemL2.memLp_vecEuclideanNorm
  have hGradNorm_ne_top :
      euclideanFieldELpNormOn U 2 v.grad ≠ ∞ := by
    simpa only [euclideanFieldELpNormOn, eLpNormOn, volumeOn] using
      hGradMem.eLpNorm_ne_top
  have hSob :=
    eLpNormOn_sobolevConjugate_two_le_euclideanFieldELpNormOn hd v
  have hvMem : MemLp v.toFun
      (ENNReal.ofReal (sobolevConjugate d 2)) (volumeOn U) := by
    apply lt_of_le_of_lt (by
      simpa only [eLpNormOn, volumeOn] using hSob)
    exact lt_top_iff_ne_top.mpr <|
      ENNReal.mul_ne_top ENNReal.coe_ne_top hGradNorm_ne_top
  have hinnerU : euclideanBall x₀ r ⊆ U :=
    (euclideanBall_mono hr.le hrR.le).trans hball
  have hvMemInner : MemLp v.toFun
      (ENNReal.ofReal (sobolevConjugate d 2))
      (volume.restrict (euclideanBall x₀ r)) := by
    have h := hvMem.restrict (euclideanBall x₀ r)
    rwa [show (volumeOn U).restrict (euclideanBall x₀ r) =
      volume.restrict (euclideanBall x₀ r) by
        exact Measure.restrict_restrict_of_subset hinnerU] at h
  have hvValue : v.toFun = fun x => η x * max (u x - k) 0 := by
    dsimp only [v, w]
    rw [mulCutoffToH10_toFun, positivePartSubConst_toFun]
  have hplateau : (fun x => max (u x - k) 0) =ᵐ[
      volume.restrict (euclideanBall x₀ r)] v.toFun := by
    filter_upwards [ae_restrict_mem
      (isOpen_euclideanBall x₀ r).measurableSet] with x hx
    rw [hvValue]
    change max (u x - k) 0 = η x * max (u x - k) 0
    rw [η.eq_one_on_inner x hx]
    ring
  exact (memLp_congr_ae hplateau).mpr hvMemInner

/-- The same local critical-integrability result with the exponent expanded
to the form consumed by the De Giorgi superlevel estimate. -/
theorem memLp_positivePartSubConst_two_mul_div_sub_two_on_euclideanBall
    {d : ℕ} {U : Set (Vec d)} {u : H1Function U}
    {x₀ : Vec d} {k r R : ℝ}
    (hd : 3 ≤ d) (hU : IsOpenBoundedConvexDomain U)
    (hr : 0 < r) (hrR : r < R)
    (hball : euclideanBall x₀ R ⊆ U) :
    MemLp (fun x => max (u x - k) 0)
      (ENNReal.ofReal ((2 : ℝ) * d / ((d : ℝ) - 2)))
      (volume.restrict (euclideanBall x₀ r)) := by
  simpa only [sobolevConjugate, mul_comm] using
    memLp_positivePartSubConst_sobolevConjugate_two_on_euclideanBall
      (u := u) (k := k) hd hU hr hrR hball

end H1Function

end PDE
