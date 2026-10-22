module

public import PDEFoundation.Analysis.Newtonian.Potential.KernelBounds
public import PDEFoundation.Sobolev.ClassicalLaplacian
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Smoothness of the Newton potential via convolution

`newtonPotential F = Σ_i E_i ⋆ F_i`, so smoothness and the coordinate derivative formula follow from
the Mathlib convolution API.
-/

@[expose] public section

open MeasureTheory Set
open scoped Convolution

namespace PDE

noncomputable section

variable {d : ℕ}

/-- The `i`th coordinate of a compactly supported field has compact support. -/
theorem hasCompactSupport_apply {F : Vec d → Vec d} (hFc : HasCompactSupport F) (i : Fin d) :
    HasCompactSupport (fun z => F z i) :=
  hFc.comp_left (g := fun v : Vec d => v i) rfl

/-- The Newton potential as a sum of Mathlib convolutions. -/
theorem newtonPotential_eq_sum_convolution (hd : 0 < d) {F : Vec d → Vec d}
    (hF : Continuous F) (hFc : HasCompactSupport F) (x : Vec d) :
    newtonPotential F x = ∑ i : Fin d,
      ((fun z : Vec d => newtonKernel z i) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
        (fun z => F z i)) x := by
  have hint : ∀ i : Fin d, Integrable (fun t : Vec d => newtonKernel t i * F (x - t) i) volume :=
    fun i => (hasCompactSupport_apply hFc i).convolutionExists_right
      (ContinuousLinearMap.mul ℝ ℝ) (locallyIntegrable_newtonKernel_apply hd i)
      ((continuous_apply i).comp hF) x
  have h1 : newtonPotential F x = ∫ t, vecDot (newtonKernel t) (F (x - t)) := by
    unfold newtonPotential
    rw [← integral_sub_left_eq_self (fun t => vecDot (newtonKernel t) (F (x - t))) (volume : Measure (Vec d)) x]
    simp only [sub_sub_cancel]
  rw [h1]
  unfold vecDot
  rw [integral_finsetSum _ (fun i _ => hint i)]
  rfl

theorem contDiff_newtonPotential (hd : 0 < d) {F : Vec d → Vec d}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) :
    ContDiff ℝ (⊤ : ℕ∞) (newtonPotential F) := by
  have : newtonPotential F = fun x => ∑ i : Fin d,
      ((fun z : Vec d => newtonKernel z i) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
        (fun z => F z i)) x :=
    funext (newtonPotential_eq_sum_convolution hd hF.continuous hFc)
  rw [this]
  refine ContDiff.sum fun i _ => ?_
  exact (hasCompactSupport_apply hFc i).contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (locallyIntegrable_newtonKernel_apply hd i)
    ((contDiff_pi.mp hF) i)

theorem coordDeriv_newtonPotential (hd : 0 < d) {F : Vec d → Vec d}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) (k : Fin d) (x : Vec d) :
    euclideanCoordDeriv k (newtonPotential F) x =
      ∫ y, vecDot (newtonKernel (x - y))
        (fun i => euclideanCoordDeriv k (fun z => F z i) y) := by
  set L := ContinuousLinearMap.mul ℝ ℝ with hL
  have hgs : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun z => F z i) :=
    fun i => (contDiff_pi.mp hF) i
  have hg1 : ∀ i : Fin d, ContDiff ℝ 1 (fun z => F z i) :=
    fun i => (hgs i).of_le (by exact_mod_cast le_top)
  have hdc : ∀ i : Fin d, Continuous (fderiv ℝ (fun z => F z i)) :=
    fun i => (hgs i).continuous_fderiv (by simp)
  have hcd : ∀ i : Fin d, HasCompactSupport (fderiv ℝ (fun z => F z i)) :=
    fun i => (hasCompactSupport_apply hFc i).fderiv ℝ
  have hder : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      HasFDerivAt (((fun z : Vec d => newtonKernel z i) ⋆[L, volume] (fun z => F z i)))
        ((((fun z : Vec d => newtonKernel z i) ⋆[L.precompR (Vec d), volume]
          fderiv ℝ (fun z => F z i)) x)) x :=
    fun i _ => (hasCompactSupport_apply hFc i).hasFDerivAt_convolution_right L
      (locallyIntegrable_newtonKernel_apply hd i) (hg1 i) x
  have hsum := HasFDerivAt.sum hder
  have hfun : newtonPotential F = ∑ i : Fin d,
      ((fun z : Vec d => newtonKernel z i) ⋆[L, volume] (fun z => F z i)) := by
    funext y
    rw [newtonPotential_eq_sum_convolution hd hF.continuous hFc y, Finset.sum_apply]
  unfold euclideanCoordDeriv
  rw [hfun, hsum.fderiv, _root_.sum_apply]
  have hterm : ∀ i : Fin d,
      ((((fun z : Vec d => newtonKernel z i) ⋆[L.precompR (Vec d), volume]
          fderiv ℝ (fun z => F z i)) x)) (basisVec k) =
        ∫ t, newtonKernel t i * fderiv ℝ (fun z => F z i) (x - t) (basisVec k) := by
    intro i
    rw [convolution_precompR_apply L (locallyIntegrable_newtonKernel_apply hd i) (hcd i) (hdc i)]
    rfl
  simp_rw [hterm]
  have hint : ∀ i : Fin d, Integrable
      (fun t : Vec d => newtonKernel t i * fderiv ℝ (fun z => F z i) (x - t) (basisVec k))
      volume := by
    intro i
    have hc : Continuous (fun z => fderiv ℝ (fun z => F z i) z (basisVec k)) :=
      (hdc i).clm_apply continuous_const
    have hs : HasCompactSupport (fun z => fderiv ℝ (fun z => F z i) z (basisVec k)) :=
      (hcd i).comp_left (g := fun L : Vec d →L[ℝ] ℝ => L (basisVec k)) (by simp)
    exact hs.convolutionExists_right L (locallyIntegrable_newtonKernel_apply hd i) hc x
  rw [← integral_finsetSum _ (fun i _ => hint i)]
  rw [← integral_sub_left_eq_self (fun t => ∑ i : Fin d,
    newtonKernel t i * fderiv ℝ (fun z => F z i) (x - t) (basisVec k)) (volume : Measure (Vec d)) x]
  simp only [sub_sub_cancel]
  rfl

end

end PDE
