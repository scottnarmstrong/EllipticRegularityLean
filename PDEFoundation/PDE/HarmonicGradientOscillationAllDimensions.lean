module

public import PDEFoundation.PDE.HarmonicGradientOscillation
public import PDEFoundation.PDE.OneDimensionalFlux
public import PDEFoundation.Sobolev.H1.MeanEnergyTriangle

/-! # Exact harmonic gradient oscillation in every positive dimension -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem centeredVectorMeanL2_eq_zero_of_ae_eq_const
    {d : ℕ} {U : Set (Vec d)} (hUpos : 0 < volume U) (hUtop : volume U < ∞)
    {g : Vec d → Vec d} {c : Vec d}
    (heq : g =ᵐ[volumeOn U] fun _ => c) : centeredVectorMeanL2 U g = 0 := by
  have hmean : vectorIntegralAverage U g = c := by
    funext i
    have hcoord : (fun x => g x i) =ᵐ[volumeOn U] fun _ => c i := by
      simpa only [Function.comp_apply] using! heq.fun_comp (fun v => v i)
    rw [vectorIntegralAverage_apply, integralAverage_congr_ae hcoord]
    exact congrFun (vectorIntegralAverage_const hUpos hUtop c) i
  unfold centeredVectorMeanL2
  rw [hmean]
  have hzero : (fun x => vecNormSq (g x - c)) =ᵐ[volumeOn U] fun _ => 0 := by
    filter_upwards [heq] with x hx
    simp only [hx, sub_self, vecNormSq, vecDot, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero]
  rw [integralAverage_congr_ae hzero]
  simp only [integralAverage, integral_zero, mul_zero, Real.sqrt_zero]

/-- In dimension one the actual weak Laplace equation makes the literal weak
gradient almost everywhere equal to its integral average. -/
theorem oneDimensional_weakHarmonic_grad_ae_eq_average
    {z : Vec 1} {R : ℝ} (hR : 0 < R)
    (u : H1Function (euclideanBall z R))
    (hu : ∀ φ : WeakTestFunction (euclideanBall z R),
      ∫ x in euclideanBall z R, vecDot (u.grad x) (φ.grad x) = 0) :
    u.grad =ᵐ[volumeOn (euclideanBall z R)]
      fun _ => fun _ => integralAverage (euclideanBall z R) (fun x => u.grad x 0) := by
  let U := euclideanBall z R
  have htop : volume U < ∞ :=
    lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top z hR.le)
  let : IsFiniteMeasure (volumeOn U) := isFiniteMeasure_restrict.mpr htop.ne
  have hmat : (fun x => matVecMul (1 : Mat 1) (u.grad x)) = u.grad := by
    funext x
    change (1 : Mat 1).mulVec (u.grad x) = u.grad x
    exact Matrix.one_mulVec _
  have hdata : DivergenceFormL2DataOn (fun _ => (1 : Mat 1)) U u 0 0 := by
    refine ⟨?_, MeasureTheory.MemLp.zero, fun _ => MeasureTheory.MemLp.zero⟩
    simpa only [hmat] using u.gradMemL2
  have hsol : IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat 1)) U u 0 0 := by
    intro φ
    refine ⟨hdata.testable φ, ?_⟩
    simpa [matVecMul, vecDot, Fin.sum_univ_one] using hu φ
  have hflux : IntegrableOn
      (fun x => (matVecMul (1 : Mat 1) (u.grad x)) 0 + (0 : Vec 1 → Vec 1) x 0) U := by
    simpa [matVecMul, Fin.sum_univ_one] using!
      (u.gradMemL2 0).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h := oneDimensional_totalFlux_ae_eq_integralAverage
    (isOpenBoundedConvexDomain_euclideanBall z hR)
    (volume_euclideanBall_pos z hR) htop hsol hflux
  have hcoord : (fun x => u.grad x 0) =ᵐ[volumeOn U]
      fun _ => integralAverage U (fun x => u.grad x 0) := by
    simpa [matVecMul, Fin.sum_univ_one] using h
  filter_upwards [hcoord] with x hx
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact hx

/-- Every concentric subball has zero centered gradient energy for a weak
one-dimensional harmonic function. -/
theorem centeredVectorMeanL2_oneDimensional_weakHarmonic_grad_eq_zero
    {z : Vec 1} {R : ℝ} (hR : 0 < R)
    (u : H1Function (euclideanBall z R))
    (hu : ∀ φ : WeakTestFunction (euclideanBall z R),
      ∫ x in euclideanBall z R, vecDot (u.grad x) (φ.grad x) = 0)
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    centeredVectorMeanL2 (euclideanBall z r) u.grad = 0 := by
  have hsub : euclideanBall z r ⊆ euclideanBall z R := euclideanBall_mono hr.le hrR
  have heq := (oneDimensional_weakHarmonic_grad_ae_eq_average hR u hu).filter_mono
    (ae_mono (Measure.restrict_mono hsub le_rfl))
  exact centeredVectorMeanL2_eq_zero_of_ae_eq_const
    (volume_euclideanBall_pos z hr)
    (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top z hr.le)) heq

/-- Exact linear centered gradient decay for every positive dimension, all
centers and scales, including the outer equation radius. -/
theorem centeredVectorMeanL2_weakHarmonic_grad_decay_of_pos
    {d : ℕ} (hd : 0 < d) {z : Vec d} {R : ℝ} (hR : 0 < R)
    (u : H1Function (euclideanBall z R))
    (hu : ∀ φ : WeakTestFunction (euclideanBall z R),
      ∫ x in euclideanBall z R, vecDot (u.grad x) (φ.grad x) = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbR : b ≤ R) :
    centeredVectorMeanL2 (euclideanBall z a) u.grad ≤
      (a / b) * centeredVectorMeanL2 (euclideanBall z b) u.grad := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  by_cases hd2 : 2 ≤ d
  · exact centeredVectorMeanL2_weakHarmonic_grad_decay hd2 hR u hu ha hab hbR
  · have hd1 : d = 1 := by omega
    subst d
    rw [centeredVectorMeanL2_oneDimensional_weakHarmonic_grad_eq_zero
      hR u hu ha (hab.trans hbR),
      centeredVectorMeanL2_oneDimensional_weakHarmonic_grad_eq_zero
        hR u hu (ha.trans_le hab) hbR]
    simp only [mul_zero, le_refl]

end
end PDE
