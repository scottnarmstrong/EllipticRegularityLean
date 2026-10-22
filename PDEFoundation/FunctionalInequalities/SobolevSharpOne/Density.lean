module

public import PDEFoundation.Measure.LpTendsto
public import PDEFoundation.Measure.FiniteVectorConvergence
public import PDEFoundation.Sobolev.ClassicalGradient
public import PDEFoundation.Sobolev.Inequalities.SobolevWholeSpaceDensity
public import PDEFoundation.Sobolev.W1p.ZeroBoundary
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Density reduction for the sharp `p = 1` Sobolev inequality

If an `L^q`-`W^{1,1}` bound holds for every compactly supported smooth function, with a finite
constant, it holds for every `W^{1,1}(ℝ^d)` representative, for every exponent `q ∈ [1, ∞]`.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE.SobolevSharp

open Filter MeasureTheory

/-- Density/limit reduction: a smooth compact-support `L^q`-`W^{1,1}` bound with constant `K`
passes to every `W^{1,1}(ℝ^d)` function. -/
theorem eLpNorm_le_of_forall_compactSmooth {d : ℕ} {q K : ℝ≥0∞} (hK : K ≠ ∞)
    (h : ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      eLpNorm ψ q volume ≤
        K * eLpNorm (fun x => vecEuclideanNorm (classicalGradient ψ x)) 1 volume)
    (u : W1pFunction (Set.univ : Set (Vec d)) 1) :
    eLpNorm u.toFun q volume ≤
      K * eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 1 volume := by
  obtain ⟨happrox⟩ := W1pFunction.hasSupportedSmoothApproximation_univ (d := d)
    le_rfl ENNReal.one_ne_top u
  have hu_ae : AEStronglyMeasurable u.toFun volume := by
    have := u.memLp.aestronglyMeasurable
    rwa [volumeOn, Measure.restrict_univ] at this
  have hgrad_ae : ∀ i, AEStronglyMeasurable (fun x => u.grad x i) volume := fun i => by
    have := (u.gradMemLp i).aestronglyMeasurable
    rwa [volumeOn, Measure.restrict_univ] at this
  have hψC1 : ∀ n, ContDiff ℝ 1 (happrox.approx n) := fun n =>
    (happrox.approx_smooth n).of_le (by simp)
  have hgψ : ∀ n i, AEStronglyMeasurable
      (fun x => classicalGradient (happrox.approx n) x i) volume := fun n i =>
    (((hψC1 n).continuous_fderiv (by simp)).clm_apply
      continuous_const).aestronglyMeasurable
  set N : (Vec d → Vec d) → ℝ≥0∞ := fun F =>
    eLpNorm (fun x => vecEuclideanNorm (F x)) 1 volume with hN
  have hab : ∀ n, eLpNorm (happrox.approx n) q volume ≤
      K * N (classicalGradient (happrox.approx n)) := fun n =>
    h _ (happrox.approx_smooth n) (happrox.approx_hasCompactSupport n)
  have hvcont : Continuous (fun x : Vec d => vecEuclideanNorm x) := by
    have : (fun x : Vec d => vecEuclideanNorm x) = fun x => Real.sqrt (∑ i, (x i) ^ 2) := by
      funext x; simp [vecEuclideanNorm, vecNormSq_eq_sum_sq]
    rw [this]
    exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
      (continuous_apply i).pow 2)
  have hgcont : ∀ n, Continuous (classicalGradient (happrox.approx n)) := fun n =>
    continuous_pi fun i =>
      ((hψC1 n).continuous_fderiv (by simp)).clm_apply continuous_const
  -- convergence of the gradient norms
  have hdiff : Tendsto (fun n => eLpNorm (fun x => vecEuclideanNorm
      (classicalGradient (happrox.approx n) x - u.grad x)) 1 volume) atTop (𝓝 0) := by
    refine tendsto_eLpNorm_vecEuclideanNorm_sub_zero_of_coordinate (μ := volume)
      (F := fun n => classicalGradient (happrox.approx n)) (G := u.grad) le_rfl
      (fun n i => (hgψ n i).sub (hgrad_ae i)) ?_
    intro i
    have := happrox.tendsto_grad i
    simpa only [volumeOn, Measure.restrict_univ, classicalGradient_apply] using this
  have hNle : ∀ n, N (classicalGradient (happrox.approx n)) ≤ N u.grad +
      eLpNorm (fun x => vecEuclideanNorm
        (classicalGradient (happrox.approx n) x - u.grad x)) 1 volume := by
    intro n
    have hm : AEStronglyMeasurable
        (fun x => vecEuclideanNorm (classicalGradient (happrox.approx n) x)) volume :=
      (hvcont.comp (hgcont n)).aestronglyMeasurable
    calc N (classicalGradient (happrox.approx n))
        ≤ eLpNorm ((fun x => vecEuclideanNorm (u.grad x)) +
            (fun x => vecEuclideanNorm
              (classicalGradient (happrox.approx n) x - u.grad x))) 1 volume := by
          refine eLpNorm_mono_ae_real hm (Eventually.of_forall fun x => ?_)
          rw [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _)]
          have := vecEuclideanNorm_add_le (u.grad x)
            (classicalGradient (happrox.approx n) x - u.grad x)
          simpa [add_sub_cancel, add_comm] using this
      _ ≤ _ := eLpNorm_add_le le_rfl
  have hbt : Tendsto (fun n => K * (N u.grad +
      eLpNorm (fun x => vecEuclideanNorm
        (classicalGradient (happrox.approx n) x - u.grad x)) 1 volume)) atTop
      (𝓝 (K * N u.grad)) := by
    have h1 : Tendsto (fun n => N u.grad +
        eLpNorm (fun x => vecEuclideanNorm
          (classicalGradient (happrox.approx n) x - u.grad x)) 1 volume) atTop
        (𝓝 (N u.grad)) := by
      simpa using tendsto_const_nhds.add hdiff
    exact ENNReal.Tendsto.const_mul h1 (Or.inr hK)
  have htim : TendstoInMeasure volume happrox.approx atTop u.toFun :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 1) (by simp)
      (by simpa only [volumeOn, Measure.restrict_univ] using happrox.tendsto_value)
  obtain ⟨σ, hσ_mono, hσ_ae⟩ := htim.exists_seq_tendsto_ae
  have hfatou : eLpNorm u.toFun q volume ≤
      Filter.liminf (fun n => eLpNorm (happrox.approx (σ n)) q volume) atTop :=
    Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun n => (happrox.approx_smooth (σ n)).continuous.aestronglyMeasurable)
      u.toFun hu_ae hσ_ae
  have hbσ := hbt.comp hσ_mono.tendsto_atTop
  calc eLpNorm u.toFun q volume
      ≤ Filter.liminf (fun n => eLpNorm (happrox.approx (σ n)) q volume) atTop := hfatou
    _ ≤ Filter.liminf (fun n => K * (N u.grad +
        eLpNorm (fun x => vecEuclideanNorm
          (classicalGradient (happrox.approx (σ n)) x - u.grad x)) 1 volume)) atTop := by
        refine Filter.liminf_le_liminf (Eventually.of_forall fun n => ?_)
        exact (hab (σ n)).trans (mul_le_mul_right (hNle (σ n)) K)
    _ = K * N u.grad := hbσ.liminf_eq

end PDE.SobolevSharp
