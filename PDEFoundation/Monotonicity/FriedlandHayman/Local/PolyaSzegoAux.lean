module

public import PDEFoundation.Monotonicity.FriedlandHayman.Local.ZonalProfile
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Friedland--Hayman: auxiliary facts for the one-dimensional Pólya--Szegő statement

The absolute value of the restriction of a `C¹` function to the sphere is Lipschitz, nonlocal
energies are monotone in the kernel, and the `sphereIntegral` on the unit sphere is the
integral against `sphMeasure`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PDE.FHLane

noncomputable section

namespace Local

variable {D : ℕ}

/-- The absolute value of the restriction of `f` to the sphere. -/
def absRestrict (f : Vec D → ℝ) (hf : Continuous f) : C(Sph D, ℝ) :=
  ⟨fun ω => |f (ω : HilbertVec D).toVec|,
    (hf.comp (continuous_toVec.comp continuous_subtype_val)).abs⟩

theorem absRestrict_apply (f : Vec D → ℝ) (hf : Continuous f) (x : Sph D) :
    absRestrict f hf x = |f (x : HilbertVec D).toVec| := rfl

theorem sphRestrict_apply (f : Vec D → ℝ) (hf : Continuous f) (x : Sph D) :
    sphRestrict f hf x = f (x : HilbertVec D).toVec := rfl

theorem sphereIntegral_unit (F : Vec D → ℝ) :
    sphereIntegral (0 : Vec D) 1 F = ∫ x : Sph D, F (x : HilbertVec D).toVec ∂(sphMeasure D) := by
  unfold sphereIntegral
  simp only [one_pow, one_mul, zero_add, one_smul]

theorem sphereArea_eq_real_univ (D : ℕ) : sphereArea D = (sphMeasure D).real Set.univ := rfl

theorem lipschitz_sphRestrict {f : Vec D → ℝ} (hf : ContDiff ℝ 1 f) :
    ∃ L : NNReal, LipschitzWith L (sphRestrict f hf.continuous) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Vec D) 1).exists_bound_of_continuousOn
    (hf.continuous_fderiv (by simp)).continuousOn
  have hlip : LipschitzOnWith (Real.toNNReal C) f (Metric.closedBall (0 : Vec D) 1) :=
    (convex_closedBall (0 : Vec D) 1).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x _ => hf.differentiable (by simp) x) (fun x hx => by
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
        exact (hC x hx).trans (le_max_left _ _))
  refine ⟨Real.toNNReal C, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hnx : ∀ z : Sph D, (z : HilbertVec D).toVec ∈ Metric.closedBall (0 : Vec D) 1 := by
    intro z
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (norm_le_vecEuclideanNorm _).trans ?_
    rw [← HilbertVec.norm_eq_vecEuclideanNorm]; simp
  have hdiff : ‖(x : HilbertVec D).toVec - (y : HilbertVec D).toVec‖ ≤
      ‖(x : HilbertVec D) - y‖ := by
    refine (norm_le_vecEuclideanNorm _).trans ?_
    rw [HilbertVec.norm_eq_vecEuclideanNorm]
    exact le_rfl
  have h1 := hlip.dist_le_mul _ (hnx x) _ (hnx y)
  rw [dist_eq_norm] at h1
  rw [Subtype.dist_eq, dist_eq_norm]
  refine h1.trans ?_
  exact mul_le_mul_of_nonneg_left hdiff (by positivity)

theorem lipschitz_absRestrict {f : Vec D → ℝ} (hf : ContDiff ℝ 1 f) :
    ∃ L : NNReal, LipschitzWith L (absRestrict f hf.continuous) := by
  obtain ⟨L, hL⟩ := lipschitz_sphRestrict hf
  refine ⟨L, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  refine le_trans ?_ (hL.dist_le_mul x y)
  rw [Real.dist_eq, Real.dist_eq, absRestrict_apply, absRestrict_apply, sphRestrict_apply,
    sphRestrict_apply]
  exact abs_abs_sub_abs_le_abs_sub _ _

theorem nlEnergy_mono_kern {ε : ℝ} {g g' : C(Sph D, ℝ)}
    (h : ∀ x y : Sph D, (g x - g y) ^ 2 ≤ (g' x - g' y) ^ 2) : nlEnergy ε g ≤ nlEnergy ε g' := by
  rw [nlEnergy_eq_integral, nlEnergy_eq_integral]
  refine integral_mono (integrable_innerEnergy ε g) (integrable_innerEnergy ε g') fun x => ?_
  refine integral_mono (integrable_cap_at x ((continuous_const.sub g.continuous).pow 2) ε)
    (integrable_cap_at x ((continuous_const.sub g'.continuous).pow 2) ε) fun y => ?_
  by_cases hy : Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D)
  · simp only [hy, ↓reduceIte]
    exact h x y
  · simp [hy]

theorem nlEnergy_abs_le {f : Vec D → ℝ} (hf : Continuous f) (ε : ℝ) :
    nlEnergy ε (absRestrict f hf) ≤ nlEnergy ε (sphRestrict f hf) := by
  refine nlEnergy_mono_kern fun x y => ?_
  rw [absRestrict_apply, absRestrict_apply, sphRestrict_apply, sphRestrict_apply]
  have h := abs_abs_sub_abs_le_abs_sub (f (x : HilbertVec D).toVec) (f (y : HilbertVec D).toVec)
  calc (|f (x : HilbertVec D).toVec| - |f (y : HilbertVec D).toVec|) ^ 2
      = |(|f (x : HilbertVec D).toVec| - |f (y : HilbertVec D).toVec|)| ^ 2 := (sq_abs _).symm
    _ ≤ |f (x : HilbertVec D).toVec - f (y : HilbertVec D).toVec| ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = _ := sq_abs _

end Local

end

end PDE.FHLane
