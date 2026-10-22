module

public import EllipticRegularity.Parabolic.WeakHarnack.LogEstimatePoint
public import EllipticRegularity.Parabolic.ParabolicDef
public import EllipticRegularity.Parabolic.Energy.Slab

/-!
# Space-time integrability for the logarithmic estimate

For `u : ParH1Function (B₁) (-1,0]` and a globally Lipschitz `G` with bounded derivative:
`w = G ∘ u`, `ζ² w`, `ζ² w²`, `|∇u|²` and the quantity `½ζ²|G'(u)∇u|² - 2Λ|∇ζ|²` are integrable on
`B₁ × (-1,0]`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PDE.Parabolic.WeakHarnack

variable {d : ℕ}

/-- The measure space `B₁ × (-1,0]` has finite volume. -/
instance isFiniteMeasure_logCyl (d : ℕ) :
    IsFiniteMeasure (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) := by
  refine isFiniteMeasure_restrict.mpr ?_
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_ne_top (volume_euclideanBall_ne_top 0 zero_le_one) (by simp)

theorem memLp_comp_lipschitz {u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)}
    {G : ℝ → ℝ} {L : NNReal} (hL : LipschitzWith L G) :
    MemLp (fun z => G (u.toFun z)) 2
      (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) := by
  refine ((u.memL2.norm.const_mul (L : ℝ)).add (memLp_const |G 0|)).mono
    (hL.continuous.comp_aestronglyMeasurable u.memL2.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => ?_)
  have := hL.dist_le_mul (u.toFun z) 0
  rw [Real.dist_eq, Real.dist_eq, sub_zero] at this
  simp only [Real.norm_eq_abs, Pi.add_apply]
  have h2 : |G (u.toFun z)| ≤ |G 0| + L * |u.toFun z| := by
    calc |G (u.toFun z)| = |G (u.toFun z) - G 0 + G 0| := by ring_nf
      _ ≤ |G (u.toFun z) - G 0| + |G 0| := abs_add_le _ _
      _ ≤ _ := by linarith
  rw [abs_of_nonneg (by positivity : 0 ≤ (L : ℝ) * |u.toFun z| + |G 0|)]
  linarith

theorem integrable_vecNormSq_grad {u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)} :
    Integrable (fun z => vecNormSq (u.grad z))
      (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) := by
  simp only [vecNormSq_eq_sum_sq]
  exact integrable_finsetSum _ fun i _ => (u.gradMemL2 i).integrable_sq

/-- The lower bound `½ ζ² |G'(u) ∇u|² - 2 Λ |∇ζ|²` for the negative renormalized integrand. -/
noncomputable def logQ (Λ : ℝ) (G : ℝ → ℝ)
    (u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)) (z : Vec d × ℝ) : ℝ :=
  1 / 2 * radialCutoff d z.1 ^ 2 * vecNormSq (deriv G (u.toFun z) • u.grad z) -
    2 * Λ * vecNormSq (spaceGradC1 (radialCutoff d) z.1)

theorem integrable_zeta2_mul {μ : Measure (Vec d × ℝ)} {f : Vec d × ℝ → ℝ}
    (hf : Integrable f μ) : Integrable (fun z => radialCutoff d z.1 ^ 2 * f z) μ := by
  refine hf.bdd_mul (c := 1)
    ((measurable_radialCutoff d).comp measurable_fst |>.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  have h0 := radialCutoff_nonneg (d := d) z.1
  have h1 := radialCutoff_le_one (d := d) z.1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith

theorem integrable_logQ {Λ : ℝ} {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) {M : ℝ}
    (hM : ∀ s, |deriv G s| ≤ M)
    (u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)) :
    Integrable (logQ Λ G u)
      (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hg := integrable_vecNormSq_grad (u := u)
  have hdG : Continuous (deriv G) := hG.continuous_deriv le_rfl
  have hsq : ∀ z, vecNormSq (deriv G (u.toFun z) • u.grad z) =
      deriv G (u.toFun z) ^ 2 * vecNormSq (u.grad z) := fun z => vecNormSq_smul _ _
  have h1 : Integrable (fun z : Vec d × ℝ =>
      1 / 2 * radialCutoff d z.1 ^ 2 * vecNormSq (deriv G (u.toFun z) • u.grad z))
      (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) := by
    refine Integrable.mono' (g := fun z => 1 / 2 * M ^ 2 * vecNormSq (u.grad z))
      (hg.const_mul _) ?_ (Filter.Eventually.of_forall fun z => ?_)
    · simp only [hsq]
      have hz : AEStronglyMeasurable (fun z : Vec d × ℝ => radialCutoff d z.1 ^ 2)
          (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) :=
        ((measurable_radialCutoff d).comp measurable_fst |>.pow_const 2).aestronglyMeasurable
      have hu' : AEStronglyMeasurable (fun z => deriv G (u.toFun z) ^ 2)
          (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) :=
        ((hdG.comp_aestronglyMeasurable u.memL2.aestronglyMeasurable).pow 2)
      exact ((aestronglyMeasurable_const.mul hz).mul (hu'.mul hg.aestronglyMeasurable))
    · simp only [hsq]
      have h0 := radialCutoff_nonneg (d := d) z.1
      have h1 := radialCutoff_le_one (d := d) z.1
      have hn := vecNormSq_nonneg (u.grad z)
      have hz2 : radialCutoff d z.1 ^ 2 ≤ 1 := by nlinarith
      have hd2 : deriv G (u.toFun z) ^ 2 ≤ M ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hM _) 2
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have : radialCutoff d z.1 ^ 2 * deriv G (u.toFun z) ^ 2 ≤ 1 * M ^ 2 :=
        mul_le_mul hz2 hd2 (sq_nonneg _) zero_le_one
      nlinarith
  have h2 : Integrable (fun z : Vec d × ℝ => 2 * Λ * vecNormSq (spaceGradC1 (radialCutoff d) z.1))
      (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) := by
    refine Integrable.mono' (g := fun _ => |2 * Λ| * logGradBound d) (integrable_const _)
      (((continuous_vecNormSq_spaceGrad d).comp continuous_fst).const_mul (2 * Λ)
        |>.aestronglyMeasurable) (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (vecNormSq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (vecNormSq_spaceGrad_le d z.1) (abs_nonneg _)
  exact h1.sub h2

end PDE.Parabolic.WeakHarnack
