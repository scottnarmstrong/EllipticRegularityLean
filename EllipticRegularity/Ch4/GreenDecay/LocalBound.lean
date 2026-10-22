module

public import EllipticRegularity.Ch4.GreenDecay.Caccioppoli
public import PDEFoundation.Measure.BallVolume

/-!
# Gradient bound from an oscillation bound (Step 3 of Lemma 4.35)

If `w` solves `-div (b ∇w) = 0` in `B_ρ` (`ρ ≥ 2`) and `m ≤ w ≤ m + Q` a.e. in `B_2`, then
`∫_{B_1} |∇w|² ≤ 4 Λ |B_2| Q²` (Caccioppoli with the radial cutoff between `B_1` and `B_{3/2}`).
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4GreenDecay

open MeasureTheory PDE PDE.Ch4Infra PDE.MeyersDuality

noncomputable section

variable {d : ℕ}

/-- **Gradient bound in `B_1` from the oscillation of `w` in `B_2`.** -/
theorem local_gradient_bound {Λ ρ m Q : ℝ} (hρ : 2 ≤ ρ) {b : CoeffField d}
    (hbm : ∀ i j : Fin d,
      AEMeasurable (fun x => b x i j) (volumeOn (euclideanBall (0 : Vec d) ρ)))
    (hbell : ∀ x ∈ euclideanBall (0 : Vec d) ρ, IsEllipticMatrix 1 Λ (b x))
    (w : H1Function (euclideanBall (0 : Vec d) ρ))
    (hsol : IsWeakDivergenceFormSolutionOn b (euclideanBall (0 : Vec d) ρ) w (0 : Vec d → ℝ) 0)
    (hQ : ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 2)), m ≤ w.toFun x ∧ w.toFun x - m ≤ Q) :
    ∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (w.grad x) ≤
      4 * Λ * (volume (euclideanBall (0 : Vec d) 2)).toReal * Q ^ 2 := by
  have hρ0 : 0 < ρ := by linarith
  have hU : IsOpen (euclideanBall (0 : Vec d) ρ) := isOpen_euclideanBall 0 ρ
  have hfin : volume (euclideanBall (0 : Vec d) ρ) ≠ ⊤ := volume_euclideanBall_ne_top 0 hρ0.le
  have hUm : MeasurableSet (euclideanBall (0 : Vec d) ρ) := hU.measurableSet
  set η := radialCutoff (0 : Vec d) 1 (3 / 2) with hη
  have h12 : (1 : ℝ) < 3 / 2 := by norm_num
  have hηlip : EucLip ((3 / 2 - 1 : ℝ)⁻¹) η := radialCutoff_eucLip 0 h12
  have hK : (0 : ℝ) ≤ (3 / 2 - 1 : ℝ)⁻¹ := by norm_num
  have hclosed : euclideanClosedBall (0 : Vec d) (3 / 2) ⊆ euclideanBall (0 : Vec d) 2 :=
    euclideanClosedBall_subset_euclideanBall (by norm_num) (by norm_num)
  have hB2 : euclideanBall (0 : Vec d) 2 ⊆ euclideanBall (0 : Vec d) ρ :=
    euclideanBall_mono (by norm_num) hρ
  have htsupp : tsupport η ⊆ euclideanClosedBall (0 : Vec d) (3 / 2) :=
    tsupport_radialCutoff_subset 0 h12 (by norm_num)
  have hηc : HasCompactSupport η := hasCompactSupport_radialCutoff 0 h12 (by norm_num)
  have hcacc := caccioppoli_solution_cutoff_open hU hfin hbm hbell hsol (m + Q / 2) hηlip hK
    (abs_radialCutoff_le_one 0 1 (3 / 2)) hηc htsupp
    (hclosed.trans hB2) (isClosed_euclideanClosedBall 0 (3 / 2)).measurableSet
  -- oscillation bound on the closed ball
  have hclosedMeas : MeasurableSet (euclideanClosedBall (0 : Vec d) (3 / 2)) :=
    (isClosed_euclideanClosedBall 0 (3 / 2)).measurableSet
  have hae : ∀ᵐ x ∂(volumeOn (euclideanClosedBall (0 : Vec d) (3 / 2))),
      (w.toFun x - (m + Q / 2)) ^ 2 ≤ Q ^ 2 / 4 := by
    have hae2 : ∀ᵐ x ∂(volumeOn (euclideanClosedBall (0 : Vec d) (3 / 2))), x ∈ euclideanBall (0 : Vec d) 2 ∧
        (m ≤ w.toFun x ∧ w.toFun x - m ≤ Q) := by
      have h1 : ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 2)), m ≤ w.toFun x ∧ w.toFun x - m ≤ Q := hQ
      have h2 : volumeOn (euclideanClosedBall (0 : Vec d) (3 / 2)) ≤
          volumeOn (euclideanBall (0 : Vec d) 2) := Measure.restrict_mono hclosed le_rfl
      have h3 := ae_mono h2 h1
      filter_upwards [h3, ae_restrict_mem hclosedMeas] with x hx hx'
      exact ⟨hclosed hx', hx⟩
    filter_upwards [hae2] with x ⟨_, h1, h2⟩
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]
  have hwL2 : MemL2On (euclideanBall (0 : Vec d) ρ) w.toFun := w.memL2
  have hint : IntegrableOn (fun x => (w.toFun x - (m + Q / 2)) ^ 2)
      (euclideanClosedBall (0 : Vec d) (3 / 2)) := by
    have : IsFiniteMeasure (volumeOn (euclideanBall (0 : Vec d) ρ)) :=
      isFiniteMeasure_volumeOn_euclideanBall 0 hρ0.le
    have h := (w.addConst (-(m + Q / 2))).memL2
    have hfun : (w.addConst (-(m + Q / 2))).toFun = fun x => w.toFun x - (m + Q / 2) := by
      funext x; change w.toFun x + -(m + Q / 2) = _; ring
    rw [hfun] at h
    have := (integrableOn_mul_of_memL2On h h)
    simp only [← pow_two] at this
    exact this.mono_set (hclosed.trans hB2)
  have hint2 : (∫ x in euclideanClosedBall (0 : Vec d) (3 / 2), (w.toFun x - (m + Q / 2)) ^ 2) ≤
      (volume (euclideanBall (0 : Vec d) 2)).toReal * (Q ^ 2 / 4) := by
    have : IsFiniteMeasure (volumeOn (euclideanClosedBall (0 : Vec d) (3 / 2))) :=
      ⟨by simpa [volumeOn] using
        (isCompact_euclideanClosedBall (0 : Vec d) (by norm_num : (0 : ℝ) ≤ 3 / 2)).measure_lt_top⟩
    calc _ ≤ ∫ x in euclideanClosedBall (0 : Vec d) (3 / 2), Q ^ 2 / 4 :=
          integral_mono_ae hint (integrable_const _) hae
      _ = (volume (euclideanClosedBall (0 : Vec d) (3 / 2))).toReal * (Q ^ 2 / 4) := by
          rw [setIntegral_const, smul_eq_mul]
          rfl
      _ ≤ (volume (euclideanBall (0 : Vec d) 2)).toReal * (Q ^ 2 / 4) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact ENNReal.toReal_mono (volume_euclideanBall_ne_top 0 (by norm_num))
            (measure_mono hclosed)
  -- coercivity and `η = 1` on `B_1`
  have hΛ : 0 ≤ Λ := by
    have h0 : (0 : Vec d) ∈ euclideanBall (0 : Vec d) ρ := center_mem_euclideanBall 0 hρ0
    exact (hbell 0 h0).Lam_pos.le
  have hleft : ∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (w.grad x) ≤
      ∫ x in euclideanBall (0 : Vec d) ρ,
        η x ^ 2 * vecDot (matVecMul (b x) (w.grad x)) (w.grad x) := by
    have hflux := memVectorL2On_matVecMul_of_ae_elliptic hUm hbm hbell w.gradMemL2
    have hi1 := integrableOn_vecDot_of_memVectorL2On hflux w.gradMemL2
    have hB1 : euclideanBall (0 : Vec d) 1 ⊆ euclideanBall (0 : Vec d) ρ :=
      euclideanBall_mono (by norm_num) (by linarith)
    have hηmeas : AEStronglyMeasurable (fun x => η x ^ 2) (volumeOn (euclideanBall (0 : Vec d) ρ)) :=
      ((hηlip.continuous hK).pow 2).aestronglyMeasurable
    have hηint : IntegrableOn (fun x => η x ^ 2 * vecDot (matVecMul (b x) (w.grad x)) (w.grad x))
        (euclideanBall (0 : Vec d) ρ) :=
      hi1.bdd_mul (c := 1) hηmeas (Filter.Eventually.of_forall fun x => by
        have h0 := radialCutoff_nonneg (0 : Vec d) 1 (3 / 2) x
        have h1 := radialCutoff_le_one (0 : Vec d) 1 (3 / 2) x
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_one₀ h0 h1)
    have hmemρ : ∀ᵐ x ∂ volumeOn (euclideanBall (0 : Vec d) ρ), x ∈ euclideanBall (0 : Vec d) ρ :=
      (MeasureTheory.ae_restrict_iff' hUm).2 (Filter.Eventually.of_forall fun x hx => hx)
    have hqnn : ∀ᵐ x ∂ volumeOn (euclideanBall (0 : Vec d) ρ),
        0 ≤ η x ^ 2 * vecDot (matVecMul (b x) (w.grad x)) (w.grad x) := by
      filter_upwards [hmemρ] with x hx
      have := (hbell x hx).coercive (w.grad x)
      rw [one_mul, vecDot_comm] at this
      exact mul_nonneg (sq_nonneg _) ((vecNormSq_nonneg _).trans this)
    calc ∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (w.grad x)
        ≤ ∫ x in euclideanBall (0 : Vec d) 1, vecDot (matVecMul (b x) (w.grad x)) (w.grad x) := by
          refine setIntegral_mono_on (integrableOn_vecNormSq_of_memVectorL2On w.gradMemL2 |>.mono_set hB1)
            (hi1.mono_set hB1) (measurableSet_euclideanBall _ _) fun x hx => ?_
          have := (hbell x (hB1 hx)).coercive (w.grad x)
          rw [one_mul, vecDot_comm] at this
          exact this
      _ = ∫ x in euclideanBall (0 : Vec d) 1,
            η x ^ 2 * vecDot (matVecMul (b x) (w.grad x)) (w.grad x) := by
          refine setIntegral_congr_fun (measurableSet_euclideanBall _ _) fun x hx => ?_
          have hxn : vecEuclideanNorm (x - 0) ≤ 1 := by
            have := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hx
            simpa using this.le
          have hη1 : η x = 1 := radialCutoff_eq_one h12 hxn
          simp only [hη1, one_pow, one_mul]
      _ ≤ ∫ x in euclideanBall (0 : Vec d) ρ,
            η x ^ 2 * vecDot (matVecMul (b x) (w.grad x)) (w.grad x) :=
          setIntegral_mono_set hηint hqnn (Filter.Eventually.of_forall hB1)
  calc ∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (w.grad x)
      ≤ ∫ x in euclideanBall (0 : Vec d) ρ,
        η x ^ 2 * vecDot (matVecMul (b x) (w.grad x)) (w.grad x) := hleft
    _ ≤ 4 * Λ * (3 / 2 - 1 : ℝ)⁻¹ ^ 2 * ∫ x in euclideanClosedBall (0 : Vec d) (3 / 2),
          (w.toFun x - (m + Q / 2)) ^ 2 := hcacc
    _ ≤ 4 * Λ * (3 / 2 - 1 : ℝ)⁻¹ ^ 2 *
          ((volume (euclideanBall (0 : Vec d) 2)).toReal * (Q ^ 2 / 4)) :=
        mul_le_mul_of_nonneg_left hint2 (by positivity)
    _ = 4 * Λ * (volume (euclideanBall (0 : Vec d) 2)).toReal * Q ^ 2 := by norm_num; ring

end

end PDE.Ch4GreenDecay
