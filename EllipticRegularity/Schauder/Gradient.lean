module

public import EllipticRegularity.Schauder.Iteration
public import PDEFoundation.Regularity.GradientScale
public import PDEFoundation.Geometry.EuclideanBall.Interior

/-!
# Interior gradient scale control

The same half-radius comparison applies at every centre in the half-unit
ball. This module records the resulting quantitative interior gradient bound.
The uniform forcing row is an explicit intermediate estimate, subsequently
produced from the source `L^{d/(1-alpha)}` norm.
-/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The interior gradient scale estimate from an actual equation and a
displayed forcing scale bound. -/
theorem schauder_interior_gradient_bound_of_forcing_scale
    (hd : 0 < d) {α delta M : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hdelta : 0 ≤ delta)
    (hsmall : delta ≤ (2 : ℝ) ^ (-3 - (d : ℝ) / 2) * (1 - α))
    (hM : 0 ≤ M) {a : CoeffField d}
    (u : H1Function (euclideanBall (0 : Vec d) 1)) {F : Vec d → Vec d}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hclose : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
      IsMatrixPerturbationLE delta (a x) 1)
    (hF : MemVectorL2On (euclideanBall (0 : Vec d) 1) F)
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u 0 F)
    (hforce : ∀ z ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ,
      0 < r → r ≤ 1 / 2 → r ^ (1 - α) *
        Real.sqrt (integralAverage (euclideanBall z r) (fun x => vecNormSq (F x))) ≤ M) :
    ∀ z ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ,
      0 < r → r ≤ 1 / 2 → r ^ (1 - α) *
        Real.sqrt (integralAverage (euclideanBall z r) (fun x => vecNormSq (u.grad x))) ≤
      ((2 : ℝ) ^ ((d : ℝ) / 2) /
        Real.sqrt (volume (euclideanBall (0 : Vec d) (1 / 2))).toReal) *
        Real.sqrt (∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (u.grad x)) +
      8 * ((2 : ℝ) ^ ((d : ℝ) / 2)) ^ 2 * M / (1 - α) := by
  intro z hz r hr hrhalf
  have hsub := euclideanBall_half_subset_unit_of_center_mem_half hz
  let v := u.restrict (isOpen_euclideanBall z (1 / 2)) hsub
  have hF' : MemVectorL2On (euclideanBall z (1 / 2)) F :=
    fun i => memLpOn_mono hsub (hF i)
  have ha' (i j : Fin d) : AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall z (1 / 2))) :=
    (ha i j).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hdyadic := schauder_dyadic_gradient_bound hd (by norm_num : (0 : ℝ) < 1 / 2)
    hα0 hα1 hdelta hsmall hM v ha'
    (ae_restrict_of_ae_restrict_of_subset hsub hclose) hF'
    (hsol.restrict (isOpen_euclideanBall (0 : Vec d) 1)
      (isOpen_euclideanBall z (1 / 2)) hsub)
    (fun n => hforce z hz _ (dyadicRadius_pos (by norm_num) n)
      (dyadicRadius_le (by norm_num) n))
  have hread := sqrt_integralAverage_vecNormSq_of_dyadic_scale_bound z
    (by norm_num : (0 : ℝ) < 1 / 2) hα1 v.gradMemL2 hdyadic r hr hrhalf
  have hstart : (1 / 2 : ℝ) ^ (1 - α) *
      Real.sqrt (integralAverage (euclideanBall z (1 / 2))
        (fun x => vecNormSq (u.grad x))) ≤
      Real.sqrt (∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (u.grad x)) /
        Real.sqrt (volume (euclideanBall (0 : Vec d) (1 / 2))).toReal := by
    have hweight : (1 / 2 : ℝ) ^ (1 - α) ≤ 1 :=
      Real.rpow_le_one (by norm_num) (by norm_num) (by linarith)
    have hmono := Real.sqrt_le_sqrt (setIntegral_vecNormSq_mono_set hsub u.gradMemL2)
    calc
      _ ≤ Real.sqrt (integralAverage (euclideanBall z (1 / 2))
          (fun x => vecNormSq (u.grad x))) :=
        mul_le_of_le_one_left (Real.sqrt_nonneg _) hweight
      _ ≤ _ := by
        rw [sqrt_integralAverage_vecNormSq_eq]
        have hvol : (volume (euclideanBall z (1 / 2))).toReal =
            (volume (euclideanBall (0 : Vec d) (1 / 2))).toReal := by
          exact (volume_euclideanBall_toReal_eq_unit_mul_of_pos z
            (by norm_num : (0 : ℝ) < 1 / 2)).trans
            (volume_euclideanBall_toReal_eq_unit_mul_of_pos (0 : Vec d)
              (by norm_num : (0 : ℝ) < 1 / 2)).symm
        rw [hvol]
        exact div_le_div_of_nonneg_right hmono (Real.sqrt_nonneg _)
  dsimp only [v] at hread
  simp only [H1Function.restrict_grad] at hread
  calc
    _ ≤ _ := hread
    _ ≤ (2 : ℝ) ^ ((d : ℝ) / 2) *
        (Real.sqrt (∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (u.grad x)) /
          Real.sqrt (volume (euclideanBall (0 : Vec d) (1 / 2))).toReal +
          8 * ((2 : ℝ) ^ ((d : ℝ) / 2) * M) / (1 - α)) :=
      mul_le_mul_of_nonneg_left (add_le_add hstart le_rfl)
        (Real.rpow_nonneg (by norm_num) _)
    _ = _ := by ring

end

end PDE
