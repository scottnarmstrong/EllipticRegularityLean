module

public import EllipticRegularity.Ch4.GreenDecay.Energy

/-!
# Step 2 of Lemma 4.35: duality

`‖g‖² = ∫ u g = ∫ ∇v · a ∇u = -∫_{B_1} f · ∇v ≤ ‖f‖_{L²(B_1)} ‖∇v‖_{L²(B_1)}`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4GreenDecay

open MeasureTheory PDE

noncomputable section

variable {d : ℕ}

theorem vecDot_indicator_left {S : Set (Vec d)} (f : Vec d → Vec d) (w : Vec d) (x : Vec d) :
    vecDot (S.indicator f x) w = S.indicator (fun x => vecDot (f x) w) x := by
  by_cases hx : x ∈ S
  · simp only [Set.indicator_of_mem hx]
  · simp only [Set.indicator_of_notMem hx, vecDot_zero_left']

/-- **Duality estimate** (Step 2 of Lemma 4.35). -/
theorem duality_estimate {R : ℝ} (hR : 1 ≤ R) {a : CoeffField d}
    {f : Vec d → Vec d} (hf : MemVectorL2On (euclideanBall (0 : Vec d) 1) f)
    {g : Vec d → ℝ} {u v : H10Function (euclideanBall (0 : Vec d) R)}
    (hu : IsWeakDivergenceFormH10SolutionOn a (euclideanBall (0 : Vec d) R) u.toH1Function
      (0 : Vec d → ℝ) ((euclideanBall (0 : Vec d) 1).indicator f))
    (hv : IsWeakDivergenceFormH10SolutionOn (adjointCoeffField a) (euclideanBall (0 : Vec d) R)
      v.toH1Function g (0 : Vec d → Vec d))
    (hgu : (∫ x in euclideanBall (0 : Vec d) R, g x * u.toH1Function.toFun x) =
      ∫ x in euclideanBall (0 : Vec d) R, g x ^ 2) :
    (∫ x in euclideanBall (0 : Vec d) R, g x ^ 2) ≤
      Real.sqrt (∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (f x)) *
        Real.sqrt (∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (v.toH1Function.grad x)) := by
  have hB1 : euclideanBall (0 : Vec d) 1 ⊆ euclideanBall (0 : Vec d) R :=
    euclideanBall_mono (by norm_num) hR
  have h1 := (hv u).2
  have h2 := (hu v).2
  simp only [Pi.zero_apply, vecDot_zero_left', integral_zero, sub_zero, zero_mul,
    zero_sub] at h1 h2
  have hpt : ∀ x, vecDot (matVecMul (adjointCoeffField a x) (v.toH1Function.grad x))
      (u.toH1Function.grad x) =
      vecDot (matVecMul (a x) (u.toH1Function.grad x)) (v.toH1Function.grad x) := by
    intro x
    rw [adjointCoeffField_apply, vecDot_comm (matVecMul (matTranspose (a x)) _) _,
      vecDot_matVecMul_transpose'']
  have hG2 : (∫ x in euclideanBall (0 : Vec d) R, g x ^ 2) =
      -∫ x in euclideanBall (0 : Vec d) 1, vecDot (f x) (v.toH1Function.grad x) := by
    rw [← hgu, ← h1]
    simp_rw [hpt]
    rw [h2]
    congr 1
    simp_rw [vecDot_indicator_left]
    exact setIntegral_indicator_eq (measurableSet_euclideanBall _ _) hB1 _
  have hvgrad1 : MemVectorL2On (euclideanBall (0 : Vec d) 1) v.toH1Function.grad :=
    (v.toH1Function.restrict (isOpen_euclideanBall 0 1) hB1).gradMemL2
  have hfn : MemL2On (euclideanBall (0 : Vec d) 1) (fun x => vecEuclideanNorm (f x)) :=
    GradMemLpOn.memLp_vecEuclideanNorm hf
  have hgn : MemL2On (euclideanBall (0 : Vec d) 1)
      (fun x => vecEuclideanNorm (v.toH1Function.grad x)) :=
    GradMemLpOn.memLp_vecEuclideanNorm hvgrad1
  have hcs := integral_mul_le_sqrt hfn hgn
  have e1 : (∫ x in euclideanBall (0 : Vec d) 1, vecEuclideanNorm (f x) ^ 2) =
      ∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (f x) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => vecEuclideanNorm_sq' _)
  have e2 : (∫ x in euclideanBall (0 : Vec d) 1, vecEuclideanNorm (v.toH1Function.grad x) ^ 2) =
      ∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (v.toH1Function.grad x) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => vecEuclideanNorm_sq' _)
  rw [e1, e2] at hcs
  rw [hG2]
  refine le_trans ?_ hcs
  have hint1 := integrableOn_vecDot_of_memVectorL2On hf hvgrad1
  have hint2 : IntegrableOn (fun x => vecEuclideanNorm (f x) * vecEuclideanNorm (v.toH1Function.grad x))
      (euclideanBall (0 : Vec d) 1) := integrableOn_mul_of_memL2On hfn hgn
  rw [← integral_neg]
  refine integral_mono hint1.neg hint2 fun x => ?_
  have := abs_vecDot_le_mul_norm' (f x) (v.toH1Function.grad x)
  exact (neg_le_abs _).trans this

end

end PDE.Ch4GreenDecay
