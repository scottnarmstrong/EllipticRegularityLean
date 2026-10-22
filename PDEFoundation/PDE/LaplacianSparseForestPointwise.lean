module

public import PDEFoundation.Measure.CalderonZygmundCubeEnergy
public import PDEFoundation.Measure.ForcingScale
public import PDEFoundation.Measure.DyadicSparseForestDomination
public import PDEFoundation.PDE.LaplacianCubeSparsePointwise

/-! # Pointwise Laplacian sparse forest bound -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory Set
open scoped _root_.ENNReal

noncomputable section

/-- The retained Calderón--Zygmund roots assemble the one-cube Laplacian
sparse estimate into a pointwise forest bound on the inner ball. -/
theorem ae_vecEuclideanNorm_grad_le_laplacian_sparseForest
    {d : ℕ} (hd : 0 < d) {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (u : H1Function (euclideanBall (0 : Vec d) t))
    (F : Vec d → Vec d)
    (hFcoord : ∀ i, AEStronglyMeasurable (fun x => F x i) volume)
    {p : ℝ} (hp : 2 < p)
    (hFp : MemLp (fun x => vecEuclideanNorm (F x))
      (ENNReal.ofReal p) volume)
    (hsol : IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat d))
      (euclideanBall (0 : Vec d) t) u 0 F) :
    ∀ᵐ x ∂volume.restrict (euclideanBall (0 : Vec d) s),
      ENNReal.ofReal (vecEuclideanNorm (u.grad x)) ≤
        ENNReal.ofReal
          ((((1 + 2 * (2 : ℝ) ^ (1 + (d : ℝ) / 2)) *
              Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
                (Real.sqrt d / 2) ^ d) * Real.sqrt ((2 : ℝ) ^ d)) *
            Real.sqrt ((2 / (t - s)) ^ d)) *
            Real.sqrt ((∫ y in euclideanBall (0 : Vec d) t,
              vecNormSq (u.grad y)) /
              (volume (euclideanBall (0 : Vec d) 1)).toReal)) +
        ENNReal.ofReal
          (((2 : ℝ) ^ (1 + (d : ℝ) / 2) *
              Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
                (Real.sqrt d / 2) ^ d)) *
            (((d : ℝ) + 2) / 2 *
              (1 + 2 / (d : ℝ)) ^ ((d : ℝ) / 2))) *
          ∑' k : calderonZygmundRetainedIndices hd hst,
            dyadicSparseSum (calderonZygmundGridBox hd hst k.1)
              (dyadicSparseFamily (calderonZygmundGridBox hd hst k.1) u.grad)
              (dyadicBoxEssentialInfReal
                (calderonZygmundGridBox hd hst k.1)
                (fun y => (quadraticBallMaximal F y).toReal)) x := by
  let C := (2 : ℝ) ^ (1 + (d : ℝ) / 2)
  let D := Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
    (Real.sqrt d / 2) ^ d)
  let κ := ((d : ℝ) + 2) / 2 *
    (1 + 2 / (d : ℝ)) ^ ((d : ℝ) / 2)
  let E := (1 + 2 * C) * D * Real.sqrt ((2 : ℝ) ^ d)
  let G := Real.sqrt ((2 / (t - s)) ^ d) *
    Real.sqrt ((∫ y in euclideanBall (0 : Vec d) t, vecNormSq (u.grad y)) /
      (volume (euclideanBall (0 : Vec d) 1)).toReal)
  let B := C * D * κ
  let root : calderonZygmundRetainedIndices hd hst → Box (Fin d) := fun k =>
    calderonZygmundGridBox hd hst k.1
  let b : Vec d → ℝ := fun y => (quadraticBallMaximal F y).toReal
  have ht : 0 < t := hs.trans hst
  have hF2 : MemVectorL2On (euclideanBall (0 : Vec d) t) F := by
    apply memVectorL2On_euclideanBall_of_memLp_vecEuclideanNorm hp.le
      (0 : Vec d) ht (V := Set.univ) (Set.subset_univ _)
    · simpa only [volumeOn, Measure.restrict_univ] using hFp
    · intro i
      simpa only [volumeOn, Measure.restrict_univ] using hFcoord i
  have hE : 0 ≤ E := by
    dsimp only [E, C, D]
    positivity
  have hB : 0 ≤ B := by
    have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
    have hunit : 0 < (volume (euclideanBall (0 : Vec d) 1)).toReal :=
      volume_euclideanBall_toReal_pos (0 : Vec d) (by norm_num)
    dsimp only [B, C, D, κ]
    positivity
  have hroot (k : calderonZygmundRetainedIndices hd hst) :
      ∀ᵐ x ∂volume, x ∈ (root k : Set (Vec d)) →
        ENNReal.ofReal (vecEuclideanNorm (u.grad x)) ≤
          ENNReal.ofReal (E * G) + ENNReal.ofReal B *
            dyadicSparseSum (root k) (dyadicSparseFamily (root k) u.grad)
              (dyadicBoxEssentialInfReal (root k) b) x := by
    let Rk := 2 * (Real.sqrt d * calderonZygmundCubeSide d s t / 2)
    let Uk := euclideanBall (boxCenter (root k)) Rk
    have hsub : Uk ⊆ euclideanBall (0 : Vec d) t := by
      simpa only [Uk, Rk, root] using
        euclideanBall_two_mul_circumscribedRadius_retained_subset hd hs hst k
    let uk : H1Function Uk := u.restrict (isOpen_euclideanBall _ _) hsub
    have hFk : MemVectorL2On Uk F := fun i => memLpOn_mono hsub (hF2 i)
    have hsolk : IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat d)) Uk uk 0 F :=
      hsol.restrict (isOpen_euclideanBall _ _) (isOpen_euclideanBall _ _) hsub
    have hk := ae_vecEuclideanNorm_grad_le_laplacian_dyadicSparseSum
      (root k) (calderonZygmundCubeSide d s t) hd
      (upper_sub_lower_calderonZygmundGridBox hd hst k.1)
      uk F hFk hsolk hp hFp
    have hk' : ∀ᵐ x ∂volume, x ∈ (root k : Set (Vec d)) →
        ENNReal.ofReal (vecEuclideanNorm (u.grad x)) ≤
          ENNReal.ofReal (E * Real.sqrt (integralAverage Uk
            (fun y => vecNormSq (u.grad y)))) + ENNReal.ofReal B *
            dyadicSparseSum (root k) (dyadicSparseFamily (root k) u.grad)
              (dyadicBoxEssentialInfReal (root k) b) x := by
      apply (ae_restrict_iff' (root k).measurableSet_coe).mp
      simpa only [uk, H1Function.restrict_grad, Uk, Rk, root, b, E, B, C, D, κ,
        mul_assoc] using hk
    have henergy := sqrt_integralAverage_retainedCubeBall_le hd hs hst u.grad
      u.gradMemL2 k
    filter_upwards [hk'] with x hx
    intro hxroot
    refine (hx hxroot).trans (add_le_add ?_ le_rfl)
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left henergy hE)
  let : Countable (calderonZygmundRetainedIndices hd hst) :=
    countable_of_pairwiseDisjoint_box_Ioo root (by
      simpa only [root] using pairwiseDisjoint_calderonZygmundRetained_Ioo hd hst)
  have hall : ∀ᵐ x ∂volume,
      ∀ k : calderonZygmundRetainedIndices hd hst,
        x ∈ (root k : Set (Vec d)) →
        ENNReal.ofReal (vecEuclideanNorm (u.grad x)) ≤
          ENNReal.ofReal (E * G) + ENNReal.ofReal B *
            dyadicSparseSum (root k) (dyadicSparseFamily (root k) u.grad)
              (dyadicBoxEssentialInfReal (root k) b) x :=
    ae_all_iff.mpr hroot
  apply (ae_restrict_iff' (isOpen_euclideanBall _ _).measurableSet).mpr
  filter_upwards [hall] with x hxall
  intro hxs
  obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp
    (euclideanBall_subset_iUnion_calderonZygmundRetained hd hst hxs)
  have hx := hxall k hxk
  let sf : calderonZygmundRetainedIndices hd hst → ENNReal := fun j =>
    dyadicSparseSum (root j) (dyadicSparseFamily (root j) u.grad)
      (dyadicBoxEssentialInfReal (root j) b) x
  have hterm : sf k ≤ ∑' j, sf j := ENNReal.le_tsum k
  have hforest : ENNReal.ofReal B * sf k ≤
      ENNReal.ofReal B * ∑' j, sf j := by gcongr
  have hfinal := hx.trans (add_le_add le_rfl hforest)
  simpa only [sf, E, G, B, C, D, κ, root, b, mul_assoc] using hfinal

end

end PDE
