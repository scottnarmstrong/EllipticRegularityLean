module

public import PDEFoundation.Measure.AffineExtendedLpBound
public import PDEFoundation.Measure.DyadicSparseForestNorm
public import PDEFoundation.Measure.QuadraticBallMaximalReal
public import PDEFoundation.PDE.LaplacianSparseForestPointwise
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # Local Laplacian `Lᵖ` bound from the sparse forest -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory Set
open scoped _root_.ENNReal

noncomputable section

/-- The actual sparse forest gives higher integrability of the gradient on the
inner ball, together with the raw local estimate. -/
theorem memLp_grad_and_eLpNorm_le_laplacian_sparseForest
    {d : ℕ} (hd : 0 < d) {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (u : H1Function (euclideanBall (0 : Vec d) t))
    (F : Vec d → Vec d)
    (hFcoord : ∀ i, AEStronglyMeasurable (fun x => F x i) volume)
    {p : ℝ} (hp : 4 ≤ p)
    (hFp : MemLp (fun x => vecEuclideanNorm (F x))
      (ENNReal.ofReal p) volume)
    (hsol : IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat d))
      (euclideanBall (0 : Vec d) t) u 0 F) :
    MemLp (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
        (volume.restrict (euclideanBall (0 : Vec d) s)) ∧
      eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
          (volume.restrict (euclideanBall (0 : Vec d) s)) ≤
        ENNReal.ofReal
            ((((1 + 2 * (2 : ℝ) ^ (1 + (d : ℝ) / 2)) *
                Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
                  (Real.sqrt d / 2) ^ d) * Real.sqrt ((2 : ℝ) ^ d)) *
              Real.sqrt ((2 / (t - s)) ^ d)) *
              Real.sqrt ((∫ y in euclideanBall (0 : Vec d) t,
                vecNormSq (u.grad y)) /
                (volume (euclideanBall (0 : Vec d) 1)).toReal)) *
          (volume (euclideanBall (0 : Vec d) s)) ^ (1 / p) +
        ENNReal.ofReal
            (((2 : ℝ) ^ (1 + (d : ℝ) / 2) *
                Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
                  (Real.sqrt d / 2) ^ d)) *
              (((d : ℝ) + 2) / 2 *
                (1 + 2 / (d : ℝ)) ^ ((d : ℝ) / 2))) *
          (ENNReal.ofReal ((4 / 3 : ℝ) * p) *
            (ENNReal.ofReal (2 * (3 : ℝ) ^ ((d : ℝ) / 4)) *
              eLpNorm (fun x => vecEuclideanNorm (F x))
                (ENNReal.ofReal p) volume)) := by
  let ρ := calderonZygmundRetainedIndices hd hst
  let root : ρ → Box (Fin d) := fun k => calderonZygmundGridBox hd hst k.1
  let b : Vec d → ℝ := fun y => (quadraticBallMaximal F y).toReal
  let S : Vec d → ENNReal := fun x => ∑' k : ρ,
    dyadicSparseSum (root k) (dyadicSparseFamily (root k) u.grad)
      (dyadicBoxEssentialInfReal (root k) b) x
  let A := (((1 + 2 * (2 : ℝ) ^ (1 + (d : ℝ) / 2)) *
      Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
        (Real.sqrt d / 2) ^ d) * Real.sqrt ((2 : ℝ) ^ d)) *
    Real.sqrt ((2 / (t - s)) ^ d)) *
    Real.sqrt ((∫ y in euclideanBall (0 : Vec d) t, vecNormSq (u.grad y)) /
      (volume (euclideanBall (0 : Vec d) 1)).toReal)
  let B := ((2 : ℝ) ^ (1 + (d : ℝ) / 2) *
      Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
        (Real.sqrt d / 2) ^ d)) *
    (((d : ℝ) + 2) / 2 * (1 + 2 / (d : ℝ)) ^ ((d : ℝ) / 2))
  have hp2 : 2 < p := lt_of_lt_of_le (by norm_num) hp
  have ht : 0 < t := hs.trans hst
  have hrootDisjoint : Pairwise fun i j : ρ =>
      Disjoint (Box.Ioo (root i)) (Box.Ioo (root j)) := by
    simpa only [ρ, root] using pairwiseDisjoint_calderonZygmundRetained_Ioo hd hst
  let : Countable ρ := countable_of_pairwiseDisjoint_box_Ioo root hrootDisjoint
  have hgradRoot : ∀ k : ρ, ∀ i,
      MemLp (fun x => u.grad x i) 2 (volumeOn (root k : Set (Vec d))) := by
    intro k i
    have houter : euclideanBall (boxCenter (root k))
        (2 * (Real.sqrt d * calderonZygmundCubeSide d s t / 2)) ⊆
        euclideanBall (0 : Vec d) t := by
      simpa only [ρ, root] using
        euclideanBall_two_mul_circumscribedRadius_retained_subset hd hs hst k
    have hbox : (root k : Set (Vec d)) ⊆
        euclideanBall (boxCenter (root k))
          (2 * (Real.sqrt d * calderonZygmundCubeSide d s t / 2)) := by
      have hside := calderonZygmundCubeSide_pos hd hst
      have hr : 0 < Real.sqrt d * calderonZygmundCubeSide d s t / 2 := by
        have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
        positivity
      exact (Box.coe_subset_euclideanClosedBall_boxCenter (root k)
        (calderonZygmundCubeSide d s t) hd
        (by simpa only [ρ, root] using
          upper_sub_lower_calderonZygmundGridBox hd hst k.1)).trans
        (euclideanClosedBall_subset_euclideanBall hr.le (by linarith))
    exact memLpOn_mono (hbox.trans houter) (u.gradMemL2 i)
  have hb : MemLp b (ENNReal.ofReal p) volume := by
    simpa only [b] using memLp_quadraticBallMaximal_toReal F hp2 hFp
  have hSmeas : Measurable S := by
    dsimp only [S]
    exact Measurable.tsum fun k =>
      measurable_dyadicSparseSum (root k) (dyadicSparseFamily (root k) u.grad)
        (dyadicBoxEssentialInfReal (root k) b)
  have hSnorm : eLpNorm S (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((4 / 3 : ℝ) * p) *
        (ENNReal.ofReal (2 * (3 : ℝ) ^ ((d : ℝ) / 4)) *
          eLpNorm (fun x => vecEuclideanNorm (F x))
            (ENNReal.ofReal p) volume) := by
    have hsparse := eLpNorm_dyadicSparseForest_le root hrootDisjoint
      (fun _ : ρ => u.grad) hgradRoot b (by linarith) hb
    have hmax := eLpNorm_quadraticBallMaximal_le_uniform F hp hFp
    rw [eLpNorm_quadraticBallMaximal_toReal F hp2 hFp] at hsparse
    exact hsparse.trans (by gcongr)
  have hpoint := ae_vecEuclideanNorm_grad_le_laplacian_sparseForest
    hd hs hst u F hFcoord hp2 hFp hsol
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hB : 0 ≤ B := by
    have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
    have hunit : 0 < (volume (euclideanBall (0 : Vec d) 1)).toReal :=
      volume_euclideanBall_toReal_pos (0 : Vec d) (by norm_num)
    dsimp only [B]
    positivity
  have hgradMeas : AEStronglyMeasurable
      (fun x => vecEuclideanNorm (u.grad x))
      (volume.restrict (euclideanBall (0 : Vec d) s)) := by
    have hcoord (i : Fin d) : AEStronglyMeasurable (fun x => u.grad x i)
        (volume.restrict (euclideanBall (0 : Vec d) s)) :=
      (u.gradMemL2 i).aestronglyMeasurable.mono_measure
        (Measure.restrict_mono (euclideanBall_mono hs.le hst.le) le_rfl)
    have hsquare (i : Fin d) : AEStronglyMeasurable (fun x => (u.grad x i) ^ 2)
        (volume.restrict (euclideanBall (0 : Vec d) s)) := (hcoord i).pow 2
    have hsum : AEStronglyMeasurable (fun x => ∑ i : Fin d, (u.grad x i) ^ 2)
        (volume.restrict (euclideanBall (0 : Vec d) s)) :=
      by
        convert Finset.aestronglyMeasurable_sum Finset.univ
          (fun i _ => hsquare i) using 1
        ext x
        simp
    exact Real.continuous_sqrt.comp_aestronglyMeasurable (by
      simpa only [vecEuclideanNorm, vecNormSq_eq_sum_sq] using hsum)
  have haffine : eLpNorm (fun x => vecEuclideanNorm (u.grad x))
      (ENNReal.ofReal p) (volume.restrict (euclideanBall (0 : Vec d) s)) ≤
      ENNReal.ofReal A *
          ((volume.restrict (euclideanBall (0 : Vec d) s)) Set.univ) ^ (1 / p) +
        ENNReal.ofReal B * eLpNorm S (ENNReal.ofReal p)
          (volume.restrict (euclideanBall (0 : Vec d) s)) := by
    apply eLpNorm_le_of_ae_ofReal_abs_le_add_mul _ _ S hSmeas hgradMeas (by linarith) hA hB
    filter_upwards [hpoint] with x hx
    simpa only [abs_of_nonneg (vecEuclideanNorm_nonneg _), A, B, S, ρ, root, b] using hx
  have hSrestrict : eLpNorm S (ENNReal.ofReal p)
      (volume.restrict (euclideanBall (0 : Vec d) s)) ≤
      ENNReal.ofReal ((4 / 3 : ℝ) * p) *
        (ENNReal.ofReal (2 * (3 : ℝ) ^ ((d : ℝ) / 4)) *
          eLpNorm (fun x => vecEuclideanNorm (F x))
            (ENNReal.ofReal p) volume) :=
    (eLpNorm_mono_measure S Measure.restrict_le_self).trans hSnorm
  have hnorm := haffine.trans (add_le_add le_rfl (by gcongr :
    ENNReal.ofReal B * eLpNorm S (ENNReal.ofReal p)
        (volume.restrict (euclideanBall (0 : Vec d) s)) ≤
      ENNReal.ofReal B *
        (ENNReal.ofReal ((4 / 3 : ℝ) * p) *
          (ENNReal.ofReal (2 * (3 : ℝ) ^ ((d : ℝ) / 4)) *
            eLpNorm (fun x => vecEuclideanNorm (F x))
              (ENNReal.ofReal p) volume))))
  have hnorm' : eLpNorm (fun x => vecEuclideanNorm (u.grad x))
      (ENNReal.ofReal p) (volume.restrict (euclideanBall (0 : Vec d) s)) ≤
      ENNReal.ofReal A * (volume (euclideanBall (0 : Vec d) s)) ^ (1 / p) +
        ENNReal.ofReal B *
          (ENNReal.ofReal ((4 / 3 : ℝ) * p) *
            (ENNReal.ofReal (2 * (3 : ℝ) ^ ((d : ℝ) / 4)) *
              eLpNorm (fun x => vecEuclideanNorm (F x))
                (ENNReal.ofReal p) volume)) := by
    simpa only [Measure.restrict_apply_univ] using hnorm
  have hfinite :
      ENNReal.ofReal A * (volume (euclideanBall (0 : Vec d) s)) ^ (1 / p) +
        ENNReal.ofReal B *
          (ENNReal.ofReal ((4 / 3 : ℝ) * p) *
            (ENNReal.ofReal (2 * (3 : ℝ) ^ ((d : ℝ) / 4)) *
              eLpNorm (fun x => vecEuclideanNorm (F x))
                (ENNReal.ofReal p) volume)) < ⊤ := by
    apply ENNReal.add_lt_top.mpr
    constructor
    · apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      exact ENNReal.rpow_lt_top_of_nonneg (by positivity)
        (volume_euclideanBall_ne_top (0 : Vec d) hs.le)
    · apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFp.eLpNorm_lt_top
  refine ⟨(hnorm'.trans_lt hfinite), ?_⟩
  simpa only [A, B] using hnorm'

end

end PDE
