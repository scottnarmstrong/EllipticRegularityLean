module

public import PDEFoundation.Measure.UnitBallMatrixMollificationAe
public import PDEFoundation.Measure.UnitBallVectorMollification
public import PDEFoundation.Measure.ForcingScale
public import PDEFoundation.PDE.AffineDirichletPerturbativeSolution
public import PDEFoundation.PDE.DirichletGradientConvergence

/-! # Smooth affine Dirichlet approximation on the unit ball -/

@[expose] public section

namespace PDE

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-- Smooth coefficient and forcing approximants yield actual affine Dirichlet
solutions along one coefficient subsequence, with strong gradient and forcing
convergence and almost-everywhere coefficient convergence. -/
theorem exists_unitBallDirichletApproximation
    {d : ℕ} (hd : 0 < d) {p delta : ℝ} (hp : 2 ≤ p)
    (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
    (a : CoeffField d)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hclose : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (u : H1Function (euclideanBall (0 : Vec d) 1))
    (F : Vec d → Vec d)
    (hFcoord : ∀ i, AEStronglyMeasurable (fun x => F x i)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hFp : MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hsol : IsWeakDivergenceFormSolutionOn a
      (euclideanBall (0 : Vec d) 1) u 0 F) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ w : ℕ → H10Function (euclideanBall (0 : Vec d) 1),
      (∀ n, IsWeakDivergenceFormSolutionOn
        (unitBallMatrixMollification a (φ n))
        (euclideanBall (0 : Vec d) 1)
        (u + (w n).toH1Function) 0
        (unitBallVectorMollification F (φ n))) ∧
      Tendsto (fun n => eLpNorm
        (fun x => vecEuclideanNorm
          ((u + (w n).toH1Function).grad x - u.grad x)) 2
        (volumeOn (euclideanBall (0 : Vec d) 1))) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm
        (fun x => vecEuclideanNorm
          (unitBallVectorMollification F (φ n) x - F x))
        (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1)))
        atTop (𝓝 0) ∧
      (∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1), ∀ i j,
        Tendsto (fun n => unitBallMatrixMollification a (φ n) x i j)
          atTop (𝓝 (a x i j))) := by
  let U := euclideanBall (0 : Vec d) 1
  let : IsFiniteMeasure (volumeOn U) :=
    isFiniteMeasure_volumeOn_euclideanBall (0 : Vec d) (by norm_num)
  obtain ⟨φ, hφ, haConv⟩ :=
    exists_strictMono_ae_tendsto_unitBallMatrixMollification
      hd hdelta a ha hclose
  obtain ⟨hFsmooth, hFSeqLp, hFConv⟩ :=
    unitBallVectorMollification_properties hd
      (show (1 : ENNReal) ≤ ENNReal.ofReal p by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (by linarith))
      ENNReal.ofReal_ne_top F hFcoord hFp
  let aSeq : ℕ → CoeffField d := fun n => unitBallMatrixMollification a (φ n)
  let FSeq : ℕ → Vec d → Vec d := fun n => unitBallVectorMollification F (φ n)
  have haSeq (n : ℕ) (i j : Fin d) :
      AEMeasurable (fun x => aSeq n x i j) (volumeOn U) :=
    (contDiff_unitBallMatrixMollification_entry hd hdelta a ha hclose (φ n) i j).continuous
      |>.measurable.aemeasurable
  have hcloseSeq (n : ℕ) : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (aSeq n x) (1 : Mat d) :=
    Eventually.of_forall
      (unitBallMatrixMollification_isMatrixPerturbationLE
        hd hdelta a ha hclose (φ n))
  have hFSeqCoord (n : ℕ) (i : Fin d) :
      AEStronglyMeasurable (fun x => FSeq n x i) (volumeOn U) :=
    (hFsmooth (φ n) i).continuous.aestronglyMeasurable
  have hFL2 : MemVectorL2On U F := by
    apply memVectorL2On_euclideanBall_of_memLp_vecEuclideanNorm hp
      (0 : Vec d) (by norm_num) (V := U) (by rfl) hFp hFcoord
  have hFSeqL2 (n : ℕ) : MemVectorL2On U (FSeq n) := by
    apply memVectorL2On_euclideanBall_of_memLp_vecEuclideanNorm hp
      (0 : Vec d) (by norm_num) (V := U) (by rfl)
      (hFSeqLp (φ n)) (hFSeqCoord n)
  have hex (n : ℕ) : ∃ wn : H10Function U,
      IsWeakDivergenceFormSolutionOn (aSeq n) U
        (u + wn.toH1Function) 0 (FSeq n) :=
    exists_add_h10_isWeakDivergenceFormSolutionOn_unitBall hd u
      (aSeq n) hdelta hdeltaOne (haSeq n) (hcloseSeq n)
      (FSeq n) (hFSeqL2 n)
  choose w hw using hex
  have hFConvP : Tendsto (fun n => eLpNorm
      (fun x => vecEuclideanNorm (FSeq n x - F x)) (ENNReal.ofReal p)
      (volumeOn U)) atTop (𝓝 0) := by
    exact hFConv.comp hφ.tendsto_atTop
  have hpENN : (2 : ENNReal) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_ofNat]
    exact ENNReal.ofReal_le_ofReal hp
  let C : ENNReal := (volumeOn U) Set.univ ^
    (1 / (2 : ENNReal).toReal - 1 / (ENNReal.ofReal p).toReal)
  have hCtop : C ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg
    · rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ p)]
      norm_num
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) hp
    · exact measure_ne_top (volumeOn U) Set.univ
  have hFConvTwo : Tendsto (fun n => eLpNorm
      (fun x => vecEuclideanNorm (FSeq n x - F x)) 2 (volumeOn U))
      atTop (𝓝 0) := by
    have hbound (n : ℕ) : eLpNorm
        (fun x => vecEuclideanNorm (FSeq n x - F x)) 2 (volumeOn U) ≤
        eLpNorm (fun x => vecEuclideanNorm (FSeq n x - F x))
          (ENNReal.ofReal p) (volumeOn U) * C := by
      apply eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpENN
      apply aestronglyMeasurable_vecEuclideanNorm_of_coord
      intro i
      exact (hFSeqCoord n i).sub (hFcoord i)
    have hupper : Tendsto (fun n => eLpNorm
        (fun x => vecEuclideanNorm (FSeq n x - F x))
          (ENNReal.ofReal p) (volumeOn U) * C) atTop (𝓝 0) := by
      simpa only [zero_mul] using
        ENNReal.Tendsto.mul_const hFConvP (Or.inr hCtop)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hupper (fun _ => bot_le) hbound
  have hgradConv := tendsto_eLpNorm_gradient_add_h10_sub_zero
    u w aSeq a FSeq F hdelta hdeltaOne haSeq ha hcloseSeq hclose
    hFSeqL2 hFL2 hw hsol (fun i j => by
      filter_upwards [haConv] with x hx
      exact hx i j) hFConvTwo
  refine ⟨φ, hφ, w, hw, hgradConv, ?_, haConv⟩
  simpa only [FSeq, U] using hFConvP

end

end PDE
