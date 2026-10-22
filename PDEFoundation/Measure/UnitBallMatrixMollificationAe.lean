module

public import PDEFoundation.Measure.FiniteCoordinateAeSubsequence
public import PDEFoundation.Measure.UnitBallMatrixMollification

/-! # Almost-everywhere subsequences of coefficient mollifiers -/

@[expose] public section

namespace PDE

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-- On a finite-volume domain, uniform identity closeness gives actual
coordinate membership in every extended `Lᵖ` space. -/
theorem memLp_matrix_entry_of_isMatrixPerturbationLE
    {d : ℕ} {U : Set (Vec d)} [IsFiniteMeasure (volumeOn U)]
    (a : CoeffField d) {delta : ℝ}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (i j : Fin d) (p : ENNReal) :
    MemLp (fun x => a x i j) p (volumeOn U) := by
  classical
  apply MemLp.of_bound (ha i j).aestronglyMeasurable (delta + 1)
  filter_upwards [hclose] with x hx
  have hId : |(1 : Mat d) i j| ≤ (1 : ℝ) := by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hentry := hx.abs_entry_sub_le i j
  change |a x i j| ≤ delta + 1
  calc
    |a x i j| = |(a x i j - (1 : Mat d) i j) + (1 : Mat d) i j| := by
      rw [sub_add_cancel]
    _ ≤ |a x i j - (1 : Mat d) i j| + |(1 : Mat d) i j| := abs_add_le _ _
    _ ≤ delta + 1 := add_le_add hentry hId

/-- One common subsequence of the literal smooth coefficient approximants
converges almost everywhere in every matrix entry. -/
theorem exists_strictMono_ae_tendsto_unitBallMatrixMollification
    {d : ℕ} (hd : 0 < d) {delta : ℝ} (hdelta : 0 ≤ delta)
    (a : CoeffField d)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hclose : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
      IsMatrixPerturbationLE delta (a x) (1 : Mat d)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1), ∀ i j,
        Tendsto (fun n => unitBallMatrixMollification a (φ n) x i j)
          atTop (𝓝 (a x i j)) := by
  let U := euclideanBall (0 : Vec d) 1
  let : IsFiniteMeasure (volumeOn U) := isFiniteMeasure_restrict.mpr
    (volume_euclideanBall_ne_top 0 (by norm_num))
  have haSeq (n : ℕ) (i j : Fin d) :
      AEMeasurable (fun x => unitBallMatrixMollification a n x i j)
        (volumeOn U) :=
    (contDiff_unitBallMatrixMollification_entry hd hdelta a ha hclose n i j).continuous
      |>.measurable.aemeasurable
  have hcloseSeq (n : ℕ) : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (unitBallMatrixMollification a n x) (1 : Mat d) :=
    Eventually.of_forall (unitBallMatrixMollification_isMatrixPerturbationLE
      hd hdelta a ha hclose n)
  obtain ⟨φ, hφ, hconv⟩ :=
    exists_strictMono_ae_tendsto_all_coordinates_of_eLpNorm_two
      (gSeq := fun n x (ij : Fin d × Fin d) =>
        unitBallMatrixMollification a n x ij.1 ij.2)
      (g := fun x (ij : Fin d × Fin d) => a x ij.1 ij.2)
      (fun n ij => memLp_matrix_entry_of_isMatrixPerturbationLE
        (unitBallMatrixMollification a n) (haSeq n) (hcloseSeq n) ij.1 ij.2 2)
      (fun ij => memLp_matrix_entry_of_isMatrixPerturbationLE a ha hclose ij.1 ij.2 2)
      (fun ij => tendsto_eLpNorm_unitBallMatrixMollification_entry_sub
        hd hdelta a ha hclose ij.1 ij.2)
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hconv] with x hx
  exact fun i j => hx (i, j)

end

end PDE
