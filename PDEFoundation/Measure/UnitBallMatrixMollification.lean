module

public import PDEFoundation.Measure.MatrixPerturbationConvolution
public import PDEFoundation.Measure.UnitBallScalarMollification

/-! # Matrix coefficient mollification on the unit ball -/

@[expose] public section

namespace PDE

open Filter MeasureTheory Set
open scoped ENNReal Topology Convolution

noncomputable section

/-- Entrywise inward mollification of an identity perturbation on the unit
ball, with the identity matrix added back after smoothing. -/
def unitBallMatrixMollification {d : ℕ} (a : CoeffField d) (n : ℕ) :
    CoeffField d := fun x =>
  (1 : Mat d) + Matrix.of (fun i j =>
    unitBallScalarMollification (fun y => (a y - 1) i j) n x)

/-- Every entry of the matrix mollification is globally smooth. -/
theorem contDiff_unitBallMatrixMollification_entry
    {d : ℕ} (hd : 0 < d) {delta : ℝ} (hdelta : 0 ≤ delta)
    (a : CoeffField d)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hclose : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (n : ℕ) (i j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => unitBallMatrixMollification a n x i j) := by
  let U := euclideanBall (0 : Vec d) 1
  have hU : MeasurableSet U := (isOpen_euclideanBall _ _).measurableSet
  have hUtop : volume U ≠ ∞ := volume_euclideanBall_ne_top 0 (by norm_num)
  have hind := memLp_indicator_matrix_sub_identity_entry hU hUtop a hdelta
    ha hclose i j 2
  have hraw : MemLp (fun x => (a x - 1) i j) 2 (volumeOn U) := by
    rwa [memLp_indicator_iff_restrict hU] at hind
  have hsmooth := contDiff_unitBallScalarMollification hd (by norm_num)
    (fun x => (a x - 1) i j) hraw n
  simpa only [unitBallMatrixMollification, Matrix.add_apply, Matrix.one_apply,
    Matrix.of_apply] using contDiff_const.add hsmooth

/-- Every mollified coefficient field remains within the same exact operator
radius of the identity, at every point of the whole space. -/
theorem unitBallMatrixMollification_isMatrixPerturbationLE
    {d : ℕ} (hd : 0 < d) {delta : ℝ} (hdelta : 0 ≤ delta)
    (a : CoeffField d)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hclose : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (n : ℕ) (x : Vec d) :
    IsMatrixPerturbationLE delta (unitBallMatrixMollification a n x)
      (1 : Mat d) := by
  let U := euclideanBall (0 : Vec d) 1
  let b : CoeffField d := fun y => Matrix.of (fun i j =>
    U.indicator (fun z => (a z - 1) i j) y)
  let r : ℝ := 1 / (2 * Real.sqrt d)
  let ε : ℝ := unitConvexApproxScale (n + 1)
  have hU : MeasurableSet U := (isOpen_euclideanBall _ _).measurableSet
  have hUtop : volume U ≠ ∞ := volume_euclideanBall_ne_top 0 (by norm_num)
  have hb (i j : Fin d) : AEMeasurable (fun y => b y i j) volume := by
    have hi := memLp_indicator_matrix_sub_identity_entry hU hUtop a hdelta
      ha hclose i j 2
    simpa only [b, Matrix.of_apply] using hi.aestronglyMeasurable.aemeasurable
  have hbclose : ∀ᵐ y ∂volume,
      IsMatrixPerturbationLE delta (b y) (0 : Mat d) := by
    have hglobal := ae_matrix_identity_add_indicator_perturbation
      hU a hdelta hclose
    filter_upwards [hglobal] with y hy
    have hbeq : b y = U.indicator (fun z => a z - 1) y := by
      ext i j
      by_cases hyU : y ∈ U <;> simp [b, hyU]
    intro ξ
    simpa only [hbeq, add_sub_cancel_left, sub_zero] using hy ξ
  have hr : 0 < r := by
    dsimp only [r]
    have : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (by positivity)
    positivity
  have hε : 0 < ε := unitConvexApproxScale_pos (n + 1)
  have hconv := isMatrixPerturbationLE_identity_add_convolution
    (isConvexApproxKernel_unitConvexApproxKernel (d := d))
    (mul_pos hε hr) hdelta b hb hbclose ((1 - ε) • x)
  simpa [unitBallMatrixMollification, unitBallScalarMollification,
    convexApproxSmoothRepresentative, U, b, r, ε] using hconv

/-- Every entry of the mollified coefficient fields converges in true `L²`
on the unit ball to the corresponding original coefficient entry. -/
theorem tendsto_eLpNorm_unitBallMatrixMollification_entry_sub
    {d : ℕ} (hd : 0 < d) {delta : ℝ} (hdelta : 0 ≤ delta)
    (a : CoeffField d)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hclose : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (i j : Fin d) :
    Tendsto (fun n => eLpNorm
      (fun x => unitBallMatrixMollification a n x i j - a x i j) 2
      (volumeOn (euclideanBall (0 : Vec d) 1))) atTop (𝓝 0) := by
  let U := euclideanBall (0 : Vec d) 1
  have hU : MeasurableSet U := (isOpen_euclideanBall _ _).measurableSet
  have hUtop : volume U ≠ ∞ := volume_euclideanBall_ne_top 0 (by norm_num)
  have hind := memLp_indicator_matrix_sub_identity_entry hU hUtop a hdelta
    ha hclose i j 2
  have hraw : MemLp (fun x => (a x - 1) i j) 2 (volumeOn U) := by
    rwa [memLp_indicator_iff_restrict hU] at hind
  have hlim := tendsto_eLpNorm_unitBallScalarMollification_sub hd
    (by norm_num) (by norm_num) (fun x => (a x - 1) i j) hraw
  have hfunctions :
      (fun n => eLpNorm
        (fun x => unitBallScalarMollification (fun y => (a y - 1) i j) n x -
          (a x - 1) i j) 2 (volumeOn U)) =
      fun n => eLpNorm
        (fun x => unitBallMatrixMollification a n x i j - a x i j) 2
          (volumeOn U) := by
    funext n
    congr 1
    funext x
    simp only [unitBallMatrixMollification, Matrix.add_apply, Matrix.one_apply,
      Matrix.of_apply, Matrix.sub_apply]
    ring
  rw [← hfunctions]
  exact hlim

end

end PDE
