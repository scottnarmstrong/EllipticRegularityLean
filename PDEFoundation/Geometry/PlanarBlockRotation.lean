module

public import PDEFoundation.Ambient.VecAppend
public import PDEFoundation.Geometry.EuclideanBall.Basic
public import PDEFoundation.Measure.LinearNormalizedVolume
public import Mathlib.Tactic.FinCases

/-!
# A planar quarter turn on appended native coordinates

The first two coordinates are rotated by a quarter turn while all remaining
coordinates are fixed.  This literal native equivalence preserves the explicit
Euclidean norm and every centered round ball.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set

noncomputable section

def planarQuarterTurnLinearEquiv : Vec 2 ≃ₗ[ℝ] Vec 2 where
  toFun x := ![-x 1, x 0]
  invFun x := ![x 1, -x 0]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp
  map_add' x y := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' c x := by ext i; fin_cases i <;> simp

/-- The literal planar quarter turn `(-x₁,x₀)`. -/
def planarQuarterTurn : Vec 2 ≃L[ℝ] Vec 2 :=
  planarQuarterTurnLinearEquiv.toContinuousLinearEquiv

@[simp]
theorem planarQuarterTurn_apply_zero (x : Vec 2) :
    planarQuarterTurn x 0 = -x 1 := rfl

@[simp]
theorem planarQuarterTurn_apply_one (x : Vec 2) :
    planarQuarterTurn x 1 = x 0 := rfl

@[simp]
theorem planarQuarterTurn_symm_apply_zero (x : Vec 2) :
    planarQuarterTurn.symm x 0 = x 1 := rfl

@[simp]
theorem planarQuarterTurn_symm_apply_one (x : Vec 2) :
    planarQuarterTurn.symm x 1 = -x 0 := rfl

/-- The planar quarter turn preserves the explicit Euclidean squared norm. -/
theorem vecNormSq_planarQuarterTurn (x : Vec 2) :
    vecNormSq (planarQuarterTurn x) = vecNormSq x := by
  simp [planarQuarterTurn, planarQuarterTurnLinearEquiv,
    vecNormSq, vecDot, Fin.sum_univ_two]
  ring

/-- Rotate the first two coordinates and fix the remaining coordinates. -/
def planarBlockRotation (n : ℕ) : Vec (2 + n) ≃L[ℝ] Vec (2 + n) :=
  (vecAppendEquiv 2 n).trans
    ((planarQuarterTurn.prodCongr (ContinuousLinearEquiv.refl ℝ (Vec n))).trans
      (vecAppendEquiv 2 n).symm)

@[simp]
theorem vecAppendEquiv_planarBlockRotation_fst (n : ℕ) (x : Vec (2 + n)) :
    (vecAppendEquiv 2 n (planarBlockRotation n x)).1 =
      planarQuarterTurn (vecAppendEquiv 2 n x).1 := by
  simp [planarBlockRotation]

@[simp]
theorem vecAppendEquiv_planarBlockRotation_snd (n : ℕ) (x : Vec (2 + n)) :
    (vecAppendEquiv 2 n (planarBlockRotation n x)).2 =
      (vecAppendEquiv 2 n x).2 := by
  simp [planarBlockRotation]

/-- The block quarter turn preserves the explicit Euclidean squared norm. -/
theorem vecNormSq_planarBlockRotation (n : ℕ) (x : Vec (2 + n)) :
    vecNormSq (planarBlockRotation n x) = vecNormSq x := by
  rw [vecNormSq_vecAppendEquiv 2 n (planarBlockRotation n x),
    vecNormSq_vecAppendEquiv 2 n x]
  simp only [vecAppendEquiv_planarBlockRotation_fst,
    vecAppendEquiv_planarBlockRotation_snd, vecNormSq_planarQuarterTurn]

/-- The block quarter turn preserves the explicit Euclidean norm. -/
theorem vecEuclideanNorm_planarBlockRotation (n : ℕ) (x : Vec (2 + n)) :
    vecEuclideanNorm (planarBlockRotation n x) = vecEuclideanNorm x := by
  unfold vecEuclideanNorm
  rw [vecNormSq_planarBlockRotation]

/-- The block quarter turn maps every centered native round ball onto itself. -/
theorem planarBlockRotation_image_euclideanBall (n : ℕ) {R : ℝ} (hR : 0 < R) :
    planarBlockRotation n '' euclideanBall (0 : Vec (2 + n)) R =
      euclideanBall 0 R := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR] at hy ⊢
    simpa only [map_zero, sub_zero, vecEuclideanNorm_planarBlockRotation] using hy
  · intro hx
    refine ⟨(planarBlockRotation n).symm x, ?_,
      (planarBlockRotation n).apply_symm_apply x⟩
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR] at hx ⊢
    simp only [sub_zero] at hx ⊢
    have hnorm := vecEuclideanNorm_planarBlockRotation n
      ((planarBlockRotation n).symm x)
    rw [(planarBlockRotation n).apply_symm_apply] at hnorm
    exact hnorm.symm.trans_lt hx

/-- The block quarter turn preserves normalized volume on every centered round
ball. -/
theorem measurePreserving_planarBlockRotation_normalizedVolumeOn_ball
    (n : ℕ) {R : ℝ} (hR : 0 < R) :
    MeasurePreserving (planarBlockRotation n)
      (normalizedVolumeOn (euclideanBall (0 : Vec (2 + n)) R))
      (normalizedVolumeOn (euclideanBall (0 : Vec (2 + n)) R)) := by
  have h := measurePreserving_linearEquiv_normalizedVolumeOn
    (planarBlockRotation n) (euclideanBall (0 : Vec (2 + n)) R)
  rw [planarBlockRotation_image_euclideanBall n hR] at h
  exact h

end
end PDE
