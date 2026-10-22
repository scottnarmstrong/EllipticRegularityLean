module

public import PDEFoundation.Sobolev.ClassicalGradient
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Native coordinate Laplacian calculus

Coordinate derivatives and their mixed-derivative identities are extracted
from the compatible LeanIntoHomogenization foundation. The coordinate gradient
is exactly the existing `classicalGradient`.
-/

@[expose] public section

namespace PDE

noncomputable section

def euclideanCoordDeriv {d : ℕ} (i : Fin d) (u : Vec d → ℝ) : Vec d → ℝ :=
  fun x => fderiv ℝ u x (basisVec i)

theorem support_euclideanCoordDeriv_subset_tsupport {d : ℕ}
    (i : Fin d) (u : Vec d → ℝ) :
    Function.support (euclideanCoordDeriv i u) ⊆ tsupport u := by
  intro x hx
  exact
    (support_fderiv_subset (𝕜 := ℝ) (f := u)) <| by
      change fderiv ℝ u x ≠ 0
      intro hzero
      apply hx
      simp [euclideanCoordDeriv, hzero]

theorem tsupport_euclideanCoordDeriv_subset_tsupport {d : ℕ}
    (i : Fin d) (u : Vec d → ℝ) :
    tsupport (euclideanCoordDeriv i u) ⊆ tsupport u :=
  closure_minimal
    (support_euclideanCoordDeriv_subset_tsupport i u) isClosed_closure

theorem euclideanCoordDeriv_sq {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (i : Fin d) (x : Vec d) :
    euclideanCoordDeriv i (fun y => u y ^ 2) x =
      2 * u x * euclideanCoordDeriv i u x := by
  unfold euclideanCoordDeriv
  have hd : DifferentiableAt ℝ u x := (hu.differentiable (by simp)) x
  have hpow :=
    congrArg (fun L : Vec d →L[ℝ] ℝ => L (basisVec i))
      (fderiv_pow (𝕜 := ℝ) (f := u) (x := x) 2 hd)
  simpa [pow_one, two_nsmul, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
    using! hpow

def euclideanCoordSecondDeriv {d : ℕ} (i j : Fin d) (u : Vec d → ℝ) : Vec d → ℝ :=
  fun x => fderiv ℝ (euclideanCoordDeriv i u) x (basisVec j)

def euclideanCoordThirdDeriv {d : ℕ} (i j k : Fin d) (u : Vec d → ℝ) :
    Vec d → ℝ :=
  fun x => fderiv ℝ (euclideanCoordSecondDeriv i j u) x (basisVec k)

def euclideanCoordLaplacian {d : ℕ} (u : Vec d → ℝ) : Vec d → ℝ :=
  fun x => ∑ i : Fin d, euclideanCoordSecondDeriv i i u x

theorem contDiff_euclideanCoordDeriv {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanCoordDeriv i u) := by
  unfold euclideanCoordDeriv
  exact (hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem hasCompactSupport_euclideanCoordDeriv {d : ℕ} {u : Vec d → ℝ}
    (hu : HasCompactSupport u) (i : Fin d) :
    HasCompactSupport (euclideanCoordDeriv i u) := by
  unfold euclideanCoordDeriv
  exact hu.fderiv_apply (𝕜 := ℝ) (basisVec i)

theorem contDiff_euclideanCoordSecondDeriv {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (i j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanCoordSecondDeriv i j u) := by
  unfold euclideanCoordSecondDeriv
  exact contDiff_euclideanCoordDeriv (contDiff_euclideanCoordDeriv hu i) j

theorem hasCompactSupport_euclideanCoordSecondDeriv {d : ℕ} {u : Vec d → ℝ}
    (hu : HasCompactSupport u) (i j : Fin d) :
    HasCompactSupport (euclideanCoordSecondDeriv i j u) := by
  unfold euclideanCoordSecondDeriv
  exact hasCompactSupport_euclideanCoordDeriv
    (hasCompactSupport_euclideanCoordDeriv hu i) j

theorem euclideanCoordSecondDeriv_eq_fderiv_fderiv {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (i j : Fin d) (x : Vec d) :
    euclideanCoordSecondDeriv i j u x =
      fderiv ℝ (fderiv ℝ u) x (basisVec j) (basisVec i) := by
  unfold euclideanCoordSecondDeriv euclideanCoordDeriv
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) x := by
    exact
      ((hu.fderiv_right (m := 1)
        (by
          exact WithTop.coe_le_coe.2
            (show ((1 : ℕ∞) + 1) ≤ ⊤ from le_top))).differentiable
        (by norm_num)) x
  rw [fderiv_clm_apply]
  · simp
  · exact hfd
  · exact differentiableAt_const _

theorem euclideanCoordSecondDeriv_comm {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (i j : Fin d) (x : Vec d) :
    euclideanCoordSecondDeriv i j u x =
      euclideanCoordSecondDeriv j i u x := by
  rw [euclideanCoordSecondDeriv_eq_fderiv_fderiv hu i j x,
    euclideanCoordSecondDeriv_eq_fderiv_fderiv hu j i x]
  exact (ContDiffAt.isSymmSndFDerivAt (hu.contDiffAt)
    (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 (show (2 : ℕ∞) ≤ ⊤ from le_top))).eq
        (basisVec j) (basisVec i)

theorem euclideanCoordSecondDeriv_comm_fun {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (i j : Fin d) :
    euclideanCoordSecondDeriv i j u = euclideanCoordSecondDeriv j i u := by
  funext x
  exact euclideanCoordSecondDeriv_comm hu i j x

theorem euclideanCoordThirdDeriv_diag_right_comm {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (i j : Fin d) (x : Vec d) :
    euclideanCoordThirdDeriv i j j u x =
      euclideanCoordThirdDeriv j j i u x := by
  unfold euclideanCoordThirdDeriv
  have hcomm : euclideanCoordSecondDeriv i j u = euclideanCoordSecondDeriv j i u :=
    euclideanCoordSecondDeriv_comm_fun hu i j
  rw [hcomm]
  change euclideanCoordSecondDeriv i j (euclideanCoordDeriv j u) x =
    euclideanCoordSecondDeriv j i (euclideanCoordDeriv j u) x
  exact euclideanCoordSecondDeriv_comm (contDiff_euclideanCoordDeriv hu j) i j x
/-- The inherited coordinate derivative convention agrees exactly with the
existing native classical gradient. -/
theorem euclideanCoordDeriv_eq_classicalGradient_apply {d : ℕ}
    (i : Fin d) (u : Vec d → ℝ) (x : Vec d) :
    euclideanCoordDeriv i u x = classicalGradient u x i := rfl

end

end PDE
