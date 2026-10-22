module

public import PDEFoundation.PDE.HarmonicReplacement
public import PDEFoundation.PDE.H10GradientMean
public import PDEFoundation.Sobolev.H1.OrthogonalOscillation

/-! # Harmonic replacement preserves centered gradient energy -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Harmonic replacement has an actual zero-boundary remainder, orthogonal to
every zero-boundary gradient, and does not increase centered gradient energy. -/
theorem exists_harmonicReplacement_centered_on_euclideanBall
    (hd : 0 < d) {z : Vec d} {R : ℝ} (hR : 0 < R)
    (u : H1Function (euclideanBall z R)) :
    ∃ h : H1Function (euclideanBall z R),
      ∃ w : H10Function (euclideanBall z R),
        h.toFun = (fun x => u.toFun x - w.toH1Function.toFun x) ∧
        h.grad = (fun x => u.grad x - w.toH1Function.grad x) ∧
        (∀ v : H10Function (euclideanBall z R),
          ∫ x in euclideanBall z R, vecDot (h.grad x) (v.toH1Function.grad x) = 0) ∧
        centeredVectorMeanL2 (euclideanBall z R) h.grad ≤
          centeredVectorMeanL2 (euclideanBall z R) u.grad := by
  obtain ⟨h, w, hvalue, hgrad, horth, _⟩ :=
    exists_harmonicReplacement_on_euclideanBall hd hR u
  refine ⟨h, w, hvalue, hgrad, horth, ?_⟩
  have htop : volume (euclideanBall z R) < ∞ :=
    lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top z hR.le)
  have hsum : (fun x => h.grad x + w.toH1Function.grad x) = u.grad := by
    funext x
    rw [congrFun hgrad x]
    exact sub_add_cancel _ _
  have h := centeredVectorMeanL2_le_add_of_orthogonal_of_mean_eq_zero
    h.gradMemL2 w.toH1Function.gradMemL2 (volume_euclideanBall_pos z hR) htop
    (w.vectorIntegralAverage_grad_eq_zero htop) (horth w)
  exact h.trans_eq (congrArg (centeredVectorMeanL2 (euclideanBall z R)) hsum)

end
end PDE
