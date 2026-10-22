module

public import PDEFoundation.Analysis.LocalDivergenceIBP
public import PDEFoundation.Sobolev.WeakDivergenceRemovablePoint

@[expose] public section

namespace PDE
open MeasureTheory Set
open scoped BigOperators

/-- A classically divergence-free flux off one point has zero weak divergence
on the whole open domain when its coordinates belong to `L²` and `d≥2`. -/
theorem integral_vecDot_grad_eq_zero_of_classical_divergence_punctured
    {d : ℕ} (hd : 2 ≤ d) {U : Set (Vec d)} (hU : IsOpen U)
    (J : Vec d → Vec d)
    (hJ : ∀ i, MemLp (fun x => J x i) 2 (volume.restrict U))
    (hSmooth : ∀ i, ContDiffOn ℝ 1 (fun x => J x i) (U \ {0}))
    (hDiv : ∀ x ∈ U \ {0},
      (∑ i : Fin d, classicalGradient (fun y => J y i) x i) = 0) :
    ∀ φ : WeakTestFunction U, ∫ x in U, vecDot (J x) (φ.grad x) = 0 := by
  have hOpen : IsOpen (U \ {(0 : Vec d)}) := hU.sdiff isClosed_singleton
  apply integral_vecDot_classicalGradient_eq_zero_of_diff_singleton_zero hd hU hJ
  intro φ
  change (∫ x in U \ {0}, vecDot (J x) (φ.grad x)) = 0
  rw [integral_vecDot_weakTestFunction_grad_eq_neg_integral_divergence_mul
    hOpen J hSmooth φ]
  have hzero : (∫ x in U \ {0},
      (∑ i : Fin d, classicalGradient (fun y => J y i) x i) * φ x) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    rw [hDiv x hx, zero_mul]
  rw [hzero, neg_zero]

end PDE
