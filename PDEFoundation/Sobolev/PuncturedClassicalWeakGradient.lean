module

public import PDEFoundation.Sobolev.ClassicalOnOpenWeakGradient
public import PDEFoundation.Sobolev.WeakGradientRemovablePoint

@[expose] public section

namespace PDE
open MeasureTheory Set

/-- A specified L2 gradient agreeing with the classical gradient away from
one point is the weak gradient on the full domain in dimension at least two. -/
theorem hasWeakGradientOn_of_punctured_classicalGradient
    {d : ℕ} (hd : 2 ≤ d) {U : Set (Vec d)} (hU : IsOpen U)
    {f : Vec d → ℝ} {G : Vec d → Vec d}
    (hf : MemLp f 2 (volume.restrict U))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict U))
    (hSmooth : ContDiffOn ℝ 1 f (U \ {0}))
    (hGrad : ∀ x ∈ U \ {0}, classicalGradient f x = G x) :
    HasWeakGradientOn U f G := by
  have hOpen : IsOpen (U \ {(0 : Vec d)}) := hU.sdiff isClosed_singleton
  have hClassical := HasWeakGradientOn.of_contDiffOn hOpen hSmooth
  apply hasWeakGradientOn_of_diff_singleton_zero hd hU hf hG
  intro i
  apply hasWeakPartialDerivOn_iff_forall_testFunction.mpr
  intro φ
  have h := hasWeakPartialDerivOn_iff_forall_testFunction.mp (hClassical i) φ
  have hEq : (∫ x in U \ {0}, classicalGradient f x i * φ x) =
      ∫ x in U \ {0}, G x i * φ x := by
    apply setIntegral_congr_fun hOpen.measurableSet
    intro x hx
    dsimp only
    rw [hGrad x hx]
  rw [hEq] at h
  exact h

end PDE
