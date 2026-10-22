module

public import PDEFoundation.Sobolev.Ch4.H10

/-!
# Compactly supported Lipschitz functions as `H¹` and `H¹₀` functions

A Euclidean-Lipschitz function with compact support is an `H¹(U)` function, with the a.e.
classical gradient (`classicalGradient ψ`, bounded in Euclidean length by the Lipschitz constant),
and if its support is inside `U` it lies in `H¹₀(U)`.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory Set Filter

namespace PDE.Ch4Infra

variable {d : ℕ} {U : Set (Vec d)}

/-- A compactly supported Euclidean-Lipschitz function as an `H¹(U)` function. -/
noncomputable def lipH1 (hU : IsOpen U) {L : ℝ} {ψ : Vec d → ℝ} (hψ : EucLip L ψ) (hL : 0 ≤ L)
    (hc : HasCompactSupport ψ) : H1Function U where
  toFun := ψ
  grad := classicalGradient ψ
  memL2 := ((hψ.continuous hL).memLp_of_hasCompactSupport hc).restrict U
  gradMemL2 := fun i => by
    refine MemLp.restrict U ?_
    refine memLp_two_of_bounded_of_zero_off (C := L) hc.isCompact
      (EucLip.aestronglyMeasurable_partialDeriv i) (hψ.ae_abs_partialDeriv_le hL i)
      (fun x hx => by simp [classicalGradient, fderiv_of_notMem_tsupport ℝ hx])
  hasWeakGradient := fun i => (hψ.hasWeakPartialDerivOn_univ hL i).restrict hU (subset_univ _)

@[simp] theorem lipH1_toFun (hU : IsOpen U) {L : ℝ} {ψ : Vec d → ℝ} (hψ : EucLip L ψ)
    (hL : 0 ≤ L) (hc : HasCompactSupport ψ) : (lipH1 hU hψ hL hc).toFun = ψ := rfl

@[simp] theorem lipH1_grad (hU : IsOpen U) {L : ℝ} {ψ : Vec d → ℝ} (hψ : EucLip L ψ)
    (hL : 0 ≤ L) (hc : HasCompactSupport ψ) : (lipH1 hU hψ hL hc).grad = classicalGradient ψ := rfl

/-- A compactly supported (in `U`) Euclidean-Lipschitz function as an `H¹₀(U)` function. -/
noncomputable def lipH10 (hU : IsOpen U) {L : ℝ} {ψ : Vec d → ℝ} (hψ : EucLip L ψ)
    (hL : 0 ≤ L) (hc : HasCompactSupport ψ) (hsub : tsupport ψ ⊆ U) : H10Function U :=
  toH10OfCompact hU (lipH1 hU hψ hL hc) hsub hc
    (fun _ _ hx => image_eq_zero_of_notMem_tsupport hx)

@[simp] theorem lipH10_toH1Function (hU : IsOpen U) {L : ℝ} {ψ : Vec d → ℝ} (hψ : EucLip L ψ)
    (hL : 0 ≤ L) (hc : HasCompactSupport ψ) (hsub : tsupport ψ ⊆ U) :
    (lipH10 hU hψ hL hc hsub).toH1Function = lipH1 hU hψ hL hc := rfl

end PDE.Ch4Infra
