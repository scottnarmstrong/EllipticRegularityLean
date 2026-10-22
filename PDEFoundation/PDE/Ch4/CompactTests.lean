module

public import PDEFoundation.PDE.Ch4.TestExtension

/-!
# Lipschitz and compactly supported `H¹` tests on bounded open sets

Corollaries of `subharmonic_test_open`, `superharmonic_test_open`, `solution_test_open`: the
weak inequality (or identity) holds for

* nonnegative compactly supported Euclidean-Lipschitz test functions `ψ`, with the a.e.
  classical gradient `classicalGradient ψ`;
* nonnegative `H¹(U)` test functions vanishing outside a compact subset of `U`.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory

namespace PDE.Ch4Infra

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {Λ : ℝ}

/-- Subharmonic functions against nonnegative compactly supported Lipschitz tests. -/
theorem subharmonic_lipTest (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsub : IsWeakDivergenceFormSubharmonicOn a U u)
    {L : ℝ} {ψ : Vec d → ℝ} (hψ : EucLip L ψ) (hL : 0 ≤ L) (hc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) (hψ0 : ∀ x, 0 ≤ ψ x) :
    IntegrableOn (fun x => vecDot (matVecMul (a x) (u.grad x)) (classicalGradient ψ x)) U ∧
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (classicalGradient ψ x) ≤ 0 :=
  subharmonic_test_open hU hfin ha hEll hsub (lipH10 hU hψ hL hc hψU)
    (H10Function.aeNonnegative_of_forall hψ0)

/-- Superharmonic functions against nonnegative compactly supported Lipschitz tests. -/
theorem superharmonic_lipTest (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u)
    {L : ℝ} {ψ : Vec d → ℝ} (hψ : EucLip L ψ) (hL : 0 ≤ L) (hc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) (hψ0 : ∀ x, 0 ≤ ψ x) :
    IntegrableOn (fun x => vecDot (matVecMul (a x) (u.grad x)) (classicalGradient ψ x)) U ∧
      0 ≤ ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (classicalGradient ψ x) :=
  superharmonic_test_open hU hfin ha hEll hsuper (lipH10 hU hψ hL hc hψU)
    (H10Function.aeNonnegative_of_forall hψ0)

/-- Solutions against compactly supported Lipschitz tests (any sign, any open set). -/
theorem solution_lipTest (hU : IsOpen U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsol : IsWeakDivergenceFormSolutionOn a U u (0 : Vec d → ℝ) 0)
    {L : ℝ} {ψ : Vec d → ℝ} (hψ : EucLip L ψ) (hL : 0 ≤ L) (hc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) :
    IntegrableOn (fun x => vecDot (matVecMul (a x) (u.grad x)) (classicalGradient ψ x)) U ∧
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (classicalGradient ψ x) = 0 :=
  solution_test_open hU ha hEll hsol (lipH10 hU hψ hL hc hψU)

/-- Subharmonic functions against nonnegative `H¹` tests vanishing outside a compact subset. -/
theorem subharmonic_compactTest (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsub : IsWeakDivergenceFormSubharmonicOn a U u)
    (φ : H1Function U) {K : Set (Vec d)} (hKU : K ⊆ U) (hK : IsCompact K)
    (hφ0 : ∀ x ∈ U, x ∉ K → φ.toFun x = 0) (hφnn : ∀ᵐ x ∂(volumeOn U), 0 ≤ φ.toFun x) :
    IntegrableOn (fun x => vecDot (matVecMul (a x) (u.grad x)) (φ.grad x)) U ∧
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.grad x) ≤ 0 :=
  subharmonic_test_open hU hfin ha hEll hsub (toH10OfCompact hU φ hKU hK hφ0) hφnn

/-- Superharmonic functions against nonnegative `H¹` tests vanishing outside a compact subset. -/
theorem superharmonic_compactTest (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u)
    (φ : H1Function U) {K : Set (Vec d)} (hKU : K ⊆ U) (hK : IsCompact K)
    (hφ0 : ∀ x ∈ U, x ∉ K → φ.toFun x = 0) (hφnn : ∀ᵐ x ∂(volumeOn U), 0 ≤ φ.toFun x) :
    IntegrableOn (fun x => vecDot (matVecMul (a x) (u.grad x)) (φ.grad x)) U ∧
      0 ≤ ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.grad x) :=
  superharmonic_test_open hU hfin ha hEll hsuper (toH10OfCompact hU φ hKU hK hφ0) hφnn

/-- Solutions against `H¹` tests vanishing outside a compact subset (any open set). -/
theorem solution_compactTest (hU : IsOpen U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsol : IsWeakDivergenceFormSolutionOn a U u (0 : Vec d → ℝ) 0)
    (φ : H1Function U) {K : Set (Vec d)} (hKU : K ⊆ U) (hK : IsCompact K)
    (hφ0 : ∀ x ∈ U, x ∉ K → φ.toFun x = 0) :
    IntegrableOn (fun x => vecDot (matVecMul (a x) (u.grad x)) (φ.grad x)) U ∧
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.grad x) = 0 :=
  solution_test_open hU ha hEll hsol (toH10OfCompact hU φ hKU hK hφ0)

end PDE.Ch4Infra
