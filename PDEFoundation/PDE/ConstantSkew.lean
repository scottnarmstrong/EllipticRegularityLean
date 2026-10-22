module

public import PDEFoundation.PDE.WeakDivergenceForm
public import PDEFoundation.Sobolev.ClassicalLaplacian

/-!
# Constant skew matrices in scalar divergence equations

A constant skew matrix pairs to zero against the Hessian of a smooth test.
This gives exact invariance of the scalar weak operator under its removal.
The proof is extracted from the compatible Superdiffusion development.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- A skew matrix pairs to zero against a symmetric array. -/
private theorem sum_sum_mul_eq_zero_of_skew_of_symm {C : Mat d}
    (hC : ∀ i j : Fin d, C j i = -C i j) {T : Fin d → Fin d → ℝ}
    (hT : ∀ i j : Fin d, T i j = T j i) :
    ∑ i : Fin d, ∑ j : Fin d, C i j * T i j = 0 := by
  have hpoint : ∀ i j : Fin d, C j i * T j i = -(C i j * T i j) := by
    intro i j
    rw [hC i j, ← hT i j]
    ring
  have hswap : ∑ i : Fin d, ∑ j : Fin d, C i j * T i j =
      ∑ i : Fin d, ∑ j : Fin d, C j i * T j i := Finset.sum_comm
  have hneg : ∑ i : Fin d, ∑ j : Fin d, C j i * T j i =
      -∑ i : Fin d, ∑ j : Fin d, C i j * T i j := by
    rw [show (∑ i : Fin d, ∑ j : Fin d, C j i * T j i) =
        ∑ i : Fin d, ∑ j : Fin d, -(C i j * T i j) from
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpoint i j]
    simp only [Finset.sum_neg_distrib]
  have h2 := hswap.trans hneg
  linarith only [h2]

/-- The `(i, j)` entry of the pairing array `∫_U ∂_j u · ∂_i ψ`, evaluated by
one integration by parts against the smooth test function `∂_i ψ`. -/
private theorem integral_grad_mul_coordDeriv_eq {U : Set (Vec d)} (u : H1Function U)
    {psi : Vec d → ℝ} (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi)
    (hpsic : HasCompactSupport psi) (hpsiU : tsupport psi ⊆ U) (i j : Fin d) :
    ∫ x in U, u.grad x j * euclideanCoordDeriv i psi x ∂volume =
      -∫ x in U, u.toFun x * euclideanCoordSecondDeriv i j psi x ∂volume := by
  have hweak := u.hasWeakGradient j (euclideanCoordDeriv i psi)
    (contDiff_euclideanCoordDeriv hpsi i)
    (hasCompactSupport_euclideanCoordDeriv hpsic i)
    ((tsupport_euclideanCoordDeriv_subset_tsupport i psi).trans hpsiU)
  have hsecond : ∀ x : Vec d,
      u.toFun x * (fderiv ℝ (euclideanCoordDeriv i psi) x) (basisVec j) =
        u.toFun x * euclideanCoordSecondDeriv i j psi x := fun _ => rfl
  rw [show (∫ x in U, u.toFun x *
        (fderiv ℝ (euclideanCoordDeriv i psi) x) (basisVec j) ∂volume) =
      ∫ x in U, u.toFun x * euclideanCoordSecondDeriv i j psi x ∂volume from
    congrArg _ (funext hsecond)] at hweak
  rw [hweak]
  ring

/-- **The pairing array is symmetric.**  This is the whole analytic content of
the antisymmetric shift: the second derivative of a smooth test function is
symmetric, and one integration by parts moves both derivatives onto it. -/
private theorem integral_grad_mul_coordDeriv_comm {U : Set (Vec d)} (u : H1Function U)
    {psi : Vec d → ℝ} (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi)
    (hpsic : HasCompactSupport psi) (hpsiU : tsupport psi ⊆ U) (i j : Fin d) :
    ∫ x in U, u.grad x j * euclideanCoordDeriv i psi x ∂volume =
      ∫ x in U, u.grad x i * euclideanCoordDeriv j psi x ∂volume := by
  rw [integral_grad_mul_coordDeriv_eq u hpsi hpsic hpsiU i j,
    integral_grad_mul_coordDeriv_eq u hpsi hpsic hpsiU j i,
    euclideanCoordSecondDeriv_comm_fun hpsi i j]

/-! ## 3. The skew pairing, first at smooth tests -/

/-- Expansion of the skew pairing into the array. -/
private theorem vecDot_matVecMul_expand (C : Mat d) (v w : Vec d) :
    vecDot (matVecMul C v) w = ∑ i : Fin d, ∑ j : Fin d, C i j * (v j * w i) := by
  simp only [vecDot, matVecMul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by ring

/-- `L²` control of the coordinates of `C ∇u` on `U`, for a constant matrix. -/
private theorem memL2On_matVecMul_const {U : Set (Vec d)} (C : Mat d)
    (u : H1Function U) (i : Fin d) :
    MemL2On U (fun x => matVecMul C (u.grad x) i) := by
  have hEq : (fun x : Vec d => matVecMul C (u.grad x) i) =
      fun x : Vec d => ∑ j : Fin d, C i j * u.grad x j := rfl
  rw [hEq]
  exact memLp_finsetSum Finset.univ
    fun j _ => (u.gradMemL2 j).const_mul (C i j)

/-- The skew pairing against a smooth compactly supported test vanishes. -/
theorem integral_vecDot_matVecMul_skew_smooth {U : Set (Vec d)} {C : Mat d}
    (hC : matTranspose C = -C) (u : H1Function U) {psi : Vec d → ℝ}
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) (hpsic : HasCompactSupport psi)
    (hpsiU : tsupport psi ⊆ U) :
    ∫ x in U, vecDot (matVecMul C (u.grad x)) (classicalGradient psi x) ∂volume = 0 := by
  have hCentry : ∀ i j : Fin d, C j i = -C i j := by
    intro i j
    simpa only [Matrix.transpose_apply, Matrix.neg_apply]
      using! congrFun (congrFun hC i) j
  have hpsiL2 : ∀ i : Fin d, MemL2On U (euclideanCoordDeriv i psi) := by
    intro i
    have hcont : Continuous (euclideanCoordDeriv i psi) :=
      (contDiff_euclideanCoordDeriv hpsi i).continuous
    have hsupp : HasCompactSupport (euclideanCoordDeriv i psi) :=
      hasCompactSupport_euclideanCoordDeriv hpsic i
    simpa only [MemL2On, volumeOn] using
      (hcont.memLp_of_hasCompactSupport (p := (2 : ℝ≥0∞)) hsupp).restrict U
  have hint : ∀ i j : Fin d,
      Integrable (fun x : Vec d => C i j * (u.grad x j * euclideanCoordDeriv i psi x))
        (volume.restrict U) := by
    intro i j
    have hmul : Integrable
        (fun x : Vec d => u.grad x j * euclideanCoordDeriv i psi x)
        (volume.restrict U) := by
      simpa only [Pi.mul_apply] using! (u.gradMemL2 j).integrable_mul (hpsiL2 i)
    exact hmul.const_mul (C i j)
  have hstep : ∫ x in U, vecDot (matVecMul C (u.grad x)) (classicalGradient psi x) ∂volume =
      ∑ i : Fin d, ∑ j : Fin d,
        C i j * ∫ x in U, u.grad x j * euclideanCoordDeriv i psi x ∂volume := by
    have hpt : ∀ x : Vec d,
        vecDot (matVecMul C (u.grad x)) (classicalGradient psi x) =
          ∑ i : Fin d, ∑ j : Fin d,
            C i j * (u.grad x j * euclideanCoordDeriv i psi x) := by
      intro x
      simpa only [classicalGradient] using!
        vecDot_matVecMul_expand C (u.grad x) (classicalGradient psi x)
    rw [show (fun x : Vec d =>
          vecDot (matVecMul C (u.grad x)) (classicalGradient psi x)) =
        fun x : Vec d => ∑ i : Fin d, ∑ j : Fin d,
          C i j * (u.grad x j * euclideanCoordDeriv i psi x) from funext hpt]
    rw [integral_finsetSum Finset.univ
      fun i _ => integrable_finsetSum Finset.univ fun j _ => hint i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum Finset.univ fun j _ => hint i j]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul (C i j) _
  rw [hstep]
  exact sum_sum_mul_eq_zero_of_skew_of_symm hCentry
    fun i j => integral_grad_mul_coordDeriv_comm u hpsi hpsic hpsiU i j

/-- Removing a constant skew part preserves the actual smooth-test weak
equation, including all its integrability requirements. -/
theorem IsWeakDivergenceFormSolutionOn.sub_const_skew
    {U : Set (Vec d)} {a : CoeffField d} {C : Mat d}
    {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hu : IsWeakDivergenceFormSolutionOn a U u f F)
    (hC : matTranspose C = -C) :
    IsWeakDivergenceFormSolutionOn (fun x => a x - C) U u f F := by
  intro φ
  have htest := hu φ
  have hCint : IntegrableOn
      (fun x => vecDot (matVecMul C (u.grad x)) (φ.grad x)) U :=
    integrableOn_vecDot_weakTestFunction_grad
      (fun i => memL2On_matVecMul_const C u i) φ
  have hCzero : ∫ x in U, vecDot (matVecMul C (u.grad x)) (φ.grad x) = 0 :=
    integral_vecDot_matVecMul_skew_smooth hC u φ.contDiff φ.hasCompactSupport
      φ.tsupport_subset
  have hpoint : (fun x => vecDot (matVecMul (a x - C) (u.grad x)) (φ.grad x)) =
      fun x => vecDot (matVecMul (a x) (u.grad x)) (φ.grad x) -
        vecDot (matVecMul C (u.grad x)) (φ.grad x) := by
    funext x
    change vecDot ((a x - C).mulVec (u.grad x)) (φ.grad x) = _
    rw [Matrix.sub_mulVec]
    simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    rfl
  refine ⟨⟨?_, htest.1.source_integrable, htest.1.forcing_integrable⟩, ?_⟩
  · rw [hpoint]
    exact htest.1.flux_integrable.sub hCint
  · rw [hpoint, integral_sub htest.1.flux_integrable hCint, hCzero, sub_zero]
    exact htest.2

end

end PDE
