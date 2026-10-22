module

public import EllipticRegularity.Ch4.GreenDecay.MaxPrincipleFull

/-!
# Local harmonicity of the Dirichlet solution

If `v ∈ H¹₀(B_R)` solves `-div (b ∇ v) = g` with `g = 0` a.e. in `B_ρ` (`ρ ≤ R`), then the restriction of `v` to
`B_ρ` is a smooth-test solution of `-div (b ∇ w) = 0` in `B_ρ`: a smooth compactly supported test function on
`B_ρ` extends by zero to an `H¹₀(B_R)` test function which vanishes where `g ≠ 0`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4GreenDecay

open MeasureTheory PDE PDE.MeyersDuality

noncomputable section

variable {d : ℕ}

/-- The gradient of a smooth function vanishes off its topological support. -/
theorem fderiv_apply_basisVec_eq_zero_of_notMem_tsupport {φ : Vec d → ℝ} {x : Vec d}
    (hx : x ∉ tsupport φ) (i : Fin d) : fderiv ℝ φ x (basisVec i) = 0 := by
  have : x ∉ tsupport (fderiv ℝ φ) := fun h => hx (tsupport_fderiv_subset ℝ h)
  rw [image_eq_zero_of_notMem_tsupport this]
  rfl

/-- **Local harmonicity**: the restriction of a Dirichlet solution to a ball where the source vanishes. -/
theorem solution_restrict_ball {Λ R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R) {b : CoeffField d}
    (hbm : ∀ i j : Fin d,
      AEMeasurable (fun x => b x i j) (volumeOn (euclideanBall (0 : Vec d) R)))
    (hbell : ∀ x ∈ euclideanBall (0 : Vec d) R, IsEllipticMatrix 1 Λ (b x))
    {g : Vec d → ℝ} (hg0 : ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) ρ)), g x = 0)
    {v : H10Function (euclideanBall (0 : Vec d) R)}
    (hv : IsWeakDivergenceFormH10SolutionOn b (euclideanBall (0 : Vec d) R) v.toH1Function g
      (0 : Vec d → Vec d)) :
    IsWeakDivergenceFormSolutionOn b (euclideanBall (0 : Vec d) ρ)
      (v.toH1Function.restrict (isOpen_euclideanBall 0 ρ)
        (euclideanBall_mono hρ.le hρR)) (0 : Vec d → ℝ) (0 : Vec d → Vec d) := by
  have hsub : euclideanBall (0 : Vec d) ρ ⊆ euclideanBall (0 : Vec d) R :=
    euclideanBall_mono hρ.le hρR
  have hUmρ : MeasurableSet (euclideanBall (0 : Vec d) ρ) := measurableSet_euclideanBall _ _
  have hUmR : MeasurableSet (euclideanBall (0 : Vec d) R) := measurableSet_euclideanBall _ _
  set w := v.toH1Function.restrict (isOpen_euclideanBall 0 ρ) hsub with hw
  have hbmρ : ∀ i j : Fin d, AEMeasurable (fun x => b x i j) (volumeOn (euclideanBall (0 : Vec d) ρ)) :=
    fun i j => (hbm i j).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hbellρ : ∀ x ∈ euclideanBall (0 : Vec d) ρ, IsEllipticMatrix 1 Λ (b x) :=
    fun x hx => hbell x (hsub hx)
  have hflux := memVectorL2On_matVecMul_of_ae_elliptic hUmρ hbmρ hbellρ w.gradMemL2
  intro φ
  refine ⟨⟨integrableOn_vecDot_weakTestFunction_grad hflux φ, ?_, ?_⟩, ?_⟩
  · simp
  · simp [vecDot]
  · have hsupp : tsupport φ.toFun ⊆ euclideanBall (0 : Vec d) R := φ.tsupport_subset.trans hsub
    let φ' : H10Function (euclideanBall (0 : Vec d) R) :=
      H10Function.ofContDiff (isOpen_euclideanBall 0 R) φ.contDiff φ.hasCompactSupport hsupp
    have heq := (hv φ').2
    have hφ'f : φ'.toH1Function.toFun = φ.toFun := rfl
    have hφ'g : ∀ x, φ'.toH1Function.grad x = φ.grad x := fun x => rfl
    -- outside `B_ρ` the test function and its gradient vanish
    have hgrad0 : ∀ x, x ∉ euclideanBall (0 : Vec d) ρ → φ.grad x = 0 := by
      intro x hx
      funext i
      exact fderiv_apply_basisVec_eq_zero_of_notMem_tsupport
        (fun h => hx (φ.tsupport_subset h)) i
    have hfun0 : ∀ x, x ∉ euclideanBall (0 : Vec d) ρ → φ.toFun x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (φ.tsupport_subset h))
    have hgφ : (∫ x in euclideanBall (0 : Vec d) R, g x * φ'.toH1Function.toFun x) = 0 := by
      have h1 : (∫ x in euclideanBall (0 : Vec d) R, g x * φ'.toH1Function.toFun x) =
          ∫ x in euclideanBall (0 : Vec d) ρ, g x * φ'.toH1Function.toFun x := by
        refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hUmR hsub ?_
        intro x hx
        rw [hφ'f, hfun0 x hx.2, mul_zero]
      rw [h1]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hg0] with x hx
      rw [hx, zero_mul]
      rfl
    have hLHS : (∫ x in euclideanBall (0 : Vec d) R,
        vecDot (matVecMul (b x) (v.toH1Function.grad x)) (φ'.toH1Function.grad x)) =
        ∫ x in euclideanBall (0 : Vec d) ρ,
          vecDot (matVecMul (b x) (w.grad x)) (φ.grad x) := by
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hUmR hsub ?_
      intro x hx
      rw [hφ'g, hgrad0 x hx.2]
      simp
    rw [hgφ, hLHS] at heq
    simpa using heq

end

end PDE.Ch4GreenDecay
