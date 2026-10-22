module

public import EllipticRegularity.Ch4.GreenFunction.Interface

/-!
# Approximate Green functions and the duality identity (Step 4 of Proposition 4.40)

`G_ρ ∈ H¹₀(B_R)` solves `-div (a ∇ G_ρ) = |B_ρ|⁻¹ 1_{B_ρ}`.  For every `H¹₀(B_R)` solution `v` of
the adjoint problem `-div (aᵗ ∇ v) = g`, testing each equation with the other solution gives
`∫ G_ρ g = ⨍_{B_ρ} v` (identity (4.154)).
-/

@[expose] public section

namespace PDE.Ch4Green

open MeasureTheory PDE

variable {d : ℕ}

/-- The normalized source `|B_ρ|⁻¹ 1_{B_ρ}` of the approximate Green function. -/
noncomputable def approxSource (d : ℕ) (ρ : ℝ) : Vec d → ℝ :=
  (euclideanBall (0 : Vec d) ρ).indicator
    (fun _ => (volume (euclideanBall (0 : Vec d) ρ)).toReal⁻¹)

theorem approxSource_nonneg (ρ : ℝ) (x : Vec d) : 0 ≤ approxSource d ρ x := by
  unfold approxSource
  exact Set.indicator_nonneg (fun _ _ => inv_nonneg.2 ENNReal.toReal_nonneg) x

theorem approxSource_eq_zero_of_notMem {ρ : ℝ} {x : Vec d}
    (hx : x ∉ euclideanBall (0 : Vec d) ρ) : approxSource d ρ x = 0 :=
  Set.indicator_of_notMem hx _

theorem memL2On_approxSource {R : ℝ} (hR : 0 ≤ R) (ρ : ℝ) :
    MemL2On (euclideanBall (0 : Vec d) R) (approxSource d ρ) := by
  unfold MemL2On MemLpOn approxSource
  refine memLp_indicator_const 2 (measurableSet_euclideanBall _ _) _ (Or.inr ?_)
  rw [Measure.restrict_apply (measurableSet_euclideanBall _ _)]
  exact ne_top_of_le_ne_top (volume_euclideanBall_ne_top _ hR) (measure_mono Set.inter_subset_right)

/-- Integrating against the normalized source gives the average over `B_ρ`. -/
theorem integral_approxSource_mul {R ρ : ℝ} (hρR : ρ ≤ R) (hρ : 0 ≤ ρ) (v : Vec d → ℝ) :
    ∫ x in euclideanBall (0 : Vec d) R, approxSource d ρ x * v x =
      integralAverage (euclideanBall (0 : Vec d) ρ) v := by
  have hsub : euclideanBall (0 : Vec d) ρ ⊆ euclideanBall (0 : Vec d) R := euclideanBall_mono hρ hρR
  have hfun : (fun x => approxSource d ρ x * v x) =
      (euclideanBall (0 : Vec d) ρ).indicator
        (fun x => (volume (euclideanBall (0 : Vec d) ρ)).toReal⁻¹ * v x) := by
    funext x
    by_cases hx : x ∈ euclideanBall (0 : Vec d) ρ
    · simp [approxSource, hx]
    · simp [approxSource, hx]
  rw [hfun, integral_indicator (measurableSet_euclideanBall _ _),
    Measure.restrict_restrict (measurableSet_euclideanBall _ _), Set.inter_eq_left.2 hsub,
    integral_const_mul, integralAverage]

/-- **Duality identity** (4.154). -/
theorem integral_mul_eq_integralAverage {a : CoeffField d} {R ρ : ℝ} (hρ : 0 ≤ ρ)
    (hρR : ρ ≤ R) {Gρ v : H10Function (euclideanBall (0 : Vec d) R)} {g : Vec d → ℝ}
    (hG : IsWeakDivergenceFormH10SolutionOn a (euclideanBall (0 : Vec d) R) Gρ.toH1Function
      (approxSource d ρ) 0)
    (hv : IsWeakDivergenceFormH10SolutionOn (adjointCoeffField a) (euclideanBall (0 : Vec d) R)
      v.toH1Function g 0) :
    ∫ x in euclideanBall (0 : Vec d) R, Gρ.toH1Function.toFun x * g x =
      integralAverage (euclideanBall (0 : Vec d) ρ) v.toH1Function.toFun := by
  obtain ⟨-, h1⟩ := hv Gρ
  obtain ⟨-, h2⟩ := hG v
  simp only [Pi.zero_apply, vecDot_zero_left, integral_zero, sub_zero] at h1 h2
  have hsym : ∀ x, vecDot (matVecMul (adjointCoeffField a x) (v.toH1Function.grad x))
      (Gρ.toH1Function.grad x) =
      vecDot (matVecMul (a x) (Gρ.toH1Function.grad x)) (v.toH1Function.grad x) := by
    intro x
    rw [adjointCoeffField_apply, vecDot_matVecMul_matTranspose, vecDot_comm]
  simp_rw [hsym] at h1
  rw [← integral_approxSource_mul hρR hρ, ← h2, h1]
  congr 1
  funext x
  ring

end PDE.Ch4Green
