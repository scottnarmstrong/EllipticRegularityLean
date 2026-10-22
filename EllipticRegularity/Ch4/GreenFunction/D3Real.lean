module

public import PDEFoundation
public import EllipticRegularity.DeGiorgi.Assembly.HarnackReal

/-!
# Real bookkeeping for Proposition 4.42

Since `Λ ≥ 1`, every constant `K > 0` satisfies `K ≤ exp(log⁺K · Λ^{1/2})` and
`K⁻¹ ≥ exp(-log⁺K · Λ^{1/2})`, and `Λ⁻¹ ≥ exp(-2 Λ^{1/2})`.
-/

@[expose] public section

namespace PDE.Ch4Green

/-- `log⁺ K = log (max K 1) ≥ 0`. -/
noncomputable def logPlus (K : ℝ) : ℝ := Real.log (max K 1)

theorem logPlus_nonneg (K : ℝ) : 0 ≤ logPlus K :=
  Real.log_nonneg (le_max_right _ _)

theorem le_exp_logPlus_mul {K Λ : ℝ} (hK : 0 < K) (hΛ : 1 ≤ Λ) :
    K ≤ Real.exp (logPlus K * Real.sqrt Λ) := by
  have hs : 1 ≤ Real.sqrt Λ := by rw [Real.one_le_sqrt]; exact hΛ
  calc K ≤ max K 1 := le_max_left _ _
    _ = Real.exp (logPlus K) := (Real.exp_log (by positivity)).symm
    _ ≤ Real.exp (logPlus K * Real.sqrt Λ) := by
        apply Real.exp_le_exp.2
        nlinarith [logPlus_nonneg K]

theorem exp_neg_logPlus_mul_le_inv {K Λ : ℝ} (hK : 0 < K) (hΛ : 1 ≤ Λ) :
    Real.exp (-(logPlus K * Real.sqrt Λ)) ≤ K⁻¹ := by
  rw [Real.exp_neg]
  exact inv_anti₀ hK (le_exp_logPlus_mul hK hΛ)

theorem exp_neg_two_sqrt_le_inv {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    Real.exp (-(2 * Real.sqrt Λ)) ≤ Λ⁻¹ := by
  have hΛ0 : 0 < Λ := by linarith
  rw [Real.exp_neg]
  refine inv_anti₀ hΛ0 ?_
  calc Λ = Real.exp (Real.log Λ) := (Real.exp_log hΛ0).symm
    _ ≤ Real.exp (2 * Real.sqrt Λ) := Real.exp_le_exp.2 (DGNMAssembly.log_le_two_sqrt hΛ)

end PDE.Ch4Green
