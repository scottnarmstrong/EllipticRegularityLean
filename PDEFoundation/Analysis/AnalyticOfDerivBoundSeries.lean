module

public import PDEFoundation.Analysis.AnalyticOfDerivBoundTaylor
public import Mathlib.Analysis.Analytic.ConvergenceRadius

/-!
# Radius bounds for Taylor coefficients under coordinate derivative estimates
-/

@[expose] public section

namespace PDE

open scoped Nat

/-- The formal Taylor series with factorial-scaled iterated Fréchet
derivatives. -/
noncomputable def derivativePowerSeries {d : ℕ}
    (g : Vec d → ℝ) (x₀ : Vec d) : FormalMultilinearSeries ℝ (Vec d) ℝ :=
  fun n => (n ! : ℝ)⁻¹ • iteratedFDeriv ℝ n g x₀

/-- The factorial-scaled iterated derivative has geometric operator-norm
growth under coordinate bounds at one point. -/
theorem norm_factorial_smul_iteratedFDeriv_le {d n : ℕ}
    (g : Vec d → ℝ) (x₀ : Vec d) {M K : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hcoord : ∀ ι : Fin n → Fin d,
      |iteratedFDeriv ℝ n g x₀ (fun k => Pi.single (ι k) 1)| ≤
        M * (K * n) ^ n) :
    ‖(n ! : ℝ)⁻¹ • iteratedFDeriv ℝ n g x₀‖ ≤
      M * (Real.exp 1 * K * d) ^ n := by
  have hB : 0 ≤ M * (K * n) ^ n :=
    mul_nonneg hM (pow_nonneg (mul_nonneg hK (Nat.cast_nonneg n)) n)
  have hderiv := norm_iteratedFDeriv_le_of_coordinate_bound g x₀ hB hcoord
  have hfac : (0 : ℝ) < (n ! : ℝ) := by positivity
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  calc
    ‖(n ! : ℝ)⁻¹ • iteratedFDeriv ℝ n g x₀‖ =
        ((n ! : ℝ)⁻¹) * ‖iteratedFDeriv ℝ n g x₀‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hfac]
    _ ≤ ((n ! : ℝ)⁻¹) * (M * (K * n) ^ n * (d : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left hderiv (inv_nonneg.mpr hfac.le)
    _ = M * (K * n) ^ n * (d : ℝ) ^ n / (n ! : ℝ) := by ring
    _ ≤ M * (Real.exp 1 * K * d) ^ n :=
      scaled_pow_line_div_factorial_le_geometric n hM hK hd

/-- A radius on which the geometric coefficient bound is at most one lies
inside the convergence radius of the factorial-scaled derivative series. -/
theorem le_radius_factorial_iteratedFDeriv_of_coordinate_bound {d : ℕ}
    (g : Vec d → ℝ) (x₀ : Vec d) {M K : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hcoord : ∀ n : ℕ, ∀ ι : Fin n → Fin d,
      |iteratedFDeriv ℝ n g x₀ (fun k => Pi.single (ι k) 1)| ≤
        M * (K * n) ^ n)
    (r : NNReal) (hr : (Real.exp 1 * K * d) * (r : ℝ) ≤ 1) :
    (r : ENNReal) ≤ (derivativePowerSeries g x₀).radius := by
  let p := derivativePowerSeries g x₀
  change (r : ENNReal) ≤ p.radius
  apply p.le_radius_of_bound M
  intro n
  have hA : 0 ≤ Real.exp 1 * K * (d : ℝ) := by positivity
  calc
    ‖p n‖ * (r : ℝ) ^ n ≤
        M * (Real.exp 1 * K * d) ^ n * (r : ℝ) ^ n := by
      gcongr
      exact norm_factorial_smul_iteratedFDeriv_le g x₀ hM hK (hcoord n)
    _ = M * ((Real.exp 1 * K * d) * (r : ℝ)) ^ n := by rw [mul_pow]; ring
    _ ≤ M * 1 :=
      mul_le_mul_of_nonneg_left
        (pow_le_one₀ (mul_nonneg hA r.coe_nonneg) hr) hM
    _ = M := mul_one _

end PDE
