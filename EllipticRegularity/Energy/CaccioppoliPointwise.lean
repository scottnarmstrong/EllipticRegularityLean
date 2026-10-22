module

public import PDEFoundation.Ambient.CoefficientField

/-!
# Pointwise algebra for sharp Caccioppoli estimates

The cross term produced by testing a divergence-form equation with
`η² (u - k)` or `η² (u - k)₊` is controlled here with an explicit positive
Young parameter. The flux bound is the energy-adapted
`|A ξ|² ≤ Λ (ξ · A ξ)`, rather than the weaker operator estimate with `Λ²`.
The fixed absorbing estimate is recovered at parameter `1 / 2`; choosing the
parameter `sqrt (Λ / λ)` instead preserves the sharp square-root
ellipticity-ratio order in hole-filling arguments.
-/

@[expose] public section

namespace PDE

/-- Coercivity remains valid after multiplying the energy by the nonnegative
weight `η²`. -/
theorem mul_sq_vecNormSq_le_sq_mul_energy_of_isEllipticMatrix
    {d : ℕ} {lam Lam eta : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A)
    (xi : Vec d) :
    lam * eta ^ 2 * vecNormSq xi ≤ eta ^ 2 * vecDot xi (matVecMul A xi) := by
  have hweighted := mul_le_mul_of_nonneg_left (hA.coercive xi) (sq_nonneg eta)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hweighted

/-- Parameterized Young bound for the flux cross term.

The coefficient of the cutoff error is `Λ / τ`, not `Λ² / τ`. This distinction
is what permits the sharp square-root ellipticity-ratio choice
`τ = sqrt (Λ / λ)` in hole-filling estimates. -/
theorem abs_two_mul_mul_vecDot_matVecMul_le_caccioppoli_parameter
    {d : ℕ} {lam Lam eta w tau : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (htau : 0 < tau)
    (xi zeta : Vec d) :
    |2 * eta * w * vecDot (matVecMul A xi) zeta| ≤
      tau * (eta ^ 2 * vecDot xi (matVecMul A xi)) +
        (Lam / tau) * w ^ 2 * vecNormSq zeta := by
  have hflux := vecNormSq_matVecMul_le_mul_vecDot_of_isEllipticMatrix hA xi
  have hdotSq :=
    sq_vecDot_le_vecNormSq_mul_vecNormSq (matVecMul A xi) zeta
  have hfactorNonneg : 0 ≤ 4 * eta ^ 2 * w ^ 2 := by positivity
  have hweightedFlux :
      (4 * eta ^ 2 * w ^ 2) *
          (vecNormSq (matVecMul A xi) * vecNormSq zeta) ≤
        (4 * eta ^ 2 * w ^ 2) *
          ((Lam * vecDot xi (matVecMul A xi)) * vecNormSq zeta) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hflux (vecNormSq_nonneg zeta))
      hfactorNonneg
  have hsq :
      (2 * eta * w * vecDot (matVecMul A xi) zeta) ^ 2 ≤
        (2 * tau * (eta ^ 2 * vecDot xi (matVecMul A xi))) *
          ((2 * Lam / tau) * w ^ 2 * vecNormSq zeta) := by
    calc
      (2 * eta * w * vecDot (matVecMul A xi) zeta) ^ 2 =
          (4 * eta ^ 2 * w ^ 2) *
            vecDot (matVecMul A xi) zeta ^ 2 := by ring
      _ ≤ (4 * eta ^ 2 * w ^ 2) *
          (vecNormSq (matVecMul A xi) * vecNormSq zeta) :=
        mul_le_mul_of_nonneg_left hdotSq hfactorNonneg
      _ ≤ (4 * eta ^ 2 * w ^ 2) *
          ((Lam * vecDot xi (matVecMul A xi)) * vecNormSq zeta) :=
        hweightedFlux
      _ = (2 * tau * (eta ^ 2 * vecDot xi (matVecMul A xi))) *
          ((2 * Lam / tau) * w ^ 2 * vecNormSq zeta) := by
            field_simp [htau.ne']
            ring
  have henergyNonneg : 0 ≤ vecDot xi (matVecMul A xi) :=
    (mul_nonneg hA.lam_pos.le (vecNormSq_nonneg xi)).trans (hA.coercive xi)
  have hleftNonneg :
      0 ≤ 2 * tau * (eta ^ 2 * vecDot xi (matVecMul A xi)) :=
    mul_nonneg (mul_nonneg (by norm_num) htau.le)
      (mul_nonneg (sq_nonneg eta) henergyNonneg)
  have hrightNonneg :
      0 ≤ (2 * Lam / tau) * w ^ 2 * vecNormSq zeta := by
    exact mul_nonneg
      (mul_nonneg
        (div_nonneg (mul_nonneg (by norm_num) hA.Lam_pos.le) htau.le)
        (sq_nonneg w))
      (vecNormSq_nonneg zeta)
  have hyoung :=
    abs_le_add_halves_of_sq_le_mul hsq hleftNonneg hrightNonneg
  calc
    |2 * eta * w * vecDot (matVecMul A xi) zeta| ≤
        (2 * tau * (eta ^ 2 * vecDot xi (matVecMul A xi))) / 2 +
          ((2 * Lam / tau) * w ^ 2 * vecNormSq zeta) / 2 := hyoung
    _ = tau * (eta ^ 2 * vecDot xi (matVecMul A xi)) +
          (Lam / tau) * w ^ 2 * vecNormSq zeta := by ring

/-- The sharp pointwise Young bound for the Caccioppoli cross term of a
possibly nonsymmetric uniformly elliptic matrix, with the absorbing parameter
fixed to `1 / 2`. -/
theorem abs_two_mul_mul_vecDot_matVecMul_le_caccioppoli
    {d : ℕ} {lam Lam eta w : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A)
    (xi zeta : Vec d) :
    |2 * eta * w * vecDot (matVecMul A xi) zeta| ≤
      (eta ^ 2 * vecDot xi (matVecMul A xi)) / 2 +
        2 * Lam * w ^ 2 * vecNormSq zeta := by
  have hparameter :=
    abs_two_mul_mul_vecDot_matVecMul_le_caccioppoli_parameter
      hA (by norm_num : (0 : ℝ) < 1 / 2) xi zeta
      (eta := eta) (w := w) (tau := 1 / 2)
  calc
    |2 * eta * w * vecDot (matVecMul A xi) zeta| ≤
        (1 / 2) * (eta ^ 2 * vecDot xi (matVecMul A xi)) +
          (Lam / (1 / 2)) * w ^ 2 * vecNormSq zeta :=
      hparameter
    _ = (eta ^ 2 * vecDot xi (matVecMul A xi)) / 2 +
          2 * Lam * w ^ 2 * vecNormSq zeta := by ring

end PDE
