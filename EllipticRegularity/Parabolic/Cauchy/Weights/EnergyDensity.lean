module

public import EllipticRegularity.Parabolic.Cauchy.Weights.MatrixDensity
public import EllipticRegularity.Parabolic.Cauchy.Weights.Nash

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Pointwise weighted energy inequality

Combining the nonsymmetric ellipticity algebra with the Gaussian weight
calculus gives the exact density inequality used by the Cauchy energy
argument. The vector `p` represents the spatial gradient of the exponent
`ψ = q / (4 A τ)`.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Weights

/-- The Gaussian weight density inequality, including the principal form and
the mixed flux term from the weighted energy identity. The hypothesis on `p`
is the squared-gradient bound inherited from `|∇q|² ≤ 4q`. -/
theorem nashGaussianWeight_fullEnergy_density {d : ℕ}
    {lam Lam A τ q : ℝ} {M : Mat d}
    (hΛ : 0 ≤ Lam) (hA : Lam < A) (hτ : 0 < τ)
    (hM : IsEllipticMatrix lam Lam M)
    (u : ℝ) (v p : Vec d)
    (hgrad : 16 * A ^ 2 * τ ^ 2 * vecNormSq p ≤ 4 * q) :
    2 * nashGaussianWeight A τ q ^ 2 *
      ((-q / (4 * A * τ ^ 2)) * u ^ 2 -
        vecDot v (matVecMul M v) -
          2 * u * vecDot (matVecMul M v) p) ≤
      -((1 - Lam / A) * q * nashGaussianWeight A τ q ^ 2 * u ^ 2 /
        (2 * A * τ ^ 2)) := by
  let W := nashGaussianWeight A τ q
  let G : ℝ := 16 * A ^ 2 * τ ^ 2 * vecNormSq p
  have hτpos : 0 < τ := hτ
  have hApos : 0 < A := lt_of_le_of_lt hΛ hA
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hτne : τ ≠ 0 := ne_of_gt hτpos
  have hG : G ≤ 4 * q := by simpa [G] using hgrad
  have hscalar := nashGaussianWeight_energy_density hΛ hA hτpos hG
  have hscalar' :
      W ^ 2 * (-q / (4 * A * τ ^ 2)) +
        Lam * W ^ 2 * vecNormSq p ≤
        -(1 - Lam / A) * q * W ^ 2 / (4 * A * τ ^ 2) := by
    dsimp [W] at hscalar ⊢
    have hleft :
        nashGaussianWeight A τ q *
            (-q / (4 * A * τ ^ 2) * nashGaussianWeight A τ q) +
          Lam * (nashGaussianWeight A τ q ^ 2 * G /
            (16 * A ^ 2 * τ ^ 2)) =
        nashGaussianWeight A τ q ^ 2 * (-q / (4 * A * τ ^ 2)) +
          Lam * nashGaussianWeight A τ q ^ 2 * vecNormSq p := by
      dsimp [G]
      field_simp [hAne, hτne]
    rw [hleft] at hscalar
    convert hscalar using 1
  have hcross := weightedEnergy_cross_term_bound hM u v p
  have hcrossW := mul_le_mul_of_nonneg_left hcross (sq_nonneg W)
  have hcombined :
      W ^ 2 * ((-q / (4 * A * τ ^ 2)) * u ^ 2 -
        vecDot v (matVecMul M v) -
          2 * u * vecDot (matVecMul M v) p) ≤
        (W ^ 2 * (-q / (4 * A * τ ^ 2)) +
          Lam * W ^ 2 * vecNormSq p) * u ^ 2 := by
    nlinarith [hcrossW]
  have hscalarU := mul_le_mul_of_nonneg_right hscalar' (sq_nonneg u)
  calc
    2 * W ^ 2 * ((-q / (4 * A * τ ^ 2)) * u ^ 2 -
        vecDot v (matVecMul M v) -
          2 * u * vecDot (matVecMul M v) p) ≤
        2 * ((W ^ 2 * (-q / (4 * A * τ ^ 2)) +
          Lam * W ^ 2 * vecNormSq p) * u ^ 2) := by
      nlinarith [hcombined]
    _ ≤ 2 * (-(1 - Lam / A) * q * W ^ 2 / (4 * A * τ ^ 2) * u ^ 2) :=
      mul_le_mul_of_nonneg_left hscalarU (by norm_num)
    _ = -((1 - Lam / A) * q * W ^ 2 * u ^ 2 /
          (2 * A * τ ^ 2)) := by
      field_simp [hAne, hτne]
      ring

end PDE.Parabolic.Cauchy.Weights
