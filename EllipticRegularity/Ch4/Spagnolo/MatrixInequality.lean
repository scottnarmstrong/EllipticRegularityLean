module

public import PDEFoundation.Ambient.EllipticNormalization

/-!
# The planar matrix inequality of the Piccinini--Spagnolo argument

For a symmetric `2 × 2` matrix `A` with `IsEllipticMatrix 1 Λ A` (eigenvalues in
`[1, Λ]`), a point `x` and a vector `g`, write `x⊥ · g = x₀ g₁ - x₁ g₀` for the
tangential component. Then
`(x · A g)² + Λ (x⊥ · g)² ≤ Λ |x|² (g · A g)`.

In the polar frame of the manuscript (Theorem 4.24, Step 1) this is the
combination of `p₁₁ ≤ Λ` with the inequality `1 + p₁₂² / p₁₁ ≤ p₂₂`
(4.99), the latter obtained by testing the lower ellipticity bound
with `ξ = -p₁₂ e_ρ + p₁₁ e_θ`. The Young consequence
`s (A g · x) ≤ (√Λ / 2) (s² + |x|² g · A g - (x⊥ · g)²)` is the pointwise form
of Step 3.
-/

@[expose] public section

namespace PDE.Ch4Spagnolo

/-- The tangential component `x⊥ · g = x₀ g₁ - x₁ g₀`, where `x⊥ = (-x₁, x₀)`. -/
def perpDot (x g : Vec 2) : ℝ :=
  x 0 * g 1 - x 1 * g 0

private theorem vecDot_two (x y : Vec 2) : vecDot x y = x 0 * y 0 + x 1 * y 1 := by
  simp [vecDot, Fin.sum_univ_two]

private theorem matVecMul_two_zero (A : Mat 2) (g : Vec 2) :
    matVecMul A g 0 = A 0 0 * g 0 + A 0 1 * g 1 := by
  simp [matVecMul, Fin.sum_univ_two]

private theorem matVecMul_two_one (A : Mat 2) (g : Vec 2) :
    matVecMul A g 1 = A 1 0 * g 0 + A 1 1 * g 1 := by
  simp [matVecMul, Fin.sum_univ_two]

/-- Abstract algebraic core of the planar matrix inequality, in terms of the
polar-frame quantities `P₁₁ = x·Ax`, `P₁₂ = x·Ax⊥`, `P₂₂ = x⊥·Ax⊥`, `G = g·Ag`,
`E = x·Ag`, `a' = x·g`, `b' = x⊥·g` and `N = |x|²`. -/
private theorem planar_quadratic_abstract (Λ N P11 P12 P22 G E a' b' : ℝ)
    (hNpos : 0 < N) (hP11up : P11 ≤ Λ * N)
    (hfunny : P11 * N ≤ P11 * P22 - P12 ^ 2) (hbG : b' ^ 2 ≤ N * G)
    (hI1 : N * E = a' * P11 + b' * P12)
    (hI2 : N ^ 2 * G = a' ^ 2 * P11 + 2 * a' * b' * P12 + b' ^ 2 * P22) :
    E ^ 2 + Λ * b' ^ 2 ≤ Λ * N * G := by
  have h1 : N ^ 2 * (E ^ 2 + Λ * b' ^ 2) =
      (a' * P11 + b' * P12) ^ 2 + Λ * N ^ 2 * b' ^ 2 := by
    rw [show N ^ 2 * (E ^ 2 + Λ * b' ^ 2) = (N * E) ^ 2 + Λ * N ^ 2 * b' ^ 2 by ring, hI1]
  have h2 : P11 * (N ^ 2 * G) =
      (a' * P11 + b' * P12) ^ 2 + b' ^ 2 * (P11 * P22 - P12 ^ 2) := by
    rw [hI2]; ring
  have h3 : (a' * P11 + b' * P12) ^ 2 ≤ P11 * (N ^ 2 * G) - b' ^ 2 * (P11 * N) := by
    have := mul_le_mul_of_nonneg_left hfunny (sq_nonneg b')
    linarith
  have h4 : 0 ≤ N * (Λ * N - P11) * (N * G - b' ^ 2) :=
    mul_nonneg (mul_nonneg hNpos.le (by linarith)) (by linarith)
  have h5 : P11 * (N ^ 2 * G) - b' ^ 2 * (P11 * N) + Λ * N ^ 2 * b' ^ 2 =
      N ^ 2 * (Λ * N * G) - N * (Λ * N - P11) * (N * G - b' ^ 2) := by ring
  have h6 : N ^ 2 * (E ^ 2 + Λ * b' ^ 2) ≤ N ^ 2 * (Λ * N * G) := by
    rw [h1]; linarith
  exact le_of_mul_le_mul_left h6 (by positivity)

/-- The coordinate form of the planar matrix inequality. The hypotheses are the
lower and upper quadratic bounds of the symmetric matrix `[[α, γ], [γ, δ]]`. -/
theorem planar_quadratic_core (α γ δ Λ x0 x1 g0 g1 : ℝ)
    (hcoer : ∀ ξ0 ξ1 : ℝ, ξ0 ^ 2 + ξ1 ^ 2 ≤
      α * ξ0 ^ 2 + 2 * γ * ξ0 * ξ1 + δ * ξ1 ^ 2)
    (hup : ∀ ξ0 ξ1 : ℝ, α * ξ0 ^ 2 + 2 * γ * ξ0 * ξ1 + δ * ξ1 ^ 2 ≤
      Λ * (ξ0 ^ 2 + ξ1 ^ 2)) :
    (x0 * (α * g0 + γ * g1) + x1 * (γ * g0 + δ * g1)) ^ 2 +
        Λ * (x0 * g1 - x1 * g0) ^ 2 ≤
      Λ * (x0 ^ 2 + x1 ^ 2) *
        (g0 * (α * g0 + γ * g1) + g1 * (γ * g0 + δ * g1)) := by
  rcases eq_or_lt_of_le (show 0 ≤ x0 ^ 2 + x1 ^ 2 by positivity) with hN0 | hNpos
  · have hx0 : x0 = 0 := by nlinarith [sq_nonneg x0, sq_nonneg x1]
    have hx1 : x1 = 0 := by nlinarith [sq_nonneg x0, sq_nonneg x1]
    subst hx0 hx1
    simp
  have hP11N := hcoer x0 x1
  have hP11pos : 0 < α * x0 ^ 2 + 2 * γ * x0 * x1 + δ * x1 ^ 2 :=
    lt_of_lt_of_le hNpos hP11N
  have hfunny : (α * x0 ^ 2 + 2 * γ * x0 * x1 + δ * x1 ^ 2) * (x0 ^ 2 + x1 ^ 2) ≤
      (α * x0 ^ 2 + 2 * γ * x0 * x1 + δ * x1 ^ 2) *
          (α * x1 ^ 2 - 2 * γ * x0 * x1 + δ * x0 ^ 2) -
        (-α * x0 * x1 + γ * x0 ^ 2 - γ * x1 ^ 2 + δ * x0 * x1) ^ 2 := by
    generalize hP11 : α * x0 ^ 2 + 2 * γ * x0 * x1 + δ * x1 ^ 2 = P11 at hP11pos
    generalize hP12 : -α * x0 * x1 + γ * x0 ^ 2 - γ * x1 ^ 2 + δ * x0 * x1 = P12
    generalize hP22 : α * x1 ^ 2 - 2 * γ * x0 * x1 + δ * x0 ^ 2 = P22
    have h := hcoer (-P12 * x0 - P11 * x1) (-P12 * x1 + P11 * x0)
    have hl : (-P12 * x0 - P11 * x1) ^ 2 + (-P12 * x1 + P11 * x0) ^ 2 =
        (P12 ^ 2 + P11 ^ 2) * (x0 ^ 2 + x1 ^ 2) := by ring
    have hr : α * (-P12 * x0 - P11 * x1) ^ 2 +
        2 * γ * (-P12 * x0 - P11 * x1) * (-P12 * x1 + P11 * x0) +
        δ * (-P12 * x1 + P11 * x0) ^ 2 = P11 * (P11 * P22 - P12 ^ 2) := by
      rw [← hP11, ← hP12, ← hP22]; ring
    rw [hl, hr] at h
    have hP12N : 0 ≤ P12 ^ 2 * (x0 ^ 2 + x1 ^ 2) := mul_nonneg (sq_nonneg _) hNpos.le
    have h2 : P11 * (P11 * (x0 ^ 2 + x1 ^ 2)) ≤ P11 * (P11 * P22 - P12 ^ 2) := by
      nlinarith
    exact le_of_mul_le_mul_left h2 hP11pos
  have hGg := hcoer g0 g1
  have hbG : (x0 * g1 - x1 * g0) ^ 2 ≤ (x0 ^ 2 + x1 ^ 2) *
      (g0 * (α * g0 + γ * g1) + g1 * (γ * g0 + δ * g1)) := by
    have hLag : (x0 * g1 - x1 * g0) ^ 2 ≤ (x0 ^ 2 + x1 ^ 2) * (g0 ^ 2 + g1 ^ 2) := by
      nlinarith [sq_nonneg (x0 * g0 + x1 * g1)]
    refine hLag.trans (mul_le_mul_of_nonneg_left ?_ hNpos.le)
    linarith
  exact planar_quadratic_abstract Λ (x0 ^ 2 + x1 ^ 2)
    (α * x0 ^ 2 + 2 * γ * x0 * x1 + δ * x1 ^ 2)
    (-α * x0 * x1 + γ * x0 ^ 2 - γ * x1 ^ 2 + δ * x0 * x1)
    (α * x1 ^ 2 - 2 * γ * x0 * x1 + δ * x0 ^ 2)
    (g0 * (α * g0 + γ * g1) + g1 * (γ * g0 + δ * g1))
    (x0 * (α * g0 + γ * g1) + x1 * (γ * g0 + δ * g1))
    (x0 * g0 + x1 * g1) (x0 * g1 - x1 * g0)
    hNpos (by simpa using hup x0 x1) hfunny hbG (by ring) (by ring)

/-- **Planar matrix inequality.** For a symmetric matrix with eigenvalues in
`[1, Λ]`: `(x · A g)² + Λ (x⊥ · g)² ≤ Λ |x|² (g · A g)`. -/
theorem sq_vecDot_add_perpDot_le {Λ : ℝ} {A : Mat 2} (hA : IsEllipticMatrix 1 Λ A)
    (hsymm : A 0 1 = A 1 0) (x g : Vec 2) :
    vecDot x (matVecMul A g) ^ 2 + Λ * perpDot x g ^ 2 ≤
      Λ * vecNormSq x * vecDot g (matVecMul A g) := by
  have hq : ∀ ξ : Vec 2, vecDot ξ (matVecMul A ξ) =
      A 0 0 * ξ 0 ^ 2 + 2 * A 1 0 * ξ 0 * ξ 1 + A 1 1 * ξ 1 ^ 2 := by
    intro ξ
    rw [vecDot_two, matVecMul_two_zero, matVecMul_two_one, hsymm]
    ring
  have hn : ∀ ξ : Vec 2, vecNormSq ξ = ξ 0 ^ 2 + ξ 1 ^ 2 := by
    intro ξ
    simp [vecNormSq, vecDot, Fin.sum_univ_two, pow_two]
  have hcoer : ∀ ξ0 ξ1 : ℝ, ξ0 ^ 2 + ξ1 ^ 2 ≤
      A 0 0 * ξ0 ^ 2 + 2 * A 1 0 * ξ0 * ξ1 + A 1 1 * ξ1 ^ 2 := by
    intro ξ0 ξ1
    have h := hA.coercive ![ξ0, ξ1]
    rw [one_mul, hq, hn] at h
    simpa using h
  have hup : ∀ ξ0 ξ1 : ℝ, A 0 0 * ξ0 ^ 2 + 2 * A 1 0 * ξ0 * ξ1 + A 1 1 * ξ1 ^ 2 ≤
      Λ * (ξ0 ^ 2 + ξ1 ^ 2) := by
    intro ξ0 ξ1
    have h := symmPart_quadratic_upper_of_isEllipticMatrix hA ![ξ0, ξ1]
    rw [vecDot_symmPart_matVecMul, hq, hn] at h
    simpa using h
  have hcore := planar_quadratic_core (A 0 0) (A 1 0) (A 1 1) Λ (x 0) (x 1) (g 0) (g 1)
    hcoer hup
  have hE : vecDot x (matVecMul A g) =
      x 0 * (A 0 0 * g 0 + A 1 0 * g 1) + x 1 * (A 1 0 * g 0 + A 1 1 * g 1) := by
    rw [vecDot_two, matVecMul_two_zero, matVecMul_two_one, hsymm]
  have hG : vecDot g (matVecMul A g) =
      g 0 * (A 0 0 * g 0 + A 1 0 * g 1) + g 1 * (A 1 0 * g 0 + A 1 1 * g 1) := by
    rw [vecDot_two, matVecMul_two_zero, matVecMul_two_one, hsymm]
  rw [hE, hG, hn, perpDot]
  exact hcore

/-- **Pointwise Young step.** For a symmetric matrix with eigenvalues in
`[1, Λ]` and every real `s`,
`s (A g · x) ≤ (√Λ / 2) (s² + |x|² (g · A g) - (x⊥ · g)²)`. -/
theorem mul_vecDot_le_young {Λ : ℝ} {A : Mat 2} (hA : IsEllipticMatrix 1 Λ A)
    (hsymm : A 0 1 = A 1 0) (x g : Vec 2) (s : ℝ) :
    s * vecDot (matVecMul A g) x ≤
      Real.sqrt Λ / 2 *
        (s ^ 2 + vecNormSq x * vecDot g (matVecMul A g) - perpDot x g ^ 2) := by
  have hΛpos : 0 < Λ := hA.Lam_pos
  set L : ℝ := Real.sqrt Λ with hL
  have hLpos : 0 < L := Real.sqrt_pos.2 hΛpos
  have hLsq : L ^ 2 = Λ := Real.sq_sqrt hΛpos.le
  have hmain := sq_vecDot_add_perpDot_le hA hsymm x g
  rw [vecDot_comm (matVecMul A g) x]
  generalize vecDot x (matVecMul A g) = E at hmain ⊢
  generalize hD : vecNormSq x * vecDot g (matVecMul A g) - perpDot x g ^ 2 = D
  have hE2 : E ^ 2 ≤ L ^ 2 * D := by
    rw [hLsq, ← hD]
    nlinarith [hmain]
  have hkey : 2 * L * (s * E) ≤ L ^ 2 * s ^ 2 + L ^ 2 * D := by
    nlinarith [sq_nonneg (L * s - E)]
  have h2 : L * (2 * (s * E)) ≤ L * (L * (s ^ 2 + D)) := by nlinarith [hkey]
  have h3 := le_of_mul_le_mul_left h2 hLpos
  have hrw : L / 2 * (s ^ 2 + vecNormSq x * vecDot g (matVecMul A g) - perpDot x g ^ 2) =
      L / 2 * (s ^ 2 + D) := by rw [← hD]; ring
  rw [hrw]
  linarith

end PDE.Ch4Spagnolo
