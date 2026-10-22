module

public import PDEFoundation.PDE.DGNM.Caccioppoli

/-!
# Pure real algebra for the Moser one-step estimates

The weighted Young inequality for the cross term of the test-function computation and the
resulting absorption argument.  These are elementary real-number statements; the analysis
lives in the neighbouring files.
-/

@[expose] public section

namespace PDE.DGNMOneStep

open PDE

variable {d : ℕ} {Λ : ℝ}

/-- Weighted Young bound for the cross term, with a free absorption parameter `ε > 0`. -/
theorem abs_two_mul_mul_vecDot_le_eps {η w : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix 1 Λ A) (ξ ζ : Vec d) {ε : ℝ} (hε : 0 < ε) :
    |2 * η * w * vecDot (matVecMul A ξ) ζ| ≤
      ε * (η ^ 2 * vecDot ξ (matVecMul A ξ)) + Λ / ε * (w ^ 2 * vecNormSq ζ) := by
  have h2ε : 0 ≤ 2 * ε := by linarith
  set c : ℝ := Real.sqrt (2 * ε) with hc
  have hcsq : c ^ 2 = 2 * ε := Real.sq_sqrt h2ε
  have hcpos : 0 < c := Real.sqrt_pos.mpr (by linarith)
  have key := DGNM.abs_two_mul_mul_vecDot_le_caccioppoli (η := c * η) (w := w / c) hA ξ ζ
  have e1 : 2 * (c * η) * (w / c) * vecDot (matVecMul A ξ) ζ =
      2 * η * w * vecDot (matVecMul A ξ) ζ := by
    field_simp
  have e2 : ((c * η) ^ 2 * vecDot ξ (matVecMul A ξ)) / 2 =
      ε * (η ^ 2 * vecDot ξ (matVecMul A ξ)) := by
    rw [mul_pow, hcsq]; ring
  have e3 : 2 * Λ * (w / c) ^ 2 * vecNormSq ζ = Λ / ε * (w ^ 2 * vecNormSq ζ) := by
    rw [div_pow, hcsq]
    field_simp
  rw [e1, e2, e3] at key
  exact key

/-- Absorption: from `c₁ x + c₂ y ≤ 0` and `|y| ≤ ε x + (Λ/ε) W` for the choice
`ε = c₁ / (2 |c₂|)` we get `x ≤ 4 c₂² Λ / c₁² · W`. -/
theorem absorb {c₁ c₂ x y W Λ : ℝ} (hc₁ : 0 < c₁) (hc₂ : c₂ ≠ 0)
    (htest : c₁ * x + c₂ * y ≤ 0)
    (hy : ∀ ε : ℝ, 0 < ε → |y| ≤ ε * x + Λ / ε * W) :
    x ≤ 4 * c₂ ^ 2 * Λ / c₁ ^ 2 * W := by
  have hc₂pos : 0 < |c₂| := abs_pos.mpr hc₂
  have hε : 0 < c₁ / (2 * |c₂|) := by positivity
  have h := hy _ hε
  have hle : c₁ * x ≤ |c₂| * |y| := by
    have : -(c₂ * y) ≤ |c₂ * y| := neg_le_abs _
    rw [abs_mul] at this
    linarith
  have h2 : |c₂| * |y| ≤ |c₂| * (c₁ / (2 * |c₂|) * x + Λ / (c₁ / (2 * |c₂|)) * W) :=
    mul_le_mul_of_nonneg_left h hc₂pos.le
  have h3 : |c₂| * (c₁ / (2 * |c₂|) * x + Λ / (c₁ / (2 * |c₂|)) * W) =
      c₁ / 2 * x + 2 * c₂ ^ 2 * Λ / c₁ * W := by
    have : |c₂| ^ 2 = c₂ ^ 2 := sq_abs c₂
    field_simp
    rw [this]
    ring
  have h4 : c₁ / 2 * x ≤ 2 * c₂ ^ 2 * Λ / c₁ * W := by linarith
  have h5 : x ≤ 2 * (2 * c₂ ^ 2 * Λ / c₁ * W) / c₁ := by
    rw [le_div_iff₀ hc₁]; linarith
  calc x ≤ _ := h5
    _ = 4 * c₂ ^ 2 * Λ / c₁ ^ 2 * W := by field_simp; ring

end PDE.DGNMOneStep
