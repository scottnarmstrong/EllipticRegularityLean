module

public import EllipticRegularity.Ch4.Meyers.GradNorm
public import EllipticRegularity.Ch4.Meyers.TestCalculus

/-!
# The planar-type example (Proposition 4.7): the equation

`u = s^γ x_{i0}`, `v' = s^γ x_{i1}` with `s = x_{i0}² + x_{i1}²`, `a = I + (Λ-1) q qᵀ/s`,
`γ = (1/√Λ - 1)/2`.  Off the axis `a ∇u = R (√Λ ∇v')` with `R` the rotation in the
`(i0, i1)`-plane, so the equation for `u` follows from the curl pairing.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4Meyers

open MeasureTheory Set

variable {d : ℕ} {i0 i1 : Fin d}

/-- The weights of the planar example: one exactly at `i0` and `i1`. -/
noncomputable def sharpW (i0 i1 : Fin d) : Fin d → ℝ := fun j =>
  if j = i0 ∨ j = i1 then 1 else 0

theorem sharpW_01 (i0 i1 : Fin d) (j : Fin d) : sharpW i0 i1 j = 0 ∨ sharpW i0 i1 j = 1 := by
  unfold sharpW; split_ifs <;> simp

theorem sharpW_i0 (i0 i1 : Fin d) : sharpW i0 i1 i0 = 1 := by simp [sharpW]

theorem sharpW_i1 (i0 i1 : Fin d) : sharpW i0 i1 i1 = 1 := by simp [sharpW]

theorem sharpW_rest {j : Fin d} (h0 : j ≠ i0) (h1 : j ≠ i1) : sharpW i0 i1 j = 0 := by
  simp [sharpW, h0, h1]

/-- The rotation `R ξ = (ξ_{i1}, -ξ_{i0})` in the `(i0, i1)`-plane. -/
def rot (i0 i1 : Fin d) (ξ : Vec d) : Vec d := fun j =>
  if j = i0 then ξ i1 else if j = i1 then -ξ i0 else 0

theorem vecDot_rot (hi : i0 ≠ i1) (ξ η : Vec d) :
    vecDot (rot i0 i1 ξ) η = ξ i1 * η i0 - ξ i0 * η i1 := by
  unfold vecDot
  rw [Finset.sum_eq_add i0 i1 hi]
  · simp [rot, hi.symm]; ring
  · intro c _ hc; simp [rot, hc.1, hc.2]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro h; exact absurd (Finset.mem_univ _) h

theorem flux_eq_rot (hi : i0 ≠ i1) {q Λ γ : ℝ} (hq : 0 < q) (hΛ : Λ = q ^ 2)
    (hγ : γ = (1 / q - 1) / 2) {x : Vec d} (hs : 0 < axisSq (sharpW i0 i1) x) :
    matVecMul (meyersCoeff (sharpW i0 i1) Λ x) (profGrad (sharpW i0 i1) γ i0 x) =
      rot i0 i1 (fun j => q * profGrad (sharpW i0 i1) γ i1 x j) := by
  rw [meyersCoeff_matVecMul_profGrad (sharpW_01 i0 i1) hs Λ γ (sharpW_i0 i0 i1)]
  have hsq := axisSq_planar hi (sharpW_i0 i0 i1) (sharpW_i1 i0 i1)
    (fun j h0 h1 => sharpW_rest h0 h1) x
  have hr : axisSq (sharpW i0 i1) x ^ (γ - 1) =
      axisSq (sharpW i0 i1) x ^ γ / axisSq (sharpW i0 i1) x := Real.rpow_sub_one hs.ne' γ
  funext j
  simp only [profFlux, profGrad, rot, hr]
  generalize axisSq (sharpW i0 i1) x ^ γ = P at *
  generalize hsx : axisSq (sharpW i0 i1) x = s at *
  by_cases hj0 : j = i0
  · subst hj0
    simp only [sharpW_i0, sharpW_i1, ite_true, hi.symm, ite_false, mul_one, mul_zero]
    subst hΛ hγ
    subst hsq
    field_simp
    ring
  · have hne : i0 ≠ j := fun h => hj0 h.symm
    by_cases hj1 : j = i1
    · subst hj1
      simp only [hj0, hne, sharpW_i1, sharpW_i0, ite_true, ite_false, mul_one, mul_zero]
      subst hΛ hγ
      subst hsq
      field_simp
      ring
    · simp [hj0, hj1, hne, sharpW_rest hj0 hj1]

end PDE.Ch4Meyers
