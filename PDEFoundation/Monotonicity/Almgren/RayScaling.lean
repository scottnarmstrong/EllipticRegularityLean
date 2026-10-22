module

public import PDEFoundation.Monotonicity.Core.HarmonicFacade
public import PDEFoundation.Monotonicity.Core.TaylorPoly
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Almgren equality case: Euler ODE along rays

If `x · ∇u = α u` on `B_r` for a function differentiable there, then `u (t x) = t ^ α u x` for
`x ∈ B_r` and `t ∈ (0, 1]`.
-/

@[expose] public section

namespace PDE

noncomputable section

variable {d : ℕ}

theorem vecDot_smul_left_aux (c : ℝ) (x y : Vec d) : vecDot (c • x) y = c * vecDot x y := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Euler ODE along rays. -/
theorem scaling_of_euler_eq {r α : ℝ} {u : Vec d → ℝ}
    (hdiff : ∀ y ∈ euclideanBall (0 : Vec d) r, DifferentiableAt ℝ u y)
    (hv : ∀ y ∈ euclideanBall (0 : Vec d) r, vecDot y (classicalGradient u y) = α * u y)
    {x : Vec d} (hx : x ∈ euclideanBall (0 : Vec d) r) {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    u (t • x) = t ^ α * u x := by
  set φ : ℝ → ℝ := fun s => s ^ (-α) * u (s • x) with hφ
  have hmem : ∀ s ∈ Set.Icc (0 : ℝ) 1, s • x ∈ euclideanBall (0 : Vec d) r :=
    fun s hs => euclideanBall_smul_mem hx hs
  have hderiv : ∀ s ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt φ 0 s := by
    intro s hs
    have hsm := hmem s ⟨hs.1.le, hs.2⟩
    have h1 : HasDerivAt (fun s : ℝ => s • x) x s := by
      simpa using (hasDerivAt_id s).smul_const x
    have h2 : HasDerivAt (fun s : ℝ => u (s • x)) (fderiv ℝ u (s • x) x) s :=
      (hdiff _ hsm).hasFDerivAt.comp_hasDerivAt s h1
    have h3 : HasDerivAt (fun s : ℝ => s ^ (-α)) (-α * s ^ (-α - 1)) s :=
      Real.hasDerivAt_rpow_const (Or.inl hs.1.ne')
    have h4 := h3.mul h2
    have hgrad : fderiv ℝ u (s • x) x = vecDot (classicalGradient u (s • x)) x :=
      fderiv_apply_eq_vecDot_classicalGradient u (s • x) x
    have heul := hv (s • x) hsm
    rw [vecDot_smul_left_aux, vecDot_comm] at heul
    rw [hgrad] at h4
    convert h4 using 1
    have hs0 : s ≠ 0 := hs.1.ne'
    have hpow : s ^ (-α - 1) = s ^ (-α) * s⁻¹ := by
      rw [Real.rpow_sub hs.1, Real.rpow_one, div_eq_mul_inv]
    have hg : vecDot (classicalGradient u (s • x)) x = α * u (s • x) / s := by
      field_simp
      linarith
    rw [hg, hpow]
    field_simp
    ring
  have hconst := constant_of_has_deriv_right_zero (f := φ) (a := t) (b := 1)
    (fun s hs => (hderiv s ⟨ht.1.trans_le hs.1, hs.2⟩).continuousAt.continuousWithinAt)
    (fun s hs => (hderiv s ⟨ht.1.trans_le hs.1, hs.2.le⟩).hasDerivWithinAt) 1
    ⟨ht.2, le_refl _⟩
  simp only [hφ, Real.one_rpow, one_mul, one_smul] at hconst
  have hpos : 0 < t := ht.1
  have : t ^ α * (t ^ (-α) * u (t • x)) = t ^ α * u x := by rw [← hconst]
  rw [← mul_assoc, ← Real.rpow_add hpos] at this
  simpa using this

end

end PDE
