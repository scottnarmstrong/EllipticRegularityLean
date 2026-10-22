module

public import EllipticRegularity.Guerra.Field.Gradient

/-!
# Guerra sharpness: the divergence formula

For smooth `f, g` of one variable, the ambient flux
`r^{α-2} f(t) x + r^{α-1} g(t) e_j` is smooth away from the origin and
`div = r^{α-2}(β f + (α-1) t g + (1-t²) g')` with `β = α + d - 2`.
-/

@[expose] public section

open scoped BigOperators

namespace PDE.Guerra

noncomputable section

variable {d : ℕ}

/-- The ambient flux `r^{α-2} f(t) x + r^{α-1} g(t) e_j`. -/
def fluxVec (α : ℝ) (f g : ℝ → ℝ) (j : Fin d) (x : Vec d) : Vec d := fun i =>
  rad x ^ (α - 2) * f (lat j x) * x i + rad x ^ (α - 1) * g (lat j x) * basisVec j i

theorem contDiffAt_fluxVec_apply {n : ℕ} {f g : ℝ → ℝ} (hf : ContDiff ℝ n f)
    (hg : ContDiff ℝ n g) (α : ℝ) (j : Fin d) {x : Vec d} (hx : x ≠ 0) (i : Fin d) :
    ContDiffAt ℝ n (fun y : Vec d => fluxVec α f g j y i) x := by
  have hR := contDiffAt_rad (n := n) hx
  have hT := contDiffAt_lat (n := n) j hx
  unfold fluxVec
  refine ((( hR.rpow_const_of_ne (rad_pos hx).ne').mul (hf.contDiffAt.comp x hT)).mul
    (contDiff_apply ℝ ℝ i).contDiffAt).add ?_
  exact (((hR.rpow_const_of_ne (rad_pos hx).ne').mul (hg.contDiffAt.comp x hT))).mul
    contDiffAt_const

theorem contDiffOn_fluxVec_apply {n : ℕ} {f g : ℝ → ℝ} (hf : ContDiff ℝ n f)
    (hg : ContDiff ℝ n g) (α : ℝ) (j : Fin d) (i : Fin d) :
    ContDiffOn ℝ n (fun y : Vec d => fluxVec α f g j y i) ({0} : Set (Vec d))ᶜ :=
  fun _ hx => (contDiffAt_fluxVec_apply hf hg α j hx i).contDiffWithinAt

/-- Divergence of the ambient flux. -/
theorem sum_classicalGradient_fluxVec {f g : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (α : ℝ) (j : Fin d) {x : Vec d} (hx : x ≠ 0) :
    ∑ i, classicalGradient (fun y : Vec d => fluxVec α f g j y i) x i =
      rad x ^ (α - 2) * (((α + d - 2)) * f (lat j x) + (α - 1) * lat j x * g (lat j x) +
        (1 - lat j x ^ 2) * deriv g (lat j x)) := by
  have hr := rad_pos hx
  have hr0 := hr.ne'
  obtain ⟨LR, hLR, hLRv⟩ := hasFDerivAt_rad hx
  obtain ⟨LT, hLT, hLTv⟩ := hasFDerivAt_lat j hx
  have hpow1 := hLR.rpow_const (p := α - 2) (Or.inl hr0)
  have hpow2 := hLR.rpow_const (p := α - 1) (Or.inl hr0)
  have hfT := ((hf (lat j x)).hasDerivAt).comp_hasFDerivAt x hLT
  have hgT := ((hg (lat j x)).hasDerivAt).comp_hasFDerivAt x hLT
  -- exponent bookkeeping
  have e1 : rad x ^ (α - 2 - 1) = rad x ^ (α - 2) / rad x := Real.rpow_sub_one hr0 (α - 2)
  have e2 : rad x ^ (α - 1) = rad x ^ (α - 2) * rad x := by
    rw [← Real.rpow_add_one hr0]; congr 1; ring
  have e3 : rad x ^ (α - 1 - 1) = rad x ^ (α - 2) := by congr 1; ring
  have hsymm : ∀ i : Fin d, basisVec i j = basisVec j i := by
    intro i; simp only [basisVec_apply]; by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  have hself : ∀ i : Fin d, basisVec i i = 1 := by intro i; simp
  -- partial derivatives
  have hpart : ∀ i, classicalGradient (fun y : Vec d => fluxVec α f g j y i) x i =
      ((α - 2) * rad x ^ (α - 2) * f (lat j x) / rad x ^ 2 -
          rad x ^ (α - 2) * deriv f (lat j x) * x j / rad x ^ 3) * (x i * x i) +
      ((rad x ^ (α - 2) * deriv f (lat j x) / rad x +
          (α - 1) * rad x ^ (α - 2) * g (lat j x) / rad x -
          rad x ^ (α - 2) * rad x * deriv g (lat j x) * x j / rad x ^ 3) *
        (x i * basisVec j i)) + rad x ^ (α - 2) * f (lat j x) +
      rad x ^ (α - 2) * deriv g (lat j x) * (basisVec j i * basisVec j i) := by
    intro i
    have h1 := ((hpow1.mul hfT).mul (hasFDerivAt_apply (𝕜 := ℝ) i x)).add
      (((hpow2.mul hgT).mul_const (basisVec j i)))
    have h2 : HasFDerivAt (fun y : Vec d => fluxVec α f g j y i) _ x := h1
    rw [classicalGradient_apply, h2.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, hLRv, hLTv, vecDot_basisVec_right,
      Function.comp_apply, ContinuousLinearMap.proj_apply, Pi.mul_apply]
    rw [e1, e2, e3, hsymm i, hself i]
    field_simp
    ring
  have hxx : ∑ i, x i * x i = rad x ^ 2 := by rw [rad_sq, vecNormSq_eq_sum_sq]; simp [sq]
  have hxb : ∑ i, x i * basisVec j i = x j := by
    simp
  have hbb : ∑ i : Fin d, basisVec j i * basisVec j i = 1 := by
    simp
  simp only [hpart, Finset.sum_add_distrib, ← Finset.mul_sum, hxx, hxb, hbb, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [lat]
  field_simp
  ring

end

end PDE.Guerra
