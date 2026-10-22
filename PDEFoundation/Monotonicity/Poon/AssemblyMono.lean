module

public import PDEFoundation.Monotonicity.Poon.AssemblyDeriv

/-!
# Monotonicity of Poon's frequency on the admissible interval

`H` is nondecreasing on the admissible interval (`H' = 2D ≥ 0`); if `H(a) = 0` then `N(a) = 0 ≤ N(b)`;
otherwise `H > 0` on `[a, b]`, where `N' ≥ 0`.
-/

@[expose] public section

open Set

namespace PDE

noncomputable section

variable {d : ℕ} {u : ℝ → Vec d → ℝ} {T : ℝ}

theorem admissible_of_mem_Icc {A a b r : ℝ} (ha : 0 < a) (hbT : b < T) (hAb : 8 * A * b < 1)
    (hr : r ∈ Icc a b) : 0 < r ∧ r < T ∧ 8 * A * r < 1 := by
  obtain ⟨har, hrb⟩ := hr
  refine ⟨by linarith, by linarith, ?_⟩
  rcases le_total 0 A with hA | hA
  · have : 8 * A * r ≤ 8 * A * b := mul_le_mul_of_nonneg_left hrb (by linarith)
    linarith
  · have : 8 * A * r ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith

/-- Monotonicity of `poonFrequency` on the admissible interval. -/
theorem poonFrequency_monotoneOn
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (jointOf u) (Ioo (-T) 0 ×ˢ (univ : Set (Vec d))))
    (heat : ∀ t ∈ Ioo (-T) 0, ∀ x : Vec d,
      HasDerivAt (fun τ : ℝ => u τ x) (euclideanCoordLaplacian (u t) x) t)
    {A C : ℝ}
    (hbound : ∀ t ∈ Ioo (-T) 0, ∀ x : Vec d, |u t x| ≤ C * Real.exp (A * vecNormSq x)) :
    MonotoneOn (poonFrequency u) {s : ℝ | 0 < s ∧ s < T ∧ 8 * A * s < 1} := by
  intro a ha b hb hab
  obtain ⟨ha0, haT, haA⟩ := ha
  obtain ⟨hb0, hbT, hbA⟩ := hb
  rcases hab.eq_or_lt with rfl | hlt
  · exact le_rfl
  have hadm : ∀ r ∈ Icc a b, 0 < r ∧ r < T ∧ 8 * A * r < 1 := fun r hr =>
    admissible_of_mem_Icc ha0 hbT hbA hr
  -- `H` is monotone on `[a, b]`
  have hHmono : MonotoneOn (poonH u) (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
    · intro r hr
      obtain ⟨h0, h1, h2⟩ := hadm r hr
      exact (poonH_hasDerivAt_two_mul hsmooth heat hbound h0 h1 h2).continuousAt.continuousWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      obtain ⟨h0, h1, h2⟩ := hadm r (Ioo_subset_Icc_self hr)
      exact (poonH_hasDerivAt_two_mul hsmooth heat hbound h0 h1 h2).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      obtain ⟨h0, h1, h2⟩ := hadm r (Ioo_subset_Icc_self hr)
      rw [(poonH_hasDerivAt_two_mul hsmooth heat hbound h0 h1 h2).deriv]
      linarith [poonD_nonneg (u := u) h0]
  rcases (poonH_nonneg (u := u) ha0).eq_or_lt with hH0 | hHpos
  · -- junk case: `H(a) = 0`
    have : poonFrequency u a = 0 := by
      unfold poonFrequency; rw [← hH0]; simp
    rw [this]
    unfold poonFrequency
    exact div_nonneg (mul_nonneg hb0.le (poonD_nonneg hb0)) (poonH_nonneg hb0)
  · have hHr : ∀ r ∈ Icc a b, 0 < poonH u r := fun r hr =>
      hHpos.trans_le (hHmono (left_mem_Icc.2 hlt.le) hr hr.1)
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) (f := poonFrequency u) ?_ ?_ ?_
      (left_mem_Icc.2 hlt.le) (right_mem_Icc.2 hlt.le) hlt.le
    · intro r hr
      obtain ⟨h0, h1, h2⟩ := hadm r hr
      obtain ⟨N', hN, -⟩ := poonFrequency_deriv_nonneg hsmooth heat hbound h0 h1 h2 (hHr r hr)
      exact hN.continuousAt.continuousWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      have hr' := Ioo_subset_Icc_self hr
      obtain ⟨h0, h1, h2⟩ := hadm r hr'
      obtain ⟨N', hN, -⟩ := poonFrequency_deriv_nonneg hsmooth heat hbound h0 h1 h2 (hHr r hr')
      exact hN.differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      have hr' := Ioo_subset_Icc_self hr
      obtain ⟨h0, h1, h2⟩ := hadm r hr'
      obtain ⟨N', hN, hN'⟩ := poonFrequency_deriv_nonneg hsmooth heat hbound h0 h1 h2 (hHr r hr')
      rw [hN.deriv]
      exact hN'

end

end PDE
