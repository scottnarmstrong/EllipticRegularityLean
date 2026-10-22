module

public import PDEFoundation.Sobolev.H1.Composition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# `H¹` functions bounded below: logarithm and reciprocal

If `u ∈ H¹(U)` satisfies `u ≥ δ > 0` almost everywhere, then `log u` and `u⁻¹` have `H¹`
representatives with gradients `u⁻¹ ∇u` and `-u⁻² ∇u`.  The proof modifies `log` and `t ↦ t⁻¹` on
`(-∞, δ)` to `C¹` functions with bounded derivative and applies the bounded-derivative chain rule.
-/

@[expose] public section

namespace PDE.DGNMLogEnergy

open MeasureTheory intervalIntegral

/-- A `C¹` function with prescribed bounded derivative `g` agreeing with `F` on `[δ, ∞)`. -/
theorem exists_c1_extension {F g : ℝ → ℝ} {δ M : ℝ} (hg : Continuous g)
    (hM : ∀ t, |g t| ≤ M) (hF : ∀ t, δ ≤ t → HasDerivAt F (g t) t) :
    ∃ G : ℝ → ℝ, ContDiff ℝ 1 G ∧ (∀ t, |deriv G t| ≤ M) ∧
      (∀ t, δ ≤ t → G t = F t) ∧ (∀ t, δ ≤ t → deriv G t = g t) := by
  have hG : ∀ t, HasDerivAt (fun t => F δ + ∫ s in δ..t, g s) (g t) t := fun t =>
    ((hg.integral_hasStrictDerivAt δ t).hasDerivAt).const_add (F δ)
  have hderiv : ∀ t, deriv (fun t => F δ + ∫ s in δ..t, g s) t = g t := fun t => (hG t).deriv
  refine ⟨fun t => F δ + ∫ s in δ..t, g s, ?_, fun t => by rw [hderiv]; exact hM t, ?_,
    fun t _ => hderiv t⟩
  · rw [contDiff_one_iff_deriv]
    refine ⟨fun t => (hG t).differentiableAt, ?_⟩
    have : deriv (fun t => F δ + ∫ s in δ..t, g s) = g := funext hderiv
    rw [this]; exact hg
  · intro t ht
    have := integral_eq_sub_of_hasDerivAt (f := F) (f' := g) (a := δ) (b := t)
      (fun x hx => hF x (by rw [Set.uIcc_of_le ht] at hx; exact hx.1))
      (hg.intervalIntegrable _ _)
    simp only [this]; ring

theorem exists_log_modification {δ : ℝ} (hδ : 0 < δ) :
    ∃ G : ℝ → ℝ, ContDiff ℝ 1 G ∧ (∀ t, |deriv G t| ≤ δ⁻¹) ∧
      (∀ t, δ ≤ t → G t = Real.log t) ∧ (∀ t, δ ≤ t → deriv G t = t⁻¹) := by
  have hcont : Continuous fun t : ℝ => (max t δ)⁻¹ :=
    (continuous_id.max continuous_const).inv₀ (fun t => (lt_max_of_lt_right hδ).ne')
  obtain ⟨G, h1, h2, h3, h4⟩ := exists_c1_extension (F := Real.log) (δ := δ)
    (g := fun t => (max t δ)⁻¹) (M := δ⁻¹) hcont
    (fun t => by
      rw [abs_of_nonneg (inv_nonneg.mpr (le_max_of_le_right hδ.le))]
      exact inv_anti₀ hδ (le_max_right _ _))
    (fun t ht => by
      rw [max_eq_left ht]
      exact Real.hasDerivAt_log (lt_of_lt_of_le hδ ht).ne')
  exact ⟨G, h1, h2, h3, fun t ht => by rw [h4 t ht, max_eq_left ht]⟩

theorem exists_inv_modification {δ : ℝ} (hδ : 0 < δ) :
    ∃ G : ℝ → ℝ, ContDiff ℝ 1 G ∧ (∀ t, |deriv G t| ≤ (δ ^ 2)⁻¹) ∧
      (∀ t, δ ≤ t → G t = t⁻¹) ∧ (∀ t, δ ≤ t → deriv G t = -(t ^ 2)⁻¹) := by
  have hpos : ∀ t : ℝ, 0 < max t δ := fun t => lt_max_of_lt_right hδ
  have hcont : Continuous fun t : ℝ => -((max t δ) ^ 2)⁻¹ :=
    ((continuous_id.max continuous_const).pow 2).inv₀
      (fun t => (pow_pos (hpos t) 2).ne') |>.neg
  obtain ⟨G, h1, h2, h3, h4⟩ := exists_c1_extension (F := fun t => t⁻¹) (δ := δ)
    (g := fun t => -((max t δ) ^ 2)⁻¹) (M := (δ ^ 2)⁻¹) hcont
    (fun t => by
      rw [abs_neg, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
      exact inv_anti₀ (pow_pos hδ 2) (pow_le_pow_left₀ hδ.le (le_max_right _ _) 2))
    (fun t ht => by
      rw [max_eq_left ht]
      exact hasDerivAt_inv (lt_of_lt_of_le hδ ht).ne')
  exact ⟨G, h1, h2, h3, fun t ht => by rw [h4 t ht, max_eq_left ht]⟩

variable {d : ℕ} {U : Set (Vec d)}

/-- `log u` has an `H¹` representative with gradient `u⁻¹ ∇u`. -/
theorem exists_logRep (hU : IsOpenBoundedConvexDomain U) (u : H1Function U) {δ : ℝ}
    (hδ : 0 < δ) (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u.toFun x) :
    ∃ V : H1Function U, (∀ᵐ x ∂volumeOn U, V.toFun x = Real.log (u.toFun x)) ∧
      (∀ᵐ x ∂volumeOn U, V.grad x = (u.toFun x)⁻¹ • u.grad x) := by
  obtain ⟨G, hG, hM, hval, hder⟩ := exists_log_modification hδ
  refine ⟨u.compContDiffOfDerivBounded hU hG (inv_nonneg.mpr hδ.le) hM, ?_, ?_⟩
  · filter_upwards [hu] with x hx
    simp only [H1Function.compContDiffOfDerivBounded_toFun]
    exact hval _ hx
  · filter_upwards [hu] with x hx
    rw [H1Function.compContDiffOfDerivBounded_grad]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, hder _ hx]

/-- `u⁻¹` has an `H¹` representative with gradient `-u⁻² ∇u`. -/
theorem exists_invRep (hU : IsOpenBoundedConvexDomain U) (u : H1Function U) {δ : ℝ}
    (hδ : 0 < δ) (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u.toFun x) :
    ∃ W : H1Function U, (∀ᵐ x ∂volumeOn U, W.toFun x = (u.toFun x)⁻¹) ∧
      (∀ᵐ x ∂volumeOn U, W.grad x = (-((u.toFun x) ^ 2)⁻¹) • u.grad x) := by
  obtain ⟨G, hG, hM, hval, hder⟩ := exists_inv_modification hδ
  refine ⟨u.compContDiffOfDerivBounded hU hG (inv_nonneg.mpr (sq_nonneg _)) hM, ?_, ?_⟩
  · filter_upwards [hu] with x hx
    simp only [H1Function.compContDiffOfDerivBounded_toFun]
    exact hval _ hx
  · filter_upwards [hu] with x hx
    rw [H1Function.compContDiffOfDerivBounded_grad]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, hder _ hx]

end PDE.DGNMLogEnergy
