module

public import PDEFoundation.Monotonicity.Poon.DerivBounds
public import PDEFoundation.Monotonicity.Poon.DerivBoundsSlice
public import PDEFoundation.Monotonicity.Poon.DifferentiateParam

/-!
# Setup for differentiating Poon's `H` and `D`

Slice facts for a smooth caloric `u` on `(-T, 0) × ℝᵈ` (continuity of slices, the time derivative of
`∂ᵢ u` at a slice, the heat equation in terms of `deriv`), and the existence, for `s` in the
admissible interval, of a time window `[a, b] ∋ s`, a Gaussian exponent `A'` and a constant `C'`
giving both the heat kernel domination and the pointwise bounds on `u`, `∇u`, `∂ₜ u`, `∇ ∂ₜ u`.
-/

@[expose] public section

open Set Filter MeasureTheory

namespace PDE

noncomputable section

variable {d : ℕ} {u : ℝ → Vec d → ℝ} {T : ℝ}

/-- The joint function attached to `u`. -/
abbrev jointOf (u : ℝ → Vec d → ℝ) : ℝ × Vec d → ℝ := fun p => u p.1 p.2

theorem continuous_slice_of_smooth
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (jointOf u) (Ioo (-T) 0 ×ˢ (univ : Set (Vec d))))
    {t : ℝ} (ht : t ∈ Ioo (-T) 0) : Continuous (u t) :=
  hsmooth.continuousOn.comp_continuous (Continuous.prodMk_right t) fun x => ⟨ht, mem_univ x⟩

theorem continuous_jEx_slice {g : ℝ × Vec d → ℝ} {a b : ℝ} (hg : JSm (slab d a b) g)
    {t : ℝ} (ht : t ∈ Ioo a b) (i : Fin d) : Continuous (fun y : Vec d => jEx i g (t, y)) :=
  ((hg.jEx (isOpen_slab a b) i).continuousOn).comp_continuous (Continuous.prodMk_right t)
    fun x => ⟨ht, mem_univ x⟩

theorem continuous_laplacian_slice
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (jointOf u) (Ioo (-T) 0 ×ˢ (univ : Set (Vec d))))
    {t : ℝ} (ht : t ∈ Ioo (-T) 0) : Continuous (euclideanCoordLaplacian (u t)) := by
  have h : euclideanCoordLaplacian (u t) = fun y => jLap (jointOf u) (t, y) :=
    funext fun y => euclideanCoordLaplacian_slice (isOpen_slab (d := d) (-T) 0) hsmooth
      (⟨ht, mem_univ y⟩ : (t, y) ∈ slab d (-T) 0)
  rw [h]
  exact ((JSm.jLap (isOpen_slab (d := d) (-T) 0) (hsmooth : JSm (slab d (-T) 0) (jointOf u))).continuousOn).comp_continuous
    (Continuous.prodMk_right t) fun x => ⟨ht, mem_univ x⟩

theorem hasDerivAt_slice_time {h : ℝ × Vec d → ℝ} {t : ℝ} {x : Vec d}
    (hd : DifferentiableAt ℝ h (t, x)) : HasDerivAt (fun τ : ℝ => h (τ, x)) (jEt h (t, x)) t := by
  have h0 : HasFDerivAt (fun τ : ℝ => (τ, x)) (ContinuousLinearMap.inl ℝ ℝ (Vec d)) t :=
    hasFDerivAt_prodMk_left t x
  have h1 : HasFDerivAt (fun τ : ℝ => h (τ, x)) _ t := hd.hasFDerivAt.comp t h0
  have h2 := h1.hasDerivAt
  simpa [jEt, jd] using h2

theorem deriv_slice_eq_laplacian
    (heat : ∀ t ∈ Ioo (-T) 0, ∀ x : Vec d,
      HasDerivAt (fun τ : ℝ => u τ x) (euclideanCoordLaplacian (u t) x) t)
    {t : ℝ} (ht : t ∈ Ioo (-T) 0) :
    (fun y : Vec d => deriv (fun τ : ℝ => u τ y) t) = euclideanCoordLaplacian (u t) :=
  funext fun y => (heat t ht y).deriv

theorem jEt_jEx_slice
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (jointOf u) (Ioo (-T) 0 ×ˢ (univ : Set (Vec d))))
    (heat : ∀ t ∈ Ioo (-T) 0, ∀ x : Vec d,
      HasDerivAt (fun τ : ℝ => u τ x) (euclideanCoordLaplacian (u t) x) t)
    {t : ℝ} (ht : t ∈ Ioo (-T) 0) (x : Vec d) (i : Fin d) :
    jEt (jEx i (jointOf u)) (t, x) = classicalGradient (euclideanCoordLaplacian (u t)) x i := by
  have hΩ := isOpen_slab (d := d) (-T) 0
  have hp : (t, x) ∈ slab d (-T) 0 := ⟨ht, mem_univ x⟩
  have e1 : jEt (jEx i (jointOf u)) (t, x) = jEx i (jEt (jointOf u)) (t, x) :=
    jd_comm hΩ hsmooth hp _ _
  have e2 : jEx i (jEt (jointOf u)) (t, x) =
      euclideanCoordDeriv i (fun y : Vec d => jEt (jointOf u) (t, y)) x :=
    (euclideanCoordDeriv_slice hΩ (JSm.jEt hΩ (hsmooth : JSm (slab d (-T) 0) (jointOf u))) i hp).symm
  have e3 : (fun y : Vec d => jEt (jointOf u) (t, y)) = euclideanCoordLaplacian (u t) := by
    rw [← deriv_slice_eq_laplacian heat ht, ← deriv_slice_eq hsmooth ht]
  rw [e1, e2, e3]
  rfl

/-- Window, Gaussian exponent and pointwise bounds around an admissible `s`. -/
theorem exists_poon_domination
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (jointOf u) (Ioo (-T) 0 ×ˢ (univ : Set (Vec d))))
    (heat : ∀ t ∈ Ioo (-T) 0, ∀ x : Vec d,
      HasDerivAt (fun τ : ℝ => u τ x) (euclideanCoordLaplacian (u t) x) t)
    {A C : ℝ}
    (hbound : ∀ t ∈ Ioo (-T) 0, ∀ x : Vec d, |u t x| ≤ C * Real.exp (A * vecNormSq x))
    {s : ℝ} (hs0 : 0 < s) (hsT : s < T) (hAs : 8 * A * s < 1) :
    ∃ a b A' C' : ℝ, 0 < a ∧ a < s ∧ s < b ∧ b < T ∧
      (∃ c M : ℝ, 0 < c ∧ 0 ≤ M ∧ ∀ r ∈ Icc a b, ∀ x : Vec d,
        (1 + vecNormSq x) * (Real.exp (2 * A' * vecNormSq x) * heatKernel d r x) ≤
          M * Real.exp (-c * vecNormSq x)) ∧
      0 ≤ C' ∧ ∀ r ∈ Icc a b, ∀ x : Vec d,
        |u (-r) x| ≤ C' * Real.exp (A' * vecNormSq x) ∧
        vecEuclideanNorm (classicalGradient (u (-r)) x) ≤ C' * Real.exp (A' * vecNormSq x) ∧
        |euclideanCoordLaplacian (u (-r)) x| ≤ C' * Real.exp (A' * vecNormSq x) ∧
        vecEuclideanNorm (classicalGradient (euclideanCoordLaplacian (u (-r))) x) ≤
          C' * Real.exp (A' * vecNormSq x) := by
  have hev : ∀ᶠ b in nhds s, b < T ∧ 8 * A * b < 1 :=
    (eventually_lt_nhds hsT).and
      ((Continuous.tendsto (by fun_prop : Continuous fun b : ℝ => 8 * A * b) s).eventually
        (eventually_lt_nhds hAs))
  obtain ⟨b, hsb, hbT, hAb⟩ := hev.exists_gt
  have ha : 0 < s / 2 := by linarith
  obtain ⟨A', hAA', hA'b, hG⟩ := heatKernel_gaussian_domination d A ha
    (show s / 2 ≤ b by linarith) hAb
  obtain ⟨c, M, hc, hM, hGM⟩ := hG 1
  obtain ⟨C', hC', hB⟩ := derivBounds_exists hsmooth heat hbound (t₁ := -b) (t₂ := -(s / 2))
    (A' := A') (by linarith) (by linarith) hAA'
  refine ⟨s / 2, b, A', C', ha, by linarith, hsb, hbT, ⟨c, M, hc, hM, ?_⟩, hC', ?_⟩
  · intro r hr x
    simpa using hGM r hr x
  · intro r hr x
    obtain ⟨h1, h2, -, -, h5, h6⟩ := hB (-r) ⟨by linarith [hr.2], by linarith [hr.1]⟩ x
    have ht : -r ∈ Ioo (-T) 0 := ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have e := deriv_slice_eq_laplacian heat ht
    rw [e] at h6
    have h5' : |euclideanCoordLaplacian (u (-r)) x| ≤ C' * Real.exp (A' * vecNormSq x) := by
      rw [← (heat (-r) ht x).deriv]; exact h5
    exact ⟨h1, h2, h5', h6⟩

end

end PDE
