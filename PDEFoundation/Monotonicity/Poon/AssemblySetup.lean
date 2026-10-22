module

public import PDEFoundation.Monotonicity.Poon.IdentitiesFinal

/-!
# `PoonSetup` for the time slice of a caloric function

For `s` in the admissible interval, the slice `v = u(-s, ·)` carries a `PoonSetup`: smoothness,
Gaussian integrability of the weights, and Gaussian-type bounds on `v`, `∂ᵢ v`, `∂ᵢ∂ⱼ v`, `Δ v`
and `∂ᵢ Δ v`.
-/

@[expose] public section

open Set MeasureTheory

namespace PDE

noncomputable section

variable {d : ℕ} {u : ℝ → Vec d → ℝ} {T : ℝ}

theorem PDom.of_bound {a K : ℝ} {f : Vec d → ℝ} (hf : Continuous f) (hK : 0 ≤ K)
    (h : ∀ x, |f x| ≤ K * Real.exp (a * vecNormSq x)) : PDom a f :=
  ⟨hf, K, 0, hK, fun x => by simpa using h x⟩

theorem sm_slice
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (jointOf u) (Ioo (-T) 0 ×ˢ (univ : Set (Vec d))))
    {t : ℝ} (ht : t ∈ Ioo (-T) 0) : Sm (u t) := by
  show ContDiff ℝ (⊤ : ℕ∞) (u t)
  rw [contDiff_iff_contDiffAt]
  intro x
  have hopen : IsOpen (Ioo (-T) 0 ×ˢ (univ : Set (Vec d))) := isOpen_Ioo.prod isOpen_univ
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (jointOf u) (t, x) :=
    hsmooth.contDiffAt (hopen.mem_nhds ⟨ht, mem_univ x⟩)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => (t, y)) := contDiff_const.prodMk contDiff_id
  exact h1.comp x h2.contDiffAt

/-- The slice `u(-s, ·)` admits a `PoonSetup` for some Gaussian exponent `A'`. -/
theorem exists_poonSetup
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (jointOf u) (Ioo (-T) 0 ×ˢ (univ : Set (Vec d))))
    (heat : ∀ t ∈ Ioo (-T) 0, ∀ x : Vec d,
      HasDerivAt (fun τ : ℝ => u τ x) (euclideanCoordLaplacian (u t) x) t)
    {A C : ℝ}
    (hbound : ∀ t ∈ Ioo (-T) 0, ∀ x : Vec d, |u t x| ≤ C * Real.exp (A * vecNormSq x))
    {s : ℝ} (hs0 : 0 < s) (hsT : s < T) (hAs : 8 * A * s < 1) :
    ∃ A' : ℝ, PoonSetup (u (-s)) s A' := by
  have ht : -s ∈ Ioo (-T) 0 := ⟨by linarith, by linarith⟩
  obtain ⟨A', hAA', -, hG⟩ := heatKernel_gaussian_domination d A hs0 le_rfl hAs
  obtain ⟨C', hC', hB⟩ := derivBounds_exists hsmooth heat hbound (t₁ := -s) (t₂ := -s)
    (A' := A') (by linarith) (by linarith) hAA'
  have hv := sm_slice hsmooth ht
  have hb := hB (-s) ⟨le_rfl, le_rfl⟩
  have hb' : ∀ x, _ := hb
  refine ⟨A', ?_⟩
  have hS : ∀ i j, PDom A' (euclideanCoordSecondDeriv i j (u (-s))) := fun i j =>
    PDom.of_bound (sm_S hv i j).continuous hC' fun x => (hb' x).2.2.1 j i
  refine ⟨hs0, hv, ?_, ?_, ?_, hS, ?_, ?_⟩
  · intro k
    obtain ⟨c, M, hc, hM, hcM⟩ := hG k
    refine Integrable.mono' ((integrable_exp_neg_mul_vecNormSq (d := d) hc).const_mul M) ?_
      (Filter.Eventually.of_forall fun x => ?_)
    · have hq : Continuous (fun x : Vec d => vecNormSq x) := contDiff_vecNormSq.continuous
      exact (((continuous_const.add hq).pow k).mul
        ((Real.continuous_exp.comp (continuous_const.mul hq)).mul
          continuous_heatKernel_space)).aestronglyMeasurable
    · have := hcM s ⟨le_rfl, le_rfl⟩ x
      rw [Real.norm_eq_abs, abs_of_nonneg (by
        have := heatKernel_pos d hs0 x
        have := one_le_one_add_vecNormSq x
        positivity)]
      rw [← two_mul]
      exact this
  · exact PDom.of_bound hv.continuous hC' fun x => (hb' x).1
  · intro i
    exact PDom.of_bound (hv.coordDeriv i).continuous hC' fun x =>
      ((abs_apply_le_vecEuclideanNorm (classicalGradient (u (-s)) x) i).trans (hb' x).2.1)
  · have : euclideanCoordLaplacian (u (-s)) = fun x => ∑ i, euclideanCoordSecondDeriv i i (u (-s)) x :=
      rfl
    rw [this]
    exact PDom.sum _ _ fun i _ => hS i i
  · intro i
    have h1 : ∀ x, euclideanCoordDeriv i (euclideanCoordLaplacian (u (-s))) x =
        ∑ j, euclideanCoordDeriv i (euclideanCoordSecondDeriv j j (u (-s))) x := by
      intro x
      exact coordDeriv_sum _ (fun j => sm_S hv j j) i x
    refine PDom.congr (fun x => (h1 x).symm) ?_
    exact PDom.sum _ _ fun j _ =>
      PDom.of_bound (((sm_S hv j j).coordDeriv i)).continuous hC' fun x => (hb' x).2.2.2.1 i j j

end

end PDE
