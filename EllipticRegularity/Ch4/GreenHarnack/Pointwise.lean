module

public import EllipticRegularity.Ch4.GreenHarnack.Annulus

/-!
# Corollaries of the Harnack inequality in annuli

* the version on `A_r = B_r ∖ B_{r/2} ⊆ D_r` used in `greenD3`;
* the pointwise version for a representative that is continuous on the open shell
  `{r/4 < |x| < 3r/2}`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4GreenHarnack

open PDE MeasureTheory

variable {d : ℕ}

/-- An a.e. two-sided bound on an open set for a function continuous there holds everywhere. -/
theorem forall_mem_of_ae_bounds {W : Set (Vec d)} (hW : IsOpen W) {g : Vec d → ℝ}
    (hg : ContinuousOn g W) {p q : ℝ}
    (h : ∀ᵐ x ∂volumeOn W, p ≤ g x ∧ g x ≤ q) : ∀ x ∈ W, p ≤ g x ∧ g x ≤ q := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hxW, hx⟩ := hcon
  have hopen : IsOpen (W ∩ g ⁻¹' {v | ¬ (p ≤ v ∧ v ≤ q)}) := by
    refine hg.isOpen_inter_preimage hW ?_
    have : {v : ℝ | ¬ (p ≤ v ∧ v ≤ q)} = (Set.Icc p q)ᶜ := by ext v; simp
    rw [this]; exact isClosed_Icc.isOpen_compl
  have hnull : volume (W ∩ g ⁻¹' {v | ¬ (p ≤ v ∧ v ≤ q)}) = 0 := by
    have h1 := (ae_restrict_iff' hW.measurableSet).1 h
    rw [ae_iff] at h1
    refine measure_mono_null ?_ h1
    intro y ⟨hyW, hy⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hy
    simp only [Set.mem_ofPred_eq, not_imp, not_and]
    exact ⟨hyW, fun h1 h2 => hy ⟨h1, h2⟩⟩
  have := hopen.measure_eq_zero_iff volume |>.1 hnull
  have hx' : x ∈ W ∩ g ⁻¹' {v | ¬ (p ≤ v ∧ v ≤ q)} := ⟨hxW, by
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    intro h1; exact absurd (hx h1.1) (not_lt.2 h1.2)⟩
  rw [this] at hx'
  exact hx'

/-- The Harnack inequality in annuli, on `A_r = B_r ∖ B_{r/2}` (`A_r ⊆ D_r`). -/
theorem harnack_annulus_A (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField d) (r : ℝ), 0 < r →
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j)
        (volumeOn (euclideanBall (0 : Vec d) (2 * r) \ euclideanClosedBall (0 : Vec d) (r / 8)))) →
      (∀ x ∈ euclideanBall (0 : Vec d) (2 * r) \ euclideanClosedBall (0 : Vec d) (r / 8),
        IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function
          (euclideanBall (0 : Vec d) (2 * r) \ euclideanClosedBall (0 : Vec d) (r / 8)),
        (∀ᵐ x ∂volumeOn
          (euclideanBall (0 : Vec d) (2 * r) \ euclideanClosedBall (0 : Vec d) (r / 8)),
          0 ≤ u.toFun x) →
        IsWeakDivergenceFormSolutionOn a
          (euclideanBall (0 : Vec d) (2 * r) \ euclideanClosedBall (0 : Vec d) (r / 8)) u
          (0 : Vec d → ℝ) 0 →
        ∃ m : ℝ, 0 ≤ m ∧
          ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) r \ euclideanBall (0 : Vec d) (r / 2)),
            m ≤ u.toFun x ∧ u.toFun x ≤ Real.exp (C * Real.sqrt Λ) * m := by
  obtain ⟨C, hC, h⟩ := harnack_annulus d hd
  refine ⟨C, hC, fun Λ a r hr ha hEll u hu0 hsol => ?_⟩
  obtain ⟨m, hm, hae⟩ := h Λ a r hr ha hEll u hu0 hsol
  refine ⟨m, hm, ae_restrict_of_ae_restrict_of_subset ?_ hae⟩
  intro x ⟨h1, h2⟩
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hr] at h1
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith)] at h2
  refine ⟨?_, ?_⟩
  · rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith)]; linarith
  · rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith)]; intro h; apply h2; linarith

/-- The Harnack inequality in annuli for a representative `v` of `u` that is continuous on the
open shell `{r/4 < |x| < 3r/2}`: the bounds hold at every point of the shell. -/
theorem harnack_annulus_pointwise (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField d) (r : ℝ), 0 < r →
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j)
        (volumeOn (euclideanBall (0 : Vec d) (2 * r) \ euclideanClosedBall (0 : Vec d) (r / 8)))) →
      (∀ x ∈ euclideanBall (0 : Vec d) (2 * r) \ euclideanClosedBall (0 : Vec d) (r / 8),
        IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function
          (euclideanBall (0 : Vec d) (2 * r) \ euclideanClosedBall (0 : Vec d) (r / 8)),
        (∀ᵐ x ∂volumeOn
          (euclideanBall (0 : Vec d) (2 * r) \ euclideanClosedBall (0 : Vec d) (r / 8)),
          0 ≤ u.toFun x) →
        IsWeakDivergenceFormSolutionOn a
          (euclideanBall (0 : Vec d) (2 * r) \ euclideanClosedBall (0 : Vec d) (r / 8)) u
          (0 : Vec d → ℝ) 0 →
        ∀ v : Vec d → ℝ,
          ContinuousOn v (euclideanBall (0 : Vec d) (3 * r / 2) \ euclideanClosedBall (0 : Vec d) (r / 4)) →
          v =ᵐ[volumeOn
            (euclideanBall (0 : Vec d) (2 * r) \ euclideanClosedBall (0 : Vec d) (r / 8))] u.toFun →
        ∃ m : ℝ, 0 ≤ m ∧
          ∀ x : Vec d, r / 4 < vecEuclideanNorm x → vecEuclideanNorm x < 3 * r / 2 →
            m ≤ v x ∧ v x ≤ Real.exp (C * Real.sqrt Λ) * m := by
  obtain ⟨C, hC, h⟩ := harnack_annulus d hd
  refine ⟨C, hC, fun Λ a r hr ha hEll u hu0 hsol v hvc hvu => ?_⟩
  obtain ⟨m, hm, hae⟩ := h Λ a r hr ha hEll u hu0 hsol
  refine ⟨m, hm, ?_⟩
  set W := euclideanBall (0 : Vec d) (3 * r / 2) \ euclideanClosedBall (0 : Vec d) (r / 4) with hW
  have hWopen : IsOpen W := (isOpen_euclideanBall _ _).sdiff (isClosed_euclideanClosedBall _ _)
  have hWD : W ⊆ annulusD d r := by
    intro x ⟨h1, h2⟩
    refine ⟨h1, fun h3 => h2 ?_⟩
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith)] at h3
    rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by linarith)]; linarith
  have hWV : W ⊆ annulusV d r := hWD.trans (annulusD_subset_annulusV hr)
  have h1 : ∀ᵐ x ∂volumeOn W, m ≤ v x ∧ v x ≤ Real.exp (C * Real.sqrt Λ) * m := by
    have hvuW : ∀ᵐ x ∂volumeOn W, v x = u.toFun x :=
      ae_restrict_of_ae_restrict_of_subset hWV hvu
    have haeW : ∀ᵐ x ∂volumeOn W, m ≤ u.toFun x ∧ u.toFun x ≤ Real.exp (C * Real.sqrt Λ) * m :=
      ae_restrict_of_ae_restrict_of_subset hWD hae
    filter_upwards [hvuW, haeW] with x h1 h2
    rwa [h1]
  have := forall_mem_of_ae_bounds hWopen hvc h1
  intro x hx1 hx2
  apply this
  refine ⟨?_, ?_⟩
  · rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith), sub_zero]; exact hx2
  · rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by linarith), sub_zero]
    intro h; linarith

end PDE.Ch4GreenHarnack
