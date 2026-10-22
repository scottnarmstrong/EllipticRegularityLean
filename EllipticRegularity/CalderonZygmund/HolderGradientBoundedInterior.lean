module

public import EllipticRegularity.CalderonZygmund.HolderGradientBoundedBall

/-! # Interior boundedness of gradients with Hölder data -/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

/-- Hölder coefficients and forcing on the unit ball give an essentially
bounded Euclidean gradient on the ball of radius `3 / 4`. -/
theorem memLp_top_vecEuclideanNorm_grad_three_fourths_ball_of_holder
    {d : ℕ} (hd : 0 < d) {Λ α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (a : CoeffField d) (F : Vec d → Vec d)
    (hell : ∀ x ∈ euclideanBall (0 : Vec d) 1,
      IsEllipticMatrix 1 Λ (a x))
    (ha : ∃ K : ℝ, 0 ≤ K ∧
      EuclideanMatrixHolderSeminormLE (euclideanBall (0 : Vec d) 1) a α K)
    (hF : ∃ K : ℝ, 0 ≤ K ∧
      EuclideanFieldHolderSeminormLE (euclideanBall (0 : Vec d) 1) F α K)
    (u : H1Function (euclideanBall (0 : Vec d) 1))
    (hsol : IsWeakDivergenceFormSolutionOn a
      (euclideanBall (0 : Vec d) 1) u 0 F) :
    MemLp (fun x => vecEuclideanNorm (u.grad x)) ∞
      (volumeOn (euclideanBall (0 : Vec d) (3 / 4))) ∧
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) (3 / 4)),
      vecEuclideanNorm (u.grad x) ≤ M := by
  classical
  let K := euclideanClosedBall (0 : Vec d) (3 / 4)
  let outer : K → Set (Vec d) := fun z => euclideanBall z.1 (1 / 8)
  let inner : K → Set (Vec d) := fun z => euclideanBall z.1 (1 / 16)
  have houterSub (z : K) : outer z ⊆ euclideanBall (0 : Vec d) 1 := by
    intro x hx
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2
    have hxz := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hx
    have hz : vecEuclideanNorm (z.1 - 0) ≤ 3 / 4 :=
      (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by norm_num)).1 z.2
    have htri : vecEuclideanNorm (x - 0) ≤
        vecEuclideanNorm (x - z.1) + vecEuclideanNorm (z.1 - 0) := by
      calc
        vecEuclideanNorm (x - 0) =
            vecEuclideanNorm ((x - z.1) + (z.1 - 0)) := by
              congr 1
              ext i
              simp
        _ ≤ _ := vecEuclideanNorm_add_le _ _
    linarith
  have hlocal (z : K) : MemLp (fun x => vecEuclideanNorm (u.grad x)) ∞
      (volumeOn (inner z)) := by
    let uz := u.restrict (isOpen_euclideanBall _ _) (houterSub z)
    have hsolz : IsWeakDivergenceFormSolutionOn a (outer z) uz 0 F :=
      hsol.restrict (isOpen_euclideanBall _ _) (isOpen_euclideanBall _ _)
        (houterSub z)
    have hellz : ∀ x ∈ outer z, IsEllipticMatrix 1 Λ (a x) :=
      fun x hx => hell x (houterSub z hx)
    obtain ⟨Ka, hKa, haKa⟩ := ha
    obtain ⟨KF, hKF, hFKF⟩ := hF
    have haz : ∃ C : ℝ, 0 ≤ C ∧
        EuclideanMatrixHolderSeminormLE (outer z) a α C :=
      ⟨Ka, hKa, fun x hx y hy ξ =>
        haKa x (houterSub z hx) y (houterSub z hy) ξ⟩
    have hFz : ∃ C : ℝ, 0 ≤ C ∧
        EuclideanFieldHolderSeminormLE (outer z) F α C :=
      ⟨KF, hKF, fun x hx y hy =>
        hFKF x (houterSub z hx) y (houterSub z hy)⟩
    have hz := memLp_top_vecEuclideanNorm_grad_halfBall_of_holder_ball
      hd (show 0 < (1 / 8 : ℝ) by norm_num) hα0 hα1 z.1 a F
      hellz haz hFz uz hsolz
    simpa only [inner, outer, uz, H1Function.restrict_grad,
      show (1 / 8 : ℝ) / 2 = 1 / 16 by norm_num] using hz
  have hcover : K ⊆ ⋃ z : K, inner z := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
    dsimp only [inner]
    exact center_mem_euclideanBall x (by norm_num)
  obtain ⟨s, hs⟩ :=
    (isCompact_euclideanClosedBall (0 : Vec d) (show 0 ≤ (3 / 4 : ℝ) by norm_num)).elim_finite_subcover
      inner (fun z => isOpen_euclideanBall _ _) hcover
  let f : Vec d → ℝ := fun x => vecEuclideanNorm (u.grad x)
  let C : K → ℝ := fun z => (eLpNorm f ∞ (volumeOn (inner z))).toReal
  have hClocal (z : K) : ∀ᵐ x ∂volumeOn (inner z), f x ≤ C z := by
    have hb := ae_le_eLpNormEssSup (f := f) (μ := volumeOn (inner z))
    rw [← eLpNorm_exponent_top (hlocal z).aestronglyMeasurable] at hb
    filter_upwards [hb] with x hx
    have htop := (hlocal z).eLpNorm_ne_top
    have hfx : 0 ≤ f x := vecEuclideanNorm_nonneg _
    have hx' : ENNReal.ofReal (f x) ≤
        eLpNorm f ∞ (volumeOn (inner z)) := by
      simpa [Real.enorm_eq_ofReal_abs, abs_of_nonneg hfx] using hx
    have hreal :=
      (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top htop).2 hx'
    simpa [f, C, ENNReal.toReal_ofReal (vecEuclideanNorm_nonneg _)] using hreal
  let M := ∑ z ∈ s, C z
  have hCnonneg (z : K) : 0 ≤ C z := ENNReal.toReal_nonneg
  have hlocalM (z : K) (hz : z ∈ s) :
      ∀ᵐ x ∂volumeOn (inner z), f x ≤ M := by
    filter_upwards [hClocal z] with x hx
    exact hx.trans (Finset.single_le_sum (fun y _ => hCnonneg y) hz)
  have hunionM : ∀ᵐ x ∂volumeOn (⋃ z ∈ s, inner z), f x ≤ M :=
    (ae_restrict_biUnion_finset_iff inner s _).2 hlocalM
  have hballSub : euclideanBall (0 : Vec d) (3 / 4) ⊆ ⋃ z ∈ s, inner z :=
    (euclideanBall_subset_euclideanClosedBall (0 : Vec d) (3 / 4)).trans hs
  have hbound : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) (3 / 4)),
      f x ≤ M :=
    ae_restrict_of_ae_restrict_of_subset hballSub hunionM
  have hmeas : AEStronglyMeasurable f
      (volumeOn (euclideanBall (0 : Vec d) (3 / 4))) := by
    exact (u.gradMemL2.memLp_vecEuclideanNorm.aestronglyMeasurable).mono_measure
      (Measure.restrict_mono (by
        intro x hx
        exact euclideanBall_mono (x₀ := (0 : Vec d))
          (r := (3 / 4 : ℝ)) (R := 1) (by norm_num) (by norm_num) hx) le_rfl)
  have hM : 0 ≤ M := Finset.sum_nonneg fun z _ => hCnonneg z
  refine ⟨?_, M, hM, hbound⟩
  apply memLp_top_of_bound hmeas M
  filter_upwards [hbound] with x hx
  simpa [f, abs_of_nonneg (vecEuclideanNorm_nonneg _)] using hx

end

end PDE
