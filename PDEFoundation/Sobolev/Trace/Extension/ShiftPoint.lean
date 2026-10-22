module

public import PDEFoundation.Sobolev.Trace.Extension.ShiftDiff

/-!
# Pointwise bound for `shift τ - ext` and its gradient on `Ω`

For `x ∈ Ω`, both `|shift τ g x - ext g x|` and the Euclidean length of
`∇ shift τ g x - ∇ ext g x` are bounded by `∑ⱼ Kⱼ · R_{j,τ}(φⱼ⁻¹ x)`, where `R_{j,τ}` is the
quantity `shiftR` of the flat extension `Fⱼ`, cut off to the half-space.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

theorem shift_vecEuclideanNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → Vec (n + 1)) :
    vecEuclideanNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, vecEuclideanNorm (f i) :=
  Finset.le_sum_of_subadditive vecEuclideanNorm (vecEuclideanNorm_eq_zero_iff.2 rfl).le
    vecEuclideanNorm_add_le s f

/-- The `j`-th difference of two shifts. -/
noncomputable def ExtData.diffTerm (D : ExtData Ω) (j : Fin D.A.N) (τ : ℝ)
    (g : Vec (n + 1) → ℝ) (y : Vec (n + 1)) : ℝ :=
  D.term j τ g y - D.term j 0 g y

theorem ExtData.shift_sub_ext_eq (D : ExtData Ω) (τ : ℝ) (g : Vec (n + 1) → ℝ) (y : Vec (n + 1)) :
    D.shift τ g y - D.ext g y = ∑ j, D.diffTerm j τ g y := by
  rw [← D.shift_zero g]
  simp only [ExtData.diffTerm, Finset.sum_sub_distrib]
  rfl

theorem ExtData.diffTerm_contDiffAt (D : ExtData Ω) (j : Fin D.A.N) {p : ℝ} (hp : 1 < p)
    {g : Vec (n + 1) → ℝ} (hg : IsBesov Ω (1 - 1 / p) p g) {τ : ℝ} (hτ : 0 < τ)
    {x : Vec (n + 1)} (hx : x ∈ Ω) : ContDiffAt ℝ 1 (D.diffTerm j τ g) x :=
  (D.term_contDiffAt j hp hg fun h => by
    have := (D.A.chart j).inv_snd_pos_of_mem hx (D.η_tsupport j h); linarith).sub
    (D.term_contDiffAt j hp hg fun h => D.pos_of_mem hx j h)

theorem ExtData.gradient_shift_sub_ext (D : ExtData Ω) {p : ℝ} (hp : 1 < p)
    {g : Vec (n + 1) → ℝ} (hg : IsBesov Ω (1 - 1 / p) p g) {τ : ℝ} (hτ : 0 < τ)
    {x : Vec (n + 1)} (hx : x ∈ Ω) :
    classicalGradient (D.shift τ g) x - classicalGradient (D.ext g) x =
      ∑ j, classicalGradient (D.diffTerm j τ g) x := by
  have hcl : x ∈ closure Ω := subset_closure hx
  have hd1 : DifferentiableAt ℝ (D.shift τ g) x :=
    (D.shift_contDiffAt hp hg fun j hj => D.pos_of_mem_closure hcl hτ j hj).differentiableAt
      one_ne_zero
  have hd0 : DifferentiableAt ℝ (D.shift 0 g) x :=
    (D.shift_contDiffAt hp hg fun j hj => D.pos_of_mem hx j hj).differentiableAt one_ne_zero
  have hdj : ∀ j ∈ (Finset.univ : Finset (Fin D.A.N)),
      DifferentiableAt ℝ (D.diffTerm j τ g) x := fun j _ =>
    (D.diffTerm_contDiffAt j hp hg hτ hx).differentiableAt one_ne_zero
  have hsum : (fun y => ∑ j, D.diffTerm j τ g y) = fun y => D.shift τ g y - D.shift 0 g y := by
    funext y
    rw [← D.shift_sub_ext_eq, D.shift_zero]
  funext i
  have h1 : fderiv ℝ (fun y => ∑ j, D.diffTerm j τ g y) x = fderiv ℝ (D.shift τ g) x -
      fderiv ℝ (D.shift 0 g) x := by
    rw [hsum, fderiv_fun_sub hd1 hd0]
  have h2 := fderiv_fun_sum hdj
  rw [h1] at h2
  simp only [Pi.sub_apply, Finset.sum_apply, classicalGradient_apply, ← D.shift_zero g]
  have := congrArg (fun L => L (basisVec i)) h2
  simpa using this

/-- Pointwise bound on `Ω` for the difference of the shifted extension and the extension. -/
theorem ExtData.exists_shift_pointwise (D : ExtData Ω) {p : ℝ} (hp : 1 < p)
    {g : Vec (n + 1) → ℝ} (hg : IsBesov Ω (1 - 1 / p) p g) :
    ∃ K : Fin D.A.N → ℝ, (∀ j, 0 ≤ K j) ∧ ∀ τ : ℝ, 0 < τ → ∀ x ∈ Ω,
      |D.shift τ g x - D.ext g x| ≤ ∑ j, K j * (upperHalf n).indicator
          (shiftR (modelExt n (D.flat j g)) τ) ((D.A.chart j).inv x) ∧
        vecEuclideanNorm (classicalGradient (D.shift τ g) x - classicalGradient (D.ext g) x) ≤
          ∑ j, K j * (upperHalf n).indicator
            (shiftR (modelExt n (D.flat j g)) τ) ((D.A.chart j).inv x) := by
  have hB : ∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ y, |D.η j y| ≤ B ∧
      vecEuclideanNorm (classicalGradient (D.η j) y) ≤ B := fun j =>
    exists_cutoff_bounds ((D.η_smooth j).of_le (by exact_mod_cast le_top)) (D.η_compact j)
  choose B hB0 hB using hB
  refine ⟨fun j => B j * (3 + (D.A.chart j).L), fun j => ?_, fun τ hτ x hx => ?_⟩
  · have := (D.A.chart j).L_nonneg
    have := hB0 j
    positivity
  have hpt : ∀ j, |D.diffTerm j τ g x| ≤ B j * (3 + (D.A.chart j).L) * (upperHalf n).indicator
          (shiftR (modelExt n (D.flat j g)) τ) ((D.A.chart j).inv x) ∧
      vecEuclideanNorm (classicalGradient (D.diffTerm j τ g) x) ≤ B j * (3 + (D.A.chart j).L) *
        (upperHalf n).indicator (shiftR (modelExt n (D.flat j g)) τ) ((D.A.chart j).inv x) :=
    fun j => shift_term_diff_bound (D.A.chart j) ((D.η_smooth j).of_le (by exact_mod_cast le_top))
      (D.η_tsupport j) (contDiffOn_modelExt (D.locallyIntegrable_flat j hp hg)) hτ (hB j) hx
  refine ⟨?_, ?_⟩
  · rw [D.shift_sub_ext_eq]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => (hpt j).1)
  · rw [D.gradient_shift_sub_ext hp hg hτ hx]
    exact (shift_vecEuclideanNorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (hpt j).2)

end PDE.TraceLane
