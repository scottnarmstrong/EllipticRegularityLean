module

public import EllipticRegularity.Ch4.Meyers.SharpDirichletEq

/-!
# Proposition 4.7 (parts (i) and (ii))

The theorem `meyers_sharpness_example_full` has exactly the type of the statement
`meyers_sharpness_example`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4Meyers

open MeasureTheory Set Filter
open scoped Topology

theorem sharpW_zero_one_eq (d : ℕ) (hd : 2 ≤ d) (j : Fin d) :
    sharpW (⟨0, by omega⟩ : Fin d) ⟨1, by omega⟩ j = if j.val < 2 then 1 else 0 := by
  unfold sharpW
  have : (j = ⟨0, by omega⟩ ∨ j = ⟨1, by omega⟩) ↔ j.val < 2 := by
    constructor
    · rintro (rfl | rfl) <;> simp
    · intro h
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
      · left; ext; simp; omega
      · right; ext; simp; omega
  simp only [this]

theorem classicalGradient_sharpχ_zero {d : ℕ} {x : Vec d}
    (hx : x ∈ euclideanBall (0 : Vec d) (1 / 4)) :
    classicalGradient (sharpχ (d := d)) x = 0 := by
  have hev : sharpχ =ᶠ[𝓝 x] fun _ : Vec d => (1 : ℝ) := by
    filter_upwards [(isOpen_euclideanBall (0 : Vec d) (1 / 4)).mem_nhds hx] with y hy
    exact sharpχ_one hy
  funext j
  rw [classicalGradient_apply, hev.fderiv_eq]
  simp

/-- Exponent arithmetic: `p (-γ) < 1 ↔ p < 2/(1 - 1/√Λ)`. -/
theorem mul_neg_sharpγ_lt_one_iff {Λ : ℝ} (hΛ : 1 < Λ) {p : ℝ} :
    p * (-sharpγ Λ) < 1 ↔ p < 2 / (1 - 1 / Real.sqrt Λ) := by
  have h1 : 1 < Real.sqrt Λ := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one hΛ
  have h2 : 0 < 1 - 1 / Real.sqrt Λ := by
    have : 1 / Real.sqrt Λ < 1 := by rw [div_lt_one (by linarith)]; exact h1
    linarith
  rw [lt_div_iff₀ h2]
  unfold sharpγ
  constructor <;> intro h <;> linarith

/-- Sharpness of the Meyers range (Proposition 4.7, parts (i) and (ii)). -/
theorem meyers_sharpness_example_full (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 < Λ) :
    ∃ a : CoeffField d,
      (∀ (x : Vec d) (i j : Fin d), a x i j =
        (if i = j then 1 else 0) +
          (if i.val < 2 ∧ j.val < 2 ∧ x ⟨0, by omega⟩ ^ 2 + x ⟨1, by omega⟩ ^ 2 ≠ 0 then
            (Λ - 1) * x i * x j / (x ⟨0, by omega⟩ ^ 2 + x ⟨1, by omega⟩ ^ 2) else 0)) ∧
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) ∧
      (∀ x, IsEllipticMatrix 1 Λ (a x)) ∧
      (∀ x i j, a x i j = a x j i) ∧
      -- (i)
      (∃ u : H1Function (euclideanBall (0 : Vec d) 1),
        (∀ x : Vec d, u.toFun x =
          (x ⟨0, by omega⟩ ^ 2 + x ⟨1, by omega⟩ ^ 2) ^ ((1 / Real.sqrt Λ - 1) / 2) *
            x ⟨0, by omega⟩) ∧
        IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u
          (0 : Vec d → ℝ) 0 ∧
        ∀ p : ℝ, 0 < p →
          (MemLp (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
              (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ↔
            p < 2 / (1 - 1 / Real.sqrt Λ))) ∧
      -- (ii)
      (∃ χ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
        tsupport χ ⊆ euclideanBall (0 : Vec d) 1 ∧
        (∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ euclideanBall (0 : Vec d) δ, χ x = 1) ∧
        ∃ f : Vec d → Vec d,
          (∀ i : Fin d, AEStronglyMeasurable (fun x => f x i)
            (volumeOn (euclideanBall (0 : Vec d) 1))) ∧
          (∃ M : ℝ, ∀ x ∈ euclideanBall (0 : Vec d) 1, vecEuclideanNorm (f x) ≤ M) ∧
          ∃ U : H10Function (euclideanBall (0 : Vec d) 1),
            (∀ x : Vec d, U.toFun x = χ x *
              ((x ⟨0, by omega⟩ ^ 2 + x ⟨1, by omega⟩ ^ 2) ^ ((1 / Real.sqrt Λ - 1) / 2) *
                x ⟨0, by omega⟩)) ∧
            IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) U.toH1Function
              (0 : Vec d → ℝ) f ∧
            ∀ p : ℝ, 2 / (1 - 1 / Real.sqrt Λ) ≤ p →
              ¬ MemLp (fun x => vecEuclideanNorm (U.grad x)) (ENNReal.ofReal p)
                (volumeOn (euclideanBall (0 : Vec d) 1)))
:= by
  classical
  set i0 : Fin d := ⟨0, by omega⟩ with hi0
  set i1 : Fin d := ⟨1, by omega⟩ with hi1
  have hi : i0 ≠ i1 := by
    intro h; have := congrArg Fin.val h; simp [hi0, hi1] at this
  have hw := sharpW_01 i0 i1
  have hs : ∀ x : Vec d, axisSq (sharpW i0 i1) x = x i0 ^ 2 + x i1 ^ 2 := fun x =>
    axisSq_planar hi (sharpW_i0 i0 i1) (sharpW_i1 i0 i1) (fun j h0 h1 => sharpW_rest h0 h1) x
  have hq : 0 < Real.sqrt Λ := Real.sqrt_pos.mpr (by linarith)
  refine ⟨meyersCoeff (sharpW i0 i1) Λ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x i j
    unfold meyersCoeff
    rw [hs x, sharpW_zero_one_eq d hd i, sharpW_zero_one_eq d hd j]
    by_cases hij : i.val < 2 ∧ j.val < 2
    · by_cases h0 : x i0 ^ 2 + x i1 ^ 2 = 0
      · simp [hij, h0]
      · simp [hij, h0]
    · have : ¬ (i.val < 2 ∧ j.val < 2 ∧ x i0 ^ 2 + x i1 ^ 2 ≠ 0) := fun h => hij ⟨h.1, h.2.1⟩
      simp only [this, ↓reduceIte]
      by_cases hi2 : i.val < 2
      · have hj2 : ¬ j.val < 2 := fun h => hij ⟨hi2, h⟩
        simp [hj2]
      · simp [hi2]
  · intro i j
    exact (measurable_meyersCoeff_apply _ Λ i j).aemeasurable
  · intro x
    exact isEllipticMatrix_meyersCoeff hw hΛ.le x
  · intro x i j
    exact meyersCoeff_symm _ Λ x i j
  · refine ⟨sharpU hi hΛ, ?_, sharp_solution hi hΛ, ?_⟩
    · intro x
      show prof (sharpW i0 i1) (sharpγ Λ) i0 x = _
      unfold prof
      rw [hs x]
      rfl
    · intro p hp
      have := memLp_gradNorm_iff hw hi (sharpW_i0 i0 i1) (sharpW_i1 i0 i1)
        (fun j h0 h1 => sharpW_rest h0 h1) (sharpγ_gt hΛ) (sharpγ_lt hΛ)
        (ρ := 1 / 2) (by norm_num) hp
      rw [mul_neg_sharpγ_lt_one_iff hΛ] at this
      exact this
  · refine ⟨sharpχ, sharpχ_smooth, sharpχ_compact, sharpχ_tsupport, ⟨1 / 4, by norm_num, ?_⟩,
      sharpF i0 i1 Λ, ?_, sharpF_bound hΛ, sharpU10 hi hΛ, ?_, ?_, ?_⟩
    · intro x hx; exact sharpχ_one hx
    · intro i; exact (measurable_sharpF_apply i0 i1 Λ i).aestronglyMeasurable
    · intro x
      rw [sharpU10_toFun]
      unfold prof
      rw [hs x]
      rfl
    · exact sharp_dirichlet_solution hi hΛ
    · intro p hp hmem
      have hβ : 0 < 2 / (1 - 1 / Real.sqrt Λ) := by
        have h1 : 1 < Real.sqrt Λ := by
          rw [show (1 : ℝ) = Real.sqrt 1 by simp]
          exact Real.sqrt_lt_sqrt zero_le_one hΛ
        have h2 : 0 < 1 - 1 / Real.sqrt Λ := by
          have : 1 / Real.sqrt Λ < 1 := by rw [div_lt_one (by linarith)]; exact h1
          linarith
        positivity
      have hp0 : 0 < p := lt_of_lt_of_le hβ hp
      have hsub : euclideanBall (0 : Vec d) (1 / 4) ⊆ euclideanBall (0 : Vec d) 1 :=
        euclideanBall_mono (by norm_num) (by norm_num)
      have hmem' := hmem.mono_measure (Measure.restrict_mono_set volume hsub)
      have hgrad : MemLp (fun x => vecEuclideanNorm (profGrad (sharpW i0 i1) (sharpγ Λ) i0 x))
          (ENNReal.ofReal p) (volume.restrict (euclideanBall (0 : Vec d) (1 / 4))) := by
        refine hmem'.ae_eq ?_
        refine (ae_restrict_iff' (measurableSet_euclideanBall _ _)).mpr (ae_of_all _ fun x hx => ?_)
        show vecEuclideanNorm ((sharpU10 hi hΛ).toH1Function.grad x) = _
        rw [sharpU10_grad, sharpχ_one hx, classicalGradient_sharpχ_zero hx]
        simp
      have := (memLp_gradNorm_iff hw hi (sharpW_i0 i0 i1) (sharpW_i1 i0 i1)
        (fun j h0 h1 => sharpW_rest h0 h1) (sharpγ_gt hΛ) (sharpγ_lt hΛ)
        (ρ := 1 / 4) (by norm_num) hp0).mp hgrad
      rw [mul_neg_sharpγ_lt_one_iff hΛ] at this
      exact absurd hp (not_le.mpr this)

end PDE.Ch4Meyers
