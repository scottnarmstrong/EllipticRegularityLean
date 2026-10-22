module

public import EllipticRegularity.Ch4.Meyers.RangeBound

/-!
# Consequence of Proposition 4.7 for the Dirichlet Meyers estimate

The theorem `meyers_range_upper_bound_dirichlet_full` has exactly the type of the statement
`meyers_range_upper_bound_dirichlet`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4Meyers

open MeasureTheory Set

/-- For `c > 2` there is `Λ > 1` with `p⋆(Λ) ≤ 2 + c/√Λ`. -/
theorem exists_lambda_of_two_lt {c : ℝ} (hc2 : 2 < c) :
    ∃ Λ : ℝ, 1 < Λ ∧ 2 / (1 - 1 / Real.sqrt Λ) ≤ 2 + c / Real.sqrt Λ := by
  set m : ℝ := c / (c - 2) + 1 with hmdef
  have hc20 : 0 < c - 2 := by linarith
  have hm1 : 1 < m := by
    have : 0 < c / (c - 2) := by positivity
    linarith
  have hm0 : 0 < m := by linarith
  refine ⟨m ^ 2, by nlinarith, ?_⟩
  have hsq : Real.sqrt (m ^ 2) = m := Real.sqrt_sq hm0.le
  rw [hsq]
  have h1 : 0 < 1 - 1 / m := by
    have : 1 / m < 1 := by rw [div_lt_one hm0]; exact hm1
    linarith
  rw [div_le_iff₀ h1]
  have hcm : c / (c - 2) * (c - 2) = c := div_mul_cancel₀ c hc20.ne'
  have key : c ≤ (c - 2) * m := by
    have : (c - 2) * m = c + (c - 2) := by
      rw [hmdef]; nlinarith [hcm]
    linarith
  field_simp
  nlinarith

/-- Consequence of Proposition 4.7 for the Dirichlet estimate of Theorem 4.4(ii). -/
theorem meyers_range_upper_bound_dirichlet_full (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c)
    (h : ∀ Λ : ℝ, 1 < Λ → ∃ C : ℝ, 0 < C ∧ ∀ a : CoeffField d,
      (∀ i j : Fin d,
        AEMeasurable (fun x => a x i j)
          (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ p : ℝ, (2 + c / Real.sqrt Λ) / (1 + c / Real.sqrt Λ) ≤ p →
        p ≤ 2 + c / Real.sqrt Λ →
        ∀ f : Vec d → Vec d,
        (∀ i : Fin d,
          AEStronglyMeasurable (fun x => f x i)
            (volumeOn (euclideanBall (0 : Vec d) 1))) →
        MemLp (fun x => vecEuclideanNorm (f x)) 2
          (volumeOn (euclideanBall (0 : Vec d) 1)) →
        MemLp (fun x => vecEuclideanNorm (f x)) (ENNReal.ofReal p)
          (volumeOn (euclideanBall (0 : Vec d) 1)) →
        ∀ u : H10Function (euclideanBall (0 : Vec d) 1),
        IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1)
            u.toH1Function (0 : Vec d → ℝ) f →
          eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
              (volumeOn (euclideanBall (0 : Vec d) 1)) ≤
            ENNReal.ofReal C *
              eLpNorm (fun x => vecEuclideanNorm (f x)) (ENNReal.ofReal p)
                (volumeOn (euclideanBall (0 : Vec d) 1))) :
    c ≤ 2
:= by
  by_contra hc2
  push Not at hc2
  obtain ⟨Λ, hΛ, hpstar⟩ := exists_lambda_of_two_lt hc2
  obtain ⟨C, hCpos, hC⟩ := h Λ hΛ
  have hq : 0 < Real.sqrt Λ := Real.sqrt_pos.mpr (by linarith)
  set t : ℝ := c / Real.sqrt Λ with ht
  have ht0 : 0 < t := by positivity
  obtain ⟨a, -, hmeas, hell, -, -, χ, -, -, -, -, f, hfmeas, ⟨M, hM⟩, U, -, hUsol, hnot⟩ :=
    meyers_sharpness_example_full d hd Λ hΛ
  have hlow : (2 + t) / (1 + t) ≤ 2 + t := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hfmeasN : AEStronglyMeasurable (fun x => vecEuclideanNorm (f x))
      (volumeOn (euclideanBall (0 : Vec d) 1)) :=
    (continuous_vecEuclideanNorm.measurable.comp_aemeasurable
      (aemeasurable_pi_iff.mpr fun i => (hfmeas i).aemeasurable)).aestronglyMeasurable
  have hfp : ∀ q : ℝ≥0∞, MemLp (fun x => vecEuclideanNorm (f x)) q
      (volumeOn (euclideanBall (0 : Vec d) 1)) := by
    intro q
    have := isFiniteMeasure_restrict_unitBall (d := d)
    refine MemLp.of_bound hfmeasN M ?_
    refine (ae_restrict_iff' (measurableSet_euclideanBall _ _)).mpr (ae_of_all _ fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _)]
    exact hM x hx
  have hmain := hC a hmeas (fun x _ => hell x) (2 + t) hlow le_rfl f hfmeas (hfp 2)
    (hfp _) U hUsol
  have hlt : eLpNorm (fun x => vecEuclideanNorm (U.grad x)) (ENNReal.ofReal (2 + t))
      (volumeOn (euclideanBall (0 : Vec d) 1)) < ∞ :=
    lt_of_le_of_lt hmain (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfp _))
  exact hnot (2 + t) hpstar hlt

end PDE.Ch4Meyers
