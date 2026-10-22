module

public import PDEFoundation.Analysis.Inequalities.PoincareAdjustMean.Gt
public import PDEFoundation.Analysis.Inequalities.PoincareAdjustMean.Two

/-!
# The Poincaré inequality with an adjusted mean

Proposition 1.10, unconditional for every `d ≥ 2`.  The case `d > 2` uses the
Sobolev--Poincaré inequality on the ball; the case `d = 2` uses the elementary bound for
`θ ≥ 1/2` and the Trudinger inequality for `θ < 1/2`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.PoincareAdjustMean

open MeasureTheory

/-- The two-dimensional case of the Poincaré inequality with an adjusted mean. -/
theorem exists_poincare_adjustmean_constant_two (d : ℕ) (hd : d = 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, 0 < θ → θ < 1 →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      ∀ E : Set (Vec d), MeasurableSet E → E ⊆ euclideanBall (0 : Vec d) 1 →
        ENNReal.ofReal θ * volume (euclideanBall (0 : Vec d) 1) ≤ volume E →
        eLpNorm (fun x => u.toFun x - integralAverage E u.toFun) 2
            (volumeOn (euclideanBall (0 : Vec d) 1)) ≤
          ENNReal.ofReal (C * (if d = 2 then Real.sqrt (1 + |Real.log θ|)
              else θ ^ (((2 : ℝ) - d) / (2 * d)))) *
            eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2
              (volumeOn (euclideanBall (0 : Vec d) 1)) ∧
        ENNReal.ofReal |integralAverage (euclideanBall (0 : Vec d) 1) u.toFun -
            integralAverage E u.toFun| ≤
          ENNReal.ofReal (C * (if d = 2 then Real.sqrt |Real.log θ|
              else θ ^ (((2 : ℝ) - d) / (2 * d)))) *
            eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2
              (volumeOn (euclideanBall (0 : Vec d) 1)) := by
  subst hd
  obtain ⟨M1, hM1, hb1⟩ := exists_meanDiff_bound_half 2
  obtain ⟨M2, hM2, hb2⟩ := exists_meanDiff_bound_lt_half_two
  set V : ℝ := (volume (euclideanBall (0 : Vec 2) 1)).toReal with hV
  have hVpos : 0 < V := ENNReal.toReal_pos (volume_euclideanBall_pos 0 one_pos).ne'
    (volume_euclideanBall_ne_top 0 zero_le_one)
  refine ⟨(2 : ℝ) ^ 2 * 2 + V ^ (1 / (2 : ℝ)) * (M1 + M2) + (M1 + M2), by positivity,
    fun θ hθ0 hθ1 u E hE hEB hθE => ?_⟩
  simp only [ite_true]
  have hlog : 0 ≤ |Real.log θ| := abs_nonneg _
  have hf₂ : 0 ≤ Real.sqrt |Real.log θ| := Real.sqrt_nonneg _
  have hf₂₁ : Real.sqrt |Real.log θ| ≤ Real.sqrt (1 + |Real.log θ|) :=
    Real.sqrt_le_sqrt (by linarith)
  have hf₁ : 1 ≤ Real.sqrt (1 + |Real.log θ|) := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
  have hb : |integralAverage (euclideanBall (0 : Vec 2) 1) u.toFun - integralAverage E u.toFun| ≤
      (M1 + M2) * Real.sqrt |Real.log θ| *
        (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2
          (volume.restrict (euclideanBall (0 : Vec 2) 1))).toReal := by
    have hg0 : 0 ≤ (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2
        (volume.restrict (euclideanBall (0 : Vec 2) 1))).toReal := ENNReal.toReal_nonneg
    rcases le_or_gt (1 / 2) θ with h | h
    · refine (hb1 θ h hθ1 u E hE hEB hθE).trans ?_
      have : 0 ≤ Real.sqrt |Real.log θ| * (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2
        (volume.restrict (euclideanBall (0 : Vec 2) 1))).toReal := by positivity
      nlinarith
    · refine (hb2 θ hθ0 h u E hE hEB hθE).trans ?_
      have : 0 ≤ Real.sqrt |Real.log θ| * (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2
        (volume.restrict (euclideanBall (0 : Vec 2) 1))).toReal := by positivity
      nlinarith
  obtain ⟨A1, A2⟩ := assemble u (by positivity : 0 ≤ M1 + M2) hf₂ hf₂₁ hf₁ hb
  have hVM : 0 ≤ V ^ (1 / (2 : ℝ)) * (M1 + M2) := by positivity
  have h2d : (0 : ℝ) ≤ (2 : ℝ) ^ 2 * 2 := by positivity
  constructor
  · refine A1.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    nlinarith
  · refine A2.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    nlinarith

/-- Poincaré inequality with the mean over a subset (Proposition 1.10).
Unconditional for every `d ≥ 2`. -/
theorem exists_poincare_adjustmean_constant_full (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, 0 < θ → θ < 1 →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      ∀ E : Set (Vec d), MeasurableSet E → E ⊆ euclideanBall (0 : Vec d) 1 →
        ENNReal.ofReal θ * volume (euclideanBall (0 : Vec d) 1) ≤ volume E →
        eLpNorm (fun x => u.toFun x - integralAverage E u.toFun) 2
            (volumeOn (euclideanBall (0 : Vec d) 1)) ≤
          ENNReal.ofReal (C * (if d = 2 then Real.sqrt (1 + |Real.log θ|)
              else θ ^ (((2 : ℝ) - d) / (2 * d)))) *
            eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2
              (volumeOn (euclideanBall (0 : Vec d) 1)) ∧
        ENNReal.ofReal |integralAverage (euclideanBall (0 : Vec d) 1) u.toFun -
            integralAverage E u.toFun| ≤
          ENNReal.ofReal (C * (if d = 2 then Real.sqrt |Real.log θ|
              else θ ^ (((2 : ℝ) - d) / (2 * d)))) *
            eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2
              (volumeOn (euclideanBall (0 : Vec d) 1)) := by
  rcases eq_or_lt_of_le hd with h | h
  · exact exists_poincare_adjustmean_constant_two d h.symm
  · exact exists_poincare_adjustmean_constant_gt d (by omega)

end PDE.PoincareAdjustMean
