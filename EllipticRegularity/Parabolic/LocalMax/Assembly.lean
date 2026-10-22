module

public import EllipticRegularity.Parabolic.LocalMax.PowerStep
public import EllipticRegularity.Parabolic.LocalMax.SliceTransfer

/-!
# Conditional assembly of the parabolic Harnack inequality (Corollary 5.14)

`PDE.Ch5LocalHarnackAssembly.of_weakHarnack` proves the exact type of the statement
`PDE.parabLocalHarnack` from a hypothesis whose type is, verbatim, the type of the statement
`PDE.parabWeakHarnack`.  It uses the weak Harnack inequality with `q = (d+1)/(d+2)` (so that
`q(d+2)/d = (d+1)/d`), the parabolic local maximum estimate
(`PDE.Parabolic.LocalMax.parabolic_local_max_of_powerStep` with `power_step`), and the rescaling
and slice transfer `PDE.Parabolic.LocalMax.localHarnack_of_unitHarnack`.

This is a conditional result: it takes the weak Harnack inequality as a hypothesis.  Applied to
`PDE.parabWeakHarnack` it gives the local Harnack inequality (`PDE.parabLocalHarnack`).
-/

@[expose] public section

namespace PDE.Ch5LocalHarnackAssembly

open MeasureTheory Set

/-- A weak solution is a weak supersolution. -/
theorem isParabolicWeakSupersolution_of_solution {d : ℕ} {a : ParCoeffField d}
    {U : Set (Vec d)} {I : Set ℝ} {u : ParH1Function U I}
    (hu : IsParabolicWeakSolution a U I u) : IsParabolicWeakSupersolution a U I u :=
  fun φ _ => ⟨(hu φ).1, (hu φ).2.ge⟩

/-- **Conditional assembly.** The hypothesis is the type of `PDE.parabWeakHarnack`; the
conclusion is the type of `PDE.parabLocalHarnack`. -/
theorem of_weakHarnack
    (hWH : ∀ (d : ℕ), 0 < d → ∀ (Lam : ℝ), 1 ≤ Lam → ∀ (q : ℝ), 0 < q → q < 1 →
          ∃ C : ℝ, 0 < C ∧ ∀ (a : ParCoeffField d),
            IsParabolicCoeff 1 Lam a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
            ∀ u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
            IsParabolicWeakSupersolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u →
            (∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
              0 ≤ u.toFun z) →
              ((volume (euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioo (-3 / 4 : ℝ) (-1 / 2)))⁻¹ *
                  ∫⁻ z in euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioo (-3 / 4 : ℝ) (-1 / 2),
                    ENNReal.ofReal (u.toFun z) ^ (q * ((d : ℝ) + 2) / d)) ^ (1 / (q * ((d : ℝ) + 2) / d))
                ≤ ENNReal.ofReal C *
                  essInf (fun z => ENNReal.ofReal (u.toFun z))
                    (volume.restrict (euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioc (-1 / 4 : ℝ) 0))) :
    ∀ (d : ℕ), 0 < d → ∀ (Lam : ℝ), 1 ≤ Lam →
      ∃ H : ℝ, 2 ≤ H ∧ ∀ (a : ParCoeffField d) (τ θ : ℝ), 0 < θ → ∀ z z' : Vec d,
        euclideanSqDist z z' ≤ θ / 4 →
        IsParabolicCoeff 1 Lam a
          (euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ)))
          (Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4)) →
        ∀ u : ParH1Function (euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ)))
          (Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4)),
        IsParabolicWeakSolution a (euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ)))
          (Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4)) u →
        (∀ᵐ w ∂(volume.restrict (euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ)) ×ˢ
          Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4))), 0 ≤ u.toFun w) →
          essSup (fun x : Vec d => ENNReal.ofReal (u.toFun (x, τ)))
              (volume.restrict (euclideanBall z (Real.sqrt θ / 4))) ≤
            ENNReal.ofReal H *
              essInf (fun x : Vec d => ENNReal.ofReal (u.toFun (x, τ + θ)))
                (volume.restrict (euclideanBall z' (Real.sqrt θ / 4))) := by
  intro d hd Lam hLam
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set q : ℝ := ((d : ℝ) + 1) / ((d : ℝ) + 2) with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one (by positivity)]; linarith
  obtain ⟨CL, hCL, hLM⟩ := PDE.Parabolic.LocalMax.parabolic_local_max d hd Lam hLam q hq
  obtain ⟨CW, hCW, hWHq⟩ := hWH d hd Lam hLam q hq0 hq1
  refine ⟨max 2 (CL * CW), le_max_left _ _, ?_⟩
  refine PDE.Parabolic.LocalMax.localHarnack_of_unitHarnack d Lam (max 2 (CL * CW))
    (le_trans zero_le_two (le_max_left _ _)) ?_
  intro ã hã ũ hũ hpos
  calc essSup (fun w => ENNReal.ofReal (ũ.toFun w))
        (volume.restrict (euclideanBall (0 : Vec d) (3 / 8) ×ˢ Ioo (-11 / 16 : ℝ) (-1 / 2)))
      ≤ ENNReal.ofReal CL *
          ((volume (euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioo (-3 / 4 : ℝ) (-1 / 2)))⁻¹ *
            ∫⁻ z in euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioo (-3 / 4 : ℝ) (-1 / 2),
              ENNReal.ofReal (ũ.toFun z) ^ (q * ((d : ℝ) + 2) / d)) ^
            (1 / (q * ((d : ℝ) + 2) / d)) := hLM ã hã ũ hũ hpos
    _ ≤ ENNReal.ofReal CL * (ENNReal.ofReal CW * essInf (fun w => ENNReal.ofReal (ũ.toFun w))
          (volume.restrict (euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioc (-1 / 4 : ℝ) 0))) := by
        gcongr
        exact hWHq ã hã ũ (isParabolicWeakSupersolution_of_solution hũ) hpos
    _ = ENNReal.ofReal (CL * CW) * essInf (fun w => ENNReal.ofReal (ũ.toFun w))
          (volume.restrict (euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioc (-1 / 4 : ℝ) 0)) := by
        rw [ENNReal.ofReal_mul hCL.le, mul_assoc]
    _ ≤ _ := by
        gcongr
        exact le_max_right _ _

end PDE.Ch5LocalHarnackAssembly
