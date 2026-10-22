module

public import PDEFoundation.Analysis.BackwardGeometricIteration
public import PDEFoundation.Analysis.CalderonZygmundIterationRadii

/-! # Backward iteration along Calderón--Zygmund radii -/

@[expose] public section

namespace PDE

/-- A backward estimate between arbitrary radii closes along the literal
Calderón--Zygmund radius sequence. The recurrence and boundedness of the
quantity remain explicit hypotheses. -/
theorem calderonZygmundRadiusIteration_bound
    {d : ℕ} (hd : 0 < d) (Φ : ℝ → ℝ) {A B η M : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hη0 : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hbound : ∀ r, 1 / 2 ≤ r → r < 3 / 4 → Φ r ≤ M)
    (hrec : ∀ s t, 1 / 2 ≤ s → s < t → t < 3 / 4 →
      Φ s ≤ A * (t - s) ^ (-(d : ℝ) / 2) + B + η * Φ t) :
    Φ (1 / 2) ≤
      A * (4 / (1 - calderonZygmundIterationSigma d)) ^ ((d : ℝ) / 2) /
          (1 - Real.sqrt 2 / 2) +
        2 * B := by
  let r : ℕ → ℝ := calderonZygmundIterationRadius d
  let K := (4 / (1 - calderonZygmundIterationSigma d)) ^ ((d : ℝ) / 2)
  have hrange (j : ℕ) : 1 / 2 ≤ r j ∧ r j < 3 / 4 := by
    exact calderonZygmundIterationRadius_mem hd
  have hboundSeq (j : ℕ) : Φ (r j) ≤ M :=
    hbound (r j) (hrange j).1 (hrange j).2
  have hrecSeq (j : ℕ) :
      Φ (r j) ≤ (A * K) * (Real.sqrt 2) ^ j + B + η * Φ (r (j + 1)) := by
    have hj := hrec (r j) (r (j + 1)) (hrange j).1
      (calderonZygmundIterationRadius_strictMono hd) (hrange (j + 1)).2
    rw [calderonZygmundIterationRadius_gap_rpow hd] at hj
    dsimp only [r, K]
    nlinarith only [hj]
  have hK : 0 ≤ K := by
    have hs : calderonZygmundIterationSigma d < 1 :=
      calderonZygmundIterationSigma_lt_one hd
    dsimp only [K]
    exact Real.rpow_nonneg (div_nonneg (by norm_num) (sub_pos.mpr hs).le) _
  have hiter := backwardSqrtTwoIteration_bound
    (φ := fun j => Φ (r j)) (A := A * K) (B := B) (η := η) (M := M)
    (mul_nonneg hA hK) hB hη0 hηhalf hboundSeq hrecSeq
  simpa only [r, calderonZygmundIterationRadius_zero, K] using hiter

end PDE
