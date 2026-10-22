module

public import PDEFoundation.FunctionalInequalities.SobolevSharpOne.ErosionBasic
public import PDEFoundation.Measure.BallVolume
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The pointwise Brunn--Minkowski step of the erosion argument

For `s > 0`, `μ(s) = |{f ≥ s}|` and `ν_h(s) = |A_s|` (the erosion set), the inclusion
`A_s + B̄_h ⊆ {f ≥ s}`, the Brunn--Minkowski inequality (taken as an explicit hypothesis of the
shape of the statement `PDE.brunn_minkowski`) and Bernoulli's inequality give
`μ(s) - ν_h(s) ≥ d |B_1|^{1/d} h ν_h(s)^{(d-1)/d}`.
All volumes are finite and are stated through `ENNReal.toReal`.
-/

@[expose] public section

open Set MeasureTheory
open scoped Pointwise ENNReal

namespace PDE.SobolevSharp

/-- Bernoulli: `(a + c)^(k+1) ≥ a^(k+1) + (k+1) a^k c` for `a, c ≥ 0`. -/
theorem bernoulli_add_pow {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (k : ℕ) :
    a ^ (k + 1) + (k + 1) * a ^ k * c ≤ (a + c) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hP : 0 ≤ (k + 1) * a ^ k * c * c := by positivity
    have hq : 0 ≤ a + c := add_nonneg ha hc
    calc a ^ (k + 1 + 1) + ((k + 1 : ℕ) + 1) * a ^ (k + 1) * c
        ≤ (a ^ (k + 1) + (k + 1) * a ^ k * c) * (a + c) := by
          have e : (a ^ (k + 1) + (k + 1) * a ^ k * c) * (a + c) =
              a ^ (k + 1 + 1) + (k + 1 + 1) * a ^ (k + 1) * c + (k + 1) * a ^ k * c * c := by
            ring
          push_cast
          linarith [hP, e]
      _ ≤ (a + c) ^ (k + 1) * (a + c) := mul_le_mul_of_nonneg_right ih hq
      _ = (a + c) ^ (k + 1 + 1) := (pow_succ _ _).symm

/-- The real-variable core of the step, with `d = k + 1`. -/
theorem bm_step_real (k : ℕ) {ν b h μ : ℝ} (hν : 0 ≤ ν) (hb : 0 ≤ b) (hh : 0 ≤ h) (hμ : 0 ≤ μ)
    (hbm : ν ^ ((1 : ℝ) / (k + 1 : ℕ)) + h * b ^ ((1 : ℝ) / (k + 1 : ℕ)) ≤
      μ ^ ((1 : ℝ) / (k + 1 : ℕ))) :
    ((k + 1 : ℕ) : ℝ) * b ^ ((1 : ℝ) / (k + 1 : ℕ)) * h *
        ν ^ ((((k + 1 : ℕ) : ℝ) - 1) / (k + 1 : ℕ)) ≤ μ - ν := by
  set a := ν ^ ((1 : ℝ) / (k + 1 : ℕ)) with ha_def
  set c := h * b ^ ((1 : ℝ) / (k + 1 : ℕ)) with hc_def
  set m := μ ^ ((1 : ℝ) / (k + 1 : ℕ)) with hm_def
  have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have ha0 : 0 ≤ a := Real.rpow_nonneg hν _
  have hc0 : 0 ≤ c := mul_nonneg hh (Real.rpow_nonneg hb _)
  have hνa : ν = a ^ (k + 1) := by
    rw [ha_def, one_div, Real.rpow_inv_natCast_pow hν (Nat.succ_ne_zero k)]
  have hμm : μ = m ^ (k + 1) := by
    rw [hm_def, one_div, Real.rpow_inv_natCast_pow hμ (Nat.succ_ne_zero k)]
  have hνk : ν ^ ((((k + 1 : ℕ) : ℝ) - 1) / (k + 1 : ℕ)) = a ^ k := by
    rw [ha_def, ← Real.rpow_natCast, ← Real.rpow_mul hν]
    congr 1
    push_cast
    field_simp
    ring
  rw [hνk]
  have hB := bernoulli_add_pow ha0 hc0 k
  have hm : (a + c) ^ (k + 1) ≤ m ^ (k + 1) :=
    pow_le_pow_left₀ (add_nonneg ha0 hc0) hbm (k + 1)
  have : ((k + 1 : ℕ) : ℝ) * b ^ ((1 : ℝ) / (k + 1 : ℕ)) * h * a ^ k =
      (k + 1) * a ^ k * c := by
    rw [hc_def]; push_cast; ring
  rw [this, hμm]
  linarith [hνa]

section Geometry

variable {d : ℕ}

theorem isCompact_superlevel {f : Vec d → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {s : ℝ} (hs : 0 < s) : IsCompact {x | s ≤ f x} := by
  refine hfc.of_isClosed_subset (isClosed_le continuous_const hf) ?_
  intro x hx
  exact subset_tsupport _ (by
    simp only [Function.mem_support]; exact (lt_of_lt_of_le hs hx).ne')

theorem volume_closedBall_toReal_ge {h : ℝ} (hh : 0 < h) :
    h ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal ≤
      (volume (euclideanClosedBall (0 : Vec d) h)).toReal := by
  rw [← volume_euclideanBall_toReal_eq_unit_mul_of_pos (0 : Vec d) hh]
  exact ENNReal.toReal_mono
    ((isCompact_euclideanClosedBall (0 : Vec d) hh.le).measure_lt_top).ne
    (measure_mono (euclideanBall_subset_euclideanClosedBall _ _))

end Geometry

/-- **Pointwise Brunn--Minkowski step.** The premise `BM` has exactly the shape of the
Brunn--Minkowski statement in dimension `d > 0`. For `A_s` nonempty,
`μ(s) - ν_h(s) ≥ d |B_1|^{1/d} h ν_h(s)^{(d-1)/d}`. -/
theorem bm_step {d : ℕ} (hd : 0 < d)
    (BM : ∀ A B : Set (Vec d), IsCompact A → IsCompact B → A.Nonempty → B.Nonempty →
      volume A ^ ((1 : ℝ) / d) + volume B ^ ((1 : ℝ) / d) ≤ volume (A + B) ^ ((1 : ℝ) / d))
    {f : Vec d → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) {h s : ℝ}
    (hh : 0 < h) (hs : 0 < s) (hne : (erosionSet f h s).Nonempty) :
    (d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal ^ ((1 : ℝ) / d) * h *
        (volume (erosionSet f h s)).toReal ^ (((d : ℝ) - 1) / d) ≤
      (volume {x | s ≤ f x}).toReal - (volume (erosionSet f h s)).toReal := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  set A := erosionSet f h s with hA
  set B := euclideanClosedBall (0 : Vec (k + 1)) h with hB
  have hAc : IsCompact A := isCompact_erosionSet hf hfc hh.le hs
  have hBc : IsCompact B := isCompact_euclideanClosedBall _ hh.le
  have hBne : B.Nonempty := ⟨0, zero_mem_euclideanClosedBall_zero hh.le⟩
  have hSc := isCompact_superlevel hf hfc hs
  have hsub : A + B ⊆ {x | s ≤ f x} := erosionSet_add_subset hh.le
  have hmeas : volume (A + B) ≤ volume {x | s ≤ f x} := measure_mono hsub
  have hbm := BM A B hAc hBc hne hBne
  have hA_top : volume A ≠ ⊤ := hAc.measure_lt_top.ne
  have hB_top : volume B ≠ ⊤ := hBc.measure_lt_top.ne
  have hS_top : volume {x | s ≤ f x} ≠ ⊤ := hSc.measure_lt_top.ne
  have hp : (0 : ℝ) ≤ (1 : ℝ) / ((k + 1 : ℕ) : ℝ) := by positivity
  have hbm' := hbm.trans (ENNReal.rpow_le_rpow hmeas hp)
  have hreal := ENNReal.toReal_mono
    (ENNReal.rpow_ne_top_of_nonneg hp hS_top) hbm'
  rw [ENNReal.toReal_add (ENNReal.rpow_ne_top_of_nonneg hp hA_top)
    (ENNReal.rpow_ne_top_of_nonneg hp hB_top), ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
    ← ENNReal.toReal_rpow] at hreal
  have hball : (volume (euclideanBall (0 : Vec (k + 1)) 1)).toReal * h ^ (k + 1) ≤
      (volume B).toReal := by
    rw [mul_comm]; exact volume_closedBall_toReal_ge hh
  have hb0 : 0 ≤ (volume (euclideanBall (0 : Vec (k + 1)) 1)).toReal := ENNReal.toReal_nonneg
  have hBpow : h * (volume (euclideanBall (0 : Vec (k + 1)) 1)).toReal ^ ((1 : ℝ) / ((k + 1 : ℕ) : ℝ))
      ≤ (volume B).toReal ^ ((1 : ℝ) / ((k + 1 : ℕ) : ℝ)) := by
    have h1 := Real.rpow_le_rpow (by positivity) hball hp
    rw [Real.mul_rpow hb0 (by positivity), one_div, Real.pow_rpow_inv_natCast hh.le
      (Nat.succ_ne_zero k), mul_comm] at h1
    simpa [one_div] using h1
  have hbm'' : (volume A).toReal ^ ((1 : ℝ) / ((k + 1 : ℕ) : ℝ)) +
      h * (volume (euclideanBall (0 : Vec (k + 1)) 1)).toReal ^ ((1 : ℝ) / ((k + 1 : ℕ) : ℝ)) ≤
      (volume {x | s ≤ f x}).toReal ^ ((1 : ℝ) / ((k + 1 : ℕ) : ℝ)) := by
    linarith [hreal, hBpow]
  exact bm_step_real k ENNReal.toReal_nonneg hb0 hh.le ENNReal.toReal_nonneg hbm''

/-- For `d ≥ 2` no nonemptiness hypothesis is needed. -/
theorem bm_step_of_two_le {d : ℕ} (hd : 2 ≤ d)
    (BM : ∀ A B : Set (Vec d), IsCompact A → IsCompact B → A.Nonempty → B.Nonempty →
      volume A ^ ((1 : ℝ) / d) + volume B ^ ((1 : ℝ) / d) ≤ volume (A + B) ^ ((1 : ℝ) / d))
    {f : Vec d → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) {h s : ℝ}
    (hh : 0 < h) (hs : 0 < s) :
    (d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal ^ ((1 : ℝ) / d) * h *
        (volume (erosionSet f h s)).toReal ^ (((d : ℝ) - 1) / d) ≤
      (volume {x | s ≤ f x}).toReal - (volume (erosionSet f h s)).toReal := by
  by_cases hne : (erosionSet f h s).Nonempty
  · exact bm_step (by omega) BM hf hfc hh hs hne
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    have hd' : (1 : ℝ) < d := by exact_mod_cast hd
    have hexp : 0 < ((d : ℝ) - 1) / d := div_pos (by linarith) (by linarith)
    simp only [measure_empty, ENNReal.toReal_zero, Real.zero_rpow hexp.ne', mul_zero, sub_zero]
    exact ENNReal.toReal_nonneg

end PDE.SobolevSharp
