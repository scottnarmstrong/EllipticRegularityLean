module

public import EllipticRegularity.DeGiorgi.Assembly.Statements

/-!
# Real bookkeeping for the local Harnack inequality
-/

@[expose] public section

namespace PDE.DGNMAssembly

theorem log_le_two_sqrt {Λ : ℝ} (hΛ : 1 ≤ Λ) : Real.log Λ ≤ 2 * Real.sqrt Λ := by
  have hΛ0 : 0 < Λ := by linarith
  have hs : 0 < Real.sqrt Λ := Real.sqrt_pos.2 hΛ0
  have h1 := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hΛ0.le] at h1
  linarith

theorem harnack_real_bound {a1 B p Λ dR : ℝ} (ha1 : 0 < a1) (hB : 0 < B) (hp : 1 ≤ p)
    (hΛ : 1 ≤ Λ) (hdR : 0 ≤ dR) :
    (a1 * Λ ^ (dR / 2)) ^ (1 / p) * B ^ Real.sqrt Λ ≤
      Real.exp ((|Real.log a1| + dR + |Real.log B|) * Real.sqrt Λ) := by
  have hΛ0 : 0 < Λ := by linarith
  have hs1 : 1 ≤ Real.sqrt Λ := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hΛ
  have hp0 : 0 < p := by linarith
  have hlog := log_le_two_sqrt hΛ
  have hlogΛ : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos hB, ← Real.exp_add,
    Real.log_mul ha1.ne' (Real.rpow_pos_of_pos hΛ0 _).ne', Real.log_rpow hΛ0]
  apply Real.exp_le_exp.2
  have h1 : (Real.log a1 + dR / 2 * Real.log Λ) * (1 / p) ≤
      |Real.log a1| + dR / 2 * Real.log Λ := by
    have hnn : 0 ≤ dR / 2 * Real.log Λ := by positivity
    have hle : Real.log a1 + dR / 2 * Real.log Λ ≤ |Real.log a1| + dR / 2 * Real.log Λ := by
      linarith [le_abs_self (Real.log a1)]
    have hnn2 : 0 ≤ |Real.log a1| + dR / 2 * Real.log Λ := by positivity
    calc (Real.log a1 + dR / 2 * Real.log Λ) * (1 / p)
        ≤ (|Real.log a1| + dR / 2 * Real.log Λ) * (1 / p) :=
          mul_le_mul_of_nonneg_right hle (by positivity)
      _ ≤ (|Real.log a1| + dR / 2 * Real.log Λ) * 1 := by
          apply mul_le_mul_of_nonneg_left _ hnn2
          rw [div_le_one hp0]; exact hp
      _ = _ := mul_one _
  have h2 : Real.log B * Real.sqrt Λ ≤ |Real.log B| * Real.sqrt Λ :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
  have h3 : |Real.log a1| ≤ |Real.log a1| * Real.sqrt Λ := by
    nlinarith [abs_nonneg (Real.log a1)]
  have h4 : dR / 2 * Real.log Λ ≤ dR * Real.sqrt Λ := by nlinarith
  nlinarith

end PDE.DGNMAssembly
