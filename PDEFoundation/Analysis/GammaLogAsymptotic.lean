module

public import PDEFoundation.Analysis.FactorialRootAsymptotic
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Logarithmic asymptotics of the real Gamma function
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace PDE

private noncomputable def gammaFloorEndpoint (k : ℕ) (p : ℝ) : ℝ :=
  let m := ⌊p⌋₊ + k
  Real.log (m.factorial : ℝ) / p - Real.log p

private theorem tendsto_floor_ratio_add (k : ℕ) :
    Tendsto (fun p : ℝ => ((⌊p⌋₊ + k : ℕ) : ℝ) / p)
      atTop (𝓝 1) := by
  have hk : Tendsto (fun p : ℝ => (k : ℝ) / p) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h := tendsto_nat_floor_div_atTop.add hk
  convert h using 1
  · funext p
    push_cast
    ring_nf
  · ring_nf

private theorem tendsto_floor_log_error (k : ℕ) (hk : k ≤ 1) :
    Tendsto (fun p : ℝ =>
      ((((⌊p⌋₊ + k : ℕ) : ℝ) / p) - 1) * Real.log p)
      atTop (𝓝 0) := by
  have hkCases : k = 0 ∨ k = 1 := by omega
  have hlog : Tendsto (fun p : ℝ => Real.log p / p) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (g := fun p : ℝ => Real.log p / p)
  · filter_upwards with p
    exact norm_nonneg _
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with p hp
    have hp0 : 0 < p := by linarith
    have hfloor : ((⌊p⌋₊ : ℕ) : ℝ) ≤ p := Nat.floor_le hp0.le
    have hlt : p < ((⌊p⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one p
    have hmLower : -1 ≤ (((⌊p⌋₊ + k : ℕ) : ℝ) - p) := by
      rcases hkCases with rfl | rfl
      · push_cast
        linarith
      · push_cast
        linarith
    have hmUpper : (((⌊p⌋₊ + k : ℕ) : ℝ) - p) ≤ 1 := by
      rcases hkCases with rfl | rfl
      · push_cast
        linarith
      · push_cast
        linarith
    have habs : |(((⌊p⌋₊ + k : ℕ) : ℝ) - p)| ≤ 1 :=
      abs_le.2 ⟨hmLower, hmUpper⟩
    have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    rw [Real.norm_eq_abs, abs_mul, show (((((⌊p⌋₊ + k : ℕ) : ℝ) / p) - 1)) =
      ((((⌊p⌋₊ + k : ℕ) : ℝ) - p) / p) by field_simp]
    rw [abs_div, abs_of_pos hp0, abs_of_nonneg hlog0]
    calc
      |(((⌊p⌋₊ + k : ℕ) : ℝ) - p)| / p * Real.log p ≤
          1 / p * Real.log p :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right habs hp0.le) hlog0
      _ = Real.log p / p := by field_simp
  · exact hlog

private theorem tendsto_gammaFloorEndpoint (k : ℕ) (hk : k ≤ 1) :
    Tendsto (gammaFloorEndpoint k) atTop (𝓝 (-1)) := by
  let m : ℝ → ℕ := fun p => ⌊p⌋₊ + k
  have hmTop : Tendsto m atTop atTop :=
    (tendsto_add_atTop_nat k).comp tendsto_nat_floor_atTop
  have hA := tendsto_log_factorial_div_sub_log.comp hmTop
  have hr : Tendsto (fun p : ℝ => ((m p : ℕ) : ℝ) / p)
      atTop (𝓝 1) := by
    simpa only [m] using tendsto_floor_ratio_add k
  have hfirst : Tendsto (fun p : ℝ =>
      (((m p : ℕ) : ℝ) / p) *
        (Real.log ((m p).factorial : ℝ) / (m p : ℝ) -
          Real.log (m p : ℝ))) atTop (𝓝 (-1)) := by
    convert hr.mul hA using 1 <;> norm_num
  have hmiddle : Tendsto (fun p : ℝ =>
      ((((m p : ℕ) : ℝ) / p) - 1) * Real.log p) atTop (𝓝 0) := by
    simpa only [m] using tendsto_floor_log_error k hk
  have hlogRatio : Tendsto (fun p : ℝ =>
      Real.log (((m p : ℕ) : ℝ) / p)) atTop (𝓝 0) := by
    simpa using hr.log one_ne_zero
  have hthird : Tendsto (fun p : ℝ =>
      (((m p : ℕ) : ℝ) / p) * Real.log (((m p : ℕ) : ℝ) / p))
      atTop (𝓝 0) := by
    simpa using hr.mul hlogRatio
  have hsum : Tendsto (fun p =>
      (((m p : ℕ) : ℝ) / p) *
          (Real.log ((m p).factorial : ℝ) / (m p : ℝ) - Real.log (m p : ℝ)) +
        ((((m p : ℕ) : ℝ) / p) - 1) * Real.log p +
        (((m p : ℕ) : ℝ) / p) * Real.log (((m p : ℕ) : ℝ) / p))
      atTop (𝓝 (-1)) := by
    simpa only [add_zero] using (hfirst.add hmiddle).add hthird
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with p hp
  have hp0 : p ≠ 0 := by linarith
  have hmpos : 0 < m p := by
    dsimp only [m]
    have : 1 ≤ ⌊p⌋₊ := by
      apply Nat.le_floor
      norm_num
      linarith
    omega
  have hmR : (0 : ℝ) < m p := by exact_mod_cast hmpos
  have hmR' : (0 : ℝ) < ((⌊p⌋₊ + k : ℕ) : ℝ) := by simpa only [m] using hmR
  dsimp only [gammaFloorEndpoint, m]
  rw [Real.log_div hmR.ne' hp0]
  field_simp [hmR'.ne']
  simp only [m]
  ring_nf

/-- The logarithmic Stirling asymptotic for the real Gamma function. -/
theorem tendsto_log_Gamma_add_one_div_sub_log :
    Tendsto (fun p : ℝ =>
      Real.log (Real.Gamma (p + 1)) / p - Real.log p)
      atTop (𝓝 (-1)) := by
  have hlo := tendsto_gammaFloorEndpoint 0 (by norm_num)
  have hhi := tendsto_gammaFloorEndpoint 1 (by norm_num)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with p hp
    have hp0 : 0 < p := by linarith
    let n := ⌊p⌋₊
    have hnNat : (2 : ℕ) ≤ n := by
      apply Nat.le_floor
      norm_num
      exact hp
    have hn : (2 : ℝ) ≤ n := by exact_mod_cast hnNat
    have hnp : (n : ℝ) ≤ p := Nat.floor_le hp0.le
    have hmono : Real.Gamma ((n : ℝ) + 1) ≤ Real.Gamma (p + 1) :=
      Real.Gamma_strictMonoOn_Ici.monotoneOn
        (by simp only [mem_Ici]; linarith)
        (by simp only [mem_Ici]; linarith) (by linarith)
    rw [show Real.Gamma ((n : ℝ) + 1) = (n.factorial : ℝ) by
      simpa using Real.Gamma_nat_eq_factorial n] at hmono
    dsimp only [gammaFloorEndpoint]
    simp only [Nat.add_zero]
    exact sub_le_sub_right
      (div_le_div_of_nonneg_right
        (Real.log_le_log (by positivity) hmono) hp0.le) _
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with p hp
    have hp0 : 0 < p := by linarith
    let n := ⌊p⌋₊
    have hnNat : (2 : ℕ) ≤ n := by
      apply Nat.le_floor
      norm_num
      exact hp
    have hn : (2 : ℝ) ≤ n := by exact_mod_cast hnNat
    have hpSucc : p + 1 ≤ ((n + 1 : ℕ) : ℝ) + 1 := by
      have := Nat.lt_floor_add_one p
      push_cast at this ⊢
      linarith
    have hmono : Real.Gamma (p + 1) ≤ Real.Gamma (((n + 1 : ℕ) : ℝ) + 1) :=
      Real.Gamma_strictMonoOn_Ici.monotoneOn
        (by simp only [mem_Ici]; linarith)
        (by simp only [mem_Ici]; push_cast; linarith) hpSucc
    rw [show Real.Gamma (((n + 1 : ℕ) : ℝ) + 1) =
      ((n + 1).factorial : ℝ) by
        simpa using Real.Gamma_nat_eq_factorial (n + 1)] at hmono
    dsimp only [gammaFloorEndpoint]
    exact sub_le_sub_right
      (div_le_div_of_nonneg_right
        (Real.log_le_log (Real.Gamma_pos_of_pos (by linarith)) hmono) hp0.le) _

end PDE
