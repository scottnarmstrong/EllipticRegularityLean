module

public import BSlocalmax.HighDim
public import BSlocalmax.TwoDim
public import BSlocalmax.ThreeDim

/-!
# Sharp `L^∞`–`L²` estimate for subsolutions on cubes, all dimensions `d ≥ 2`

Setting: `Q_r = Metric.ball 0 r` (sup norm), `a` measurable with `IsEllipticMatrix 1 Λ (a x)` (`|ξ|² ≤ ξ·a(x)ξ`, `Λ⁻¹|ξ|² ≤ ξ·a(x)⁻¹ξ`),
`u ∈ H¹(Q_1)` a weak subsolution of `-div (a ∇u) ≤ 0`.  Then
`ess sup_{Q_{1/2}} u₊ ≤ C (ℓ(Λ) Λ)^{(d-1)/4} ‖u‖_{L²(Q_1)}`, where `ℓ(s) = log(e+s)` if `d = 3`
and `ℓ(s) = 1` otherwise.  That is

* `d = 2`:  `C Λ^{1/4}`,
* `d = 3`:  `C Λ^{1/2} log(e+Λ)^{1/2}`,
* `d ≥ 4`:  `C Λ^{(d-1)/4}`.
-/

@[expose] public section

namespace PDE.BSlocalmax

open MeasureTheory PDE PDE.Ch4Infra

/-- The logarithmic loss `ℓ(s) = log(e+s)` if `d = 3`, and `ℓ(s) = 1` otherwise. -/
noncomputable def ell (d : ℕ) (s : ℝ) : ℝ :=
  if d = 3 then Real.log (Real.exp 1 + s) else 1

set_option maxHeartbeats 1600000 in
/-- **Sharp `L^∞` estimate for subsolutions on cubes, `d ≥ 2`.** -/
theorem exists_sharpLocalMax_constant (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (Metric.ball (0 : Vec d) 1))) →
      (∀ x ∈ Metric.ball (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (Metric.ball (0 : Vec d) 1),
      IsWeakDivergenceFormSubharmonicOn a (Metric.ball (0 : Vec d) 1) u →
        essSup (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (Metric.ball (0 : Vec d) (1 / 2))) ≤
          ENNReal.ofReal (C * (ell d Λ * Λ) ^ (((d : ℝ) - 1) / 4)) *
            eLpNorm u.toFun 2 (volumeOn (Metric.ball (0 : Vec d) 1)) := by
  rcases Nat.lt_or_ge d 4 with h4 | h4
  · have h23 : d = 2 ∨ d = 3 := by omega
    rcases h23 with rfl | rfl
    · obtain ⟨C, hC, h⟩ := exists_sharpLocalMax_constant_cube_two
      refine ⟨C, hC, fun Λ a ha hEll u hsub => ?_⟩
      have key : C * (ell 2 Λ * Λ) ^ ((((2 : ℕ) : ℝ) - 1) / 4) = C * Λ ^ ((1 : ℝ) / 4) := by
        simp only [ell, if_neg (by norm_num : (2 : ℕ) ≠ 3), one_mul]
        norm_num
      rw [key]
      exact h Λ a ha hEll u hsub
    · obtain ⟨C, hC, h⟩ := exists_sharpLocalMax_constant_cube_three_log
      refine ⟨C, hC, fun Λ a ha hEll u hsub => ?_⟩
      have hΛ : 1 ≤ Λ := (hEll 0 (Metric.mem_ball_self one_pos)).lam_le_Lam
      have hL : 0 ≤ Real.log (Real.exp 1 + Λ) :=
        Real.log_nonneg (by linarith [Real.add_one_le_exp (1 : ℝ)])
      have key : C * (ell 3 Λ * Λ) ^ ((((3 : ℕ) : ℝ) - 1) / 4) =
          C * Λ ^ (1 / 2 : ℝ) * (Real.log (Real.exp 1 + Λ)) ^ (1 / 2 : ℝ) := by
        simp only [ell, if_true]
        have : (((3 : ℕ) : ℝ) - 1) / 4 = 1 / 2 := by norm_num
        rw [this, Real.mul_rpow hL (by linarith)]
        ring
      rw [key]
      exact h Λ a ha hEll u hsub
  · obtain ⟨C, hC, h⟩ := exists_sharpLocalMax_constant_cube d h4
    refine ⟨C, hC, fun Λ a ha hEll u hsub => ?_⟩
    have h3 : d ≠ 3 := by omega
    simp only [ell, if_neg h3, one_mul]
    exact h Λ a ha hEll u hsub

end PDE.BSlocalmax
