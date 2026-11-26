module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import BSlocalmax.FreeExponent
public import BSlocalmax.Trudinger

/-!
# The case d = 3

This file collects the following pieces, in dependency order: FinalAux1, FinalAux2, FinalD3, FinalD3Log.
-/

-- ==== from FinalAux1.lean ====
-- Elementary bounds in `κ ∈ (0,1]` for the `d = 3` statement.


@[expose] public section

namespace PDE.BSlocalmax

/-- `iterConst` is uniformly bounded for `γ - 1 = 1/κ`, `α = 1 + 1/(2κ)`, `θ = 2/3`, `b = 2`. -/
theorem iterConst_le {γ θ α b κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hγ : γ - 1 = 1 / κ)
    (hα : α = 1 + 1 / (2 * κ)) (hθ : θ = 2 / 3) (hb : b = 2) : iterConst γ θ α b ≤ 2049 := by
  have h1 : α / (γ - 1) = κ + 1 / 2 := by
    rw [hγ, hα]; field_simp
  have h2 : 1 / (γ - 1) = κ := by rw [hγ]; field_simp
  have hθ' : 1 / θ = 3 / 2 := by rw [hθ]; norm_num
  unfold iterConst
  rw [h1, h2, hθ', hb]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (2 : ℝ) ^ (κ + 1 / 2) := ⟨_, rfl⟩
  rw [← hρ]
  have hρ1 : 1 ≤ ρ := by
    rw [hρ]; exact Real.one_le_rpow (by norm_num) (by linarith)
  have hρ4 : ρ ≤ 4 := by
    rw [hρ]
    calc (2 : ℝ) ^ (κ + 1 / 2) ≤ (2 : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := by norm_num
  have e1 : (2 : ℝ) / (1 / (2 * ρ)) = 4 * ρ := by field_simp; ring
  have e2 : (2 * 2 : ℝ) / (1 / (2 * ρ)) = 8 * ρ := by field_simp; ring
  rw [e1, e2]
  have hK1 : (4 * ρ) ^ κ * ρ ^ 2 ≤ 1024 := by
    have a1 : (4 * ρ) ^ κ ≤ 4 * ρ := by
      calc (4 * ρ) ^ κ ≤ (4 * ρ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) hκ1
        _ = 4 * ρ := Real.rpow_one _
    nlinarith [mul_le_mul a1 (le_refl (ρ ^ 2)) (by positivity) (by linarith),
      sq_nonneg ρ, mul_nonneg (sub_nonneg.2 hρ4) (sub_nonneg.2 hρ1)]
  have hK3 : (8 * ρ) ^ (3 / 2 : ℝ) ≤ 1024 := by
    calc (8 * ρ) ^ (3 / 2 : ℝ) ≤ (32 : ℝ) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      _ ≤ (32 : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 1024 := by norm_num
  have : max ((4 * ρ) ^ κ * ρ ^ 2) ((8 * ρ) ^ (3 / 2 : ℝ)) ≤ 1024 := max_le hK1 hK3
  linarith

/-- `κ^{-κ/2} ≤ 2` for `κ ∈ (0,1]`. -/
theorem rpow_neg_kappa_le {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    κ ^ (-(κ / 2)) ≤ 2 := by
  rw [Real.rpow_def_of_pos hκ0]
  have hlog : 1 - κ⁻¹ ≤ Real.log κ := Real.one_sub_inv_le_log_of_pos hκ0
  have h1 : Real.log κ * -(κ / 2) ≤ 1 / 2 := by
    have : κ * (1 - κ⁻¹) = κ - 1 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hlog hκ0.le]
  have h2 : Real.exp (1 / 2) ≤ 2 := by
    have h3 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have h4 := Real.exp_one_lt_d9
    have h5 := Real.exp_pos (1 / 2)
    nlinarith
  exact (Real.exp_le_exp.2 h1).trans h2

/-- `(2+2/κ)^{(κ+1)/2} ≤ 8 κ^{-1/2}`. -/
theorem qpow_le {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    (2 + 2 / κ) ^ ((κ + 1) / 2) ≤ 8 * κ ^ (-(1 / 2 : ℝ)) := by
  have hq : 2 + 2 / κ ≤ 4 / κ := by
    rw [show (4 : ℝ) / κ = 2 / κ + 2 / κ by ring]
    have : 2 ≤ 2 / κ := by rw [le_div_iff₀ hκ0]; linarith
    linarith
  have hq0 : 0 ≤ 2 + 2 / κ := by positivity
  have h4 : (0 : ℝ) ≤ 4 / κ := by positivity
  calc (2 + 2 / κ) ^ ((κ + 1) / 2) ≤ (4 / κ) ^ ((κ + 1) / 2) :=
        Real.rpow_le_rpow hq0 hq (by positivity)
    _ = (4 / κ) ^ (1 / 2 : ℝ) * (4 / κ) ^ (κ / 2) := by
        rw [← Real.rpow_add (by positivity)]; congr 1; ring
    _ ≤ (2 * κ ^ (-(1 / 2 : ℝ))) * 4 := by
        have a1 : (4 / κ) ^ (1 / 2 : ℝ) = 2 * κ ^ (-(1 / 2 : ℝ)) := by
          rw [Real.div_rpow (by norm_num) hκ0.le, Real.rpow_neg hκ0.le, ← Real.sqrt_eq_rpow,
            show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
          field_simp
        have a2 : (4 / κ) ^ (κ / 2) ≤ 4 := by
          rw [Real.div_rpow (by norm_num) hκ0.le, div_eq_mul_inv, ← Real.rpow_neg hκ0.le]
          have b1 : (4 : ℝ) ^ (κ / 2) ≤ 2 := by
            calc (4 : ℝ) ^ (κ / 2) ≤ (4 : ℝ) ^ (1 / 2 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 2 := by
                  rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num,
                    Real.sqrt_sq (by norm_num)]
          have b2 := rpow_neg_kappa_le hκ0 hκ1
          have b3 : 0 ≤ κ ^ (-(κ / 2)) := Real.rpow_nonneg hκ0.le _
          nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) (κ / 2)]
        rw [a1]
        exact mul_le_mul_of_nonneg_left a2 (by positivity)
    _ = 8 * κ ^ (-(1 / 2 : ℝ)) := by ring

end PDE.BSlocalmax
end

-- ==== from FinalAux2.lean ====
-- The `κ`-dependence of the constant of the `d = 3` statement.


@[expose] public section

namespace PDE.BSlocalmax

lemma rpow_le_max_one {x s : ℝ} (hx : 0 ≤ x) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    x ^ s ≤ max 1 x := by
  rcases le_total 1 x with h | h
  · calc x ^ s ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hs1
      _ = x := Real.rpow_one x
      _ ≤ max 1 x := le_max_right _ _
  · calc x ^ s ≤ (1 : ℝ) ^ s := Real.rpow_le_rpow hx h hs0
      _ = 1 := Real.one_rpow s
      _ ≤ max 1 x := le_max_left _ _

lemma rpow_le_self_of_one_le' {x s : ℝ} (hx : 1 ≤ x) (hs1 : s ≤ 1) : x ^ s ≤ x := by
  calc x ^ s ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hs1
    _ = x := Real.rpow_one x

theorem bound_b {C C2 κ : ℝ} (hC : 0 < C) (hC2 : 0 < C2) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    1 + ((1 + C2 ^ 2) * (10 * 2 ^ (1 + (2 + 2 / κ) / 2) *
          (4 * (C * (2 + 2 / κ))) ^ ((2 + 2 / κ) / 2))) ^ (κ / 2) *
        (2 ^ ((1 + (2 + 2 / κ) / 2) / 2)) ^ κ ≤
      (1 + (1 + C2 ^ 2) * 10 * 4 * max 1 (4 * C) * 8 * 4) * κ ^ (-(1 / 2 : ℝ)) := by
  set q : ℝ := 2 + 2 / κ with hq
  have hq0 : 0 < q := by rw [hq]; positivity
  have hqh : q / 2 = 1 + 1 / κ := by rw [hq]; field_simp
  have hex : (1 + q / 2) * (κ / 2) = κ + 1 / 2 := by rw [hqh]; field_simp; ring
  have hex2 : (1 + q / 2) / 2 * κ = κ + 1 / 2 := by rw [← hex]; ring
  have hex3 : q / 2 * (κ / 2) = (κ + 1) / 2 := by rw [hqh]; field_simp
  have hp2 : (2 : ℝ) ^ (κ + 1 / 2) ≤ 4 := by
    calc (2 : ℝ) ^ (κ + 1 / 2) ≤ (2 : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := by norm_num
  have hC4 : 0 ≤ 4 * C := by positivity
  have hs : (κ + 1) / 2 ≤ 1 := by linarith
  have T1 : (1 + C2 ^ 2) ^ (κ / 2) ≤ 1 + C2 ^ 2 :=
    rpow_le_self_of_one_le' (by nlinarith [sq_nonneg C2]) (by linarith)
  have T2 : (10 : ℝ) ^ (κ / 2) ≤ 10 := rpow_le_self_of_one_le' (by norm_num) (by linarith)
  have T3 : ((2 : ℝ) ^ (1 + q / 2)) ^ (κ / 2) ≤ 4 := by
    rw [← Real.rpow_mul (by norm_num), hex]; exact hp2
  have T5 : ((2 : ℝ) ^ ((1 + q / 2) / 2)) ^ κ ≤ 4 := by
    rw [← Real.rpow_mul (by norm_num), hex2]; exact hp2
  have T4 : ((4 * (C * q)) ^ (q / 2)) ^ (κ / 2) ≤ max 1 (4 * C) * (8 * κ ^ (-(1 / 2 : ℝ))) := by
    rw [← Real.rpow_mul (by positivity), hex3, ← mul_assoc, Real.mul_rpow hC4 hq0.le]
    exact mul_le_mul (rpow_le_max_one hC4 (by positivity) hs) (qpow_le hκ0 hκ1)
      (Real.rpow_nonneg hq0.le _) (le_trans zero_le_one (le_max_left _ _))
  have hA : ((1 + C2 ^ 2) * (10 * 2 ^ (1 + q / 2) * (4 * (C * q)) ^ (q / 2))) ^ (κ / 2) =
      (1 + C2 ^ 2) ^ (κ / 2) * (10 ^ (κ / 2) * ((2 ^ (1 + q / 2)) ^ (κ / 2) *
        ((4 * (C * q)) ^ (q / 2)) ^ (κ / 2))) := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity)]
    ring
  rw [hA]
  have hkm : 1 ≤ κ ^ (-(1 / 2 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hκ0 hκ1 (by norm_num)
  have hkm0 : 0 ≤ κ ^ (-(1 / 2 : ℝ)) := by linarith
  have hmain : (1 + C2 ^ 2) ^ (κ / 2) * (10 ^ (κ / 2) * ((2 ^ (1 + q / 2)) ^ (κ / 2) *
        ((4 * (C * q)) ^ (q / 2)) ^ (κ / 2))) * ((2 : ℝ) ^ ((1 + q / 2) / 2)) ^ κ ≤
      (1 + C2 ^ 2) * (10 * (4 * (max 1 (4 * C) * (8 * κ ^ (-(1 / 2 : ℝ)))))) * 4 := by
    gcongr
  have hE : (1 + C2 ^ 2) * (10 * (4 * (max 1 (4 * C) * (8 * κ ^ (-(1 / 2 : ℝ)))))) * 4 =
      ((1 + C2 ^ 2) * 10 * 4 * max 1 (4 * C) * 8 * 4) * κ ^ (-(1 / 2 : ℝ)) := by ring
  rw [hE] at hmain
  nlinarith [hmain, hkm]

end PDE.BSlocalmax
end

-- ==== from FinalD3.lean ====
/-!
# Sharp local maximum principle on cubes, `d = 3`

For `κ ∈ (0,1]`: `sup_{Q_{1/2}} u₊ ≤ C κ^{-1/2} Λ^{(1+κ)/2} ‖u‖_{L²(Q_1)}`.
-/

@[expose] public section

namespace PDE.BSlocalmax

open MeasureTheory PDE PDE.Ch4Infra

set_option maxHeartbeats 1600000 in
theorem exists_sharpLocalMax_constant_cube_three :
    ∃ C : ℝ, 0 < C ∧ ∀ κ : ℝ, 0 < κ → κ ≤ 1 → ∀ (Λ : ℝ) (a : CoeffField 3),
      (∀ i j : Fin 3, AEMeasurable (fun x => a x i j) (volumeOn (Metric.ball (0 : Vec 3) 1))) →
      (∀ x ∈ Metric.ball (0 : Vec 3) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (Metric.ball (0 : Vec 3) 1),
      IsWeakDivergenceFormSubharmonicOn a (Metric.ball (0 : Vec 3) 1) u →
        essSup (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (Metric.ball (0 : Vec 3) (1 / 2))) ≤
          ENNReal.ofReal (C * κ ^ (-(1 / 2 : ℝ)) * Λ ^ ((1 + κ) / 2)) *
            eLpNorm u.toFun 2 (volumeOn (Metric.ball (0 : Vec 3) 1)) := by
  obtain ⟨Cs, hCs, hBS⟩ := boundary_sobolev_two
  obtain ⟨C2, C0, hC2, hC0, hmain⟩ := sharpLocalMax_cube_Q 2 le_rfl
  refine ⟨2049 * (1 + (1 + C2 ^ 2) * 10 * 4 * max 1 (4 * Cs) * 8 * 4) * Real.sqrt C0, by positivity, ?_⟩
  intro κ hκ0 hκ1 Λ a ha hEll u hsub
  have hΛ : 1 ≤ Λ := (hEll 0 (Metric.mem_ball_self one_pos)).lam_le_Lam
  have hΛ0 : 0 < Λ := by linarith
  have hq : 2 < 2 + 2 / κ := by have : 0 < 2 / κ := by positivity
                                linarith
  have hbs : BoundarySob 2 (2 + 2 / κ) (Cs * (2 + 2 / κ)) :=
    fun {ρ σ} hρ hρσ hσ u hu => hBS (2 + 2 / κ) hq.le hρ hρσ hσ u hu
  have h := hmain (q := 2 + 2 / κ) (Cb := Cs * (2 + 2 / κ)) hq (mul_pos hCs (by linarith)) hbs
    Λ a ha hEll u hsub
  have hp : 1 / ((2 + 2 / κ) / 2 - 1) = κ := by field_simp; ring
  rw [hp] at h
  have he : κ / 2 + 1 / 2 = (1 + κ) / 2 := by ring
  rw [he] at h
  refine h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  have hI : iterConst ((2 + 2 / κ) / 2) (2 / (((2 : ℕ) : ℝ) + 1)) ((1 + (2 + 2 / κ) / 2) / 2) 2
      ≤ 2049 := by
    refine iterConst_le hκ0 hκ1 ?_ ?_ ?_ rfl
    · field_simp; ring
    · field_simp; ring
    · norm_num
  have hI0 : 0 ≤ iterConst ((2 + 2 / κ) / 2) (2 / (((2 : ℕ) : ℝ) + 1))
      ((1 + (2 + 2 / κ) / 2) / 2) 2 := by
    unfold iterConst; positivity
  have hb := bound_b (C := Cs) (C2 := C2) hCs hC2 hκ0 hκ1
  have hM0 : 0 ≤ 1 + ((1 + C2 ^ 2) * (10 * 2 ^ (1 + (2 + 2 / κ) / 2) *
          (4 * (Cs * (2 + 2 / κ))) ^ ((2 + 2 / κ) / 2))) ^ (κ / 2) *
        (2 ^ ((1 + (2 + 2 / κ) / 2) / 2)) ^ κ := by positivity
  have key := mul_le_mul hI hb hM0 (by norm_num)
  calc _ ≤ 2049 * ((1 + (1 + C2 ^ 2) * 10 * 4 * max 1 (4 * Cs) * 8 * 4) * κ ^ (-(1 / 2 : ℝ))) *
        Real.sqrt C0 * Λ ^ ((1 + κ) / 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right key (Real.sqrt_nonneg _))
          (Real.rpow_nonneg hΛ0.le _)
    _ = _ := by ring

end PDE.BSlocalmax
end

-- ==== from FinalD3Log.lean ====
/-!
# `d = 3` without the auxiliary parameter `κ`

Choosing `κ = 1 / log (e + Λ)` in `exists_sharpLocalMax_constant_cube_three` gives
`sup_{Q_{1/2}} u₊ ≤ C Λ^{1/2} log(e+Λ)^{1/2} ‖u‖_{L²(Q_1)}`.
-/

@[expose] public section

namespace PDE.BSlocalmax

open MeasureTheory PDE PDE.Ch4Infra

theorem exists_sharpLocalMax_constant_cube_three_log :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField 3),
      (∀ i j : Fin 3, AEMeasurable (fun x => a x i j) (volumeOn (Metric.ball (0 : Vec 3) 1))) →
      (∀ x ∈ Metric.ball (0 : Vec 3) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (Metric.ball (0 : Vec 3) 1),
      IsWeakDivergenceFormSubharmonicOn a (Metric.ball (0 : Vec 3) 1) u →
        essSup (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (Metric.ball (0 : Vec 3) (1 / 2))) ≤
          ENNReal.ofReal (C * Λ ^ (1 / 2 : ℝ) * (Real.log (Real.exp 1 + Λ)) ^ (1 / 2 : ℝ)) *
            eLpNorm u.toFun 2 (volumeOn (Metric.ball (0 : Vec 3) 1)) := by
  obtain ⟨C, hC, h⟩ := exists_sharpLocalMax_constant_cube_three
  refine ⟨2 * C, by positivity, ?_⟩
  intro Λ a ha hEll u hsub
  have hΛ : 1 ≤ Λ := (hEll 0 (Metric.mem_ball_self one_pos)).lam_le_Lam
  have hΛ0 : 0 < Λ := by linarith
  have hexp : 0 < Real.exp 1 := Real.exp_pos 1
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log (Real.exp 1 + Λ) := ⟨_, rfl⟩
  rw [← hLdef]
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith)]; linarith
  have hL0 : 0 < L := by linarith
  have hκ0 : 0 < 1 / L := by positivity
  have hκ1 : 1 / L ≤ 1 := by rw [div_le_one hL0]; exact hL1
  have h3 := h (1 / L) hκ0 hκ1 Λ a ha hEll u hsub
  refine h3.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  have e1 : (1 / L) ^ (-(1 / 2 : ℝ)) = L ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_neg hκ0.le, Real.div_rpow zero_le_one hL0.le, Real.one_rpow, one_div, inv_inv]
  have e2 : Λ ^ ((1 + 1 / L) / 2) = Λ ^ (1 / 2 : ℝ) * Λ ^ ((1 / L) / 2) := by
    rw [← Real.rpow_add hΛ0]; congr 1; ring
  have hlog : Real.log Λ ≤ L := by
    rw [hLdef]; exact Real.log_le_log hΛ0 (by linarith)
  have e3 : Λ ^ ((1 / L) / 2) ≤ 2 := by
    rw [Real.rpow_def_of_pos hΛ0]
    have h1 : Real.log Λ * ((1 / L) / 2) ≤ 1 / 2 := by
      calc Real.log Λ * ((1 / L) / 2) ≤ L * ((1 / L) / 2) :=
            mul_le_mul_of_nonneg_right hlog (by positivity)
        _ = 1 / 2 := by field_simp
    have h2 : Real.exp (1 / 2) ≤ 2 := by
      have h3 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      have h4 := Real.exp_one_lt_d9
      have h5 := Real.exp_pos (1 / 2)
      nlinarith
    exact (Real.exp_le_exp.2 h1).trans h2
  rw [e1, e2]
  have hP : 0 ≤ C * L ^ (1 / 2 : ℝ) * Λ ^ (1 / 2 : ℝ) := by positivity
  calc C * L ^ (1 / 2 : ℝ) * (Λ ^ (1 / 2 : ℝ) * Λ ^ ((1 / L) / 2))
      = (C * L ^ (1 / 2 : ℝ) * Λ ^ (1 / 2 : ℝ)) * Λ ^ ((1 / L) / 2) := by ring
    _ ≤ (C * L ^ (1 / 2 : ℝ) * Λ ^ (1 / 2 : ℝ)) * 2 := mul_le_mul_of_nonneg_left e3 hP
    _ = _ := by ring

end PDE.BSlocalmax
end
