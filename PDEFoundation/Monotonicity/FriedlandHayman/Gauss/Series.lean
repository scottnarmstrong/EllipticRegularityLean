module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Friedland--Hayman: entire power series for the Hermite equation

The power series solution `∑ aₙ sⁿ` of `y'' - s y' + c y = 0` has coefficients given by the
recurrence `a_{n+2} = (n - c) aₙ / ((n+2)(n+1))` (`ouCoef`).  We prove the bound
`|a_n| ≤ (|a₀| + |a₁|) mₙ(C)` for `|c| ≤ C`, where `m(C)` is an explicit majorant such that
`∑ mₙ Rⁿ` converges for every `R`; this gives locally uniform convergence in `(c, s)` of the
series and of its derivative series (`OuUEntire`).  We also prove termwise differentiation and
the ODE relation for an entire series.
-/

@[expose] public section

open Filter Topology

namespace PDE.FHLane

noncomputable section

/-- Coefficients of the power series solution of `y'' - s y' + c y = 0`, with `y 0 = a₀`,
`y' 0 = a₁`. -/
def ouCoef (c a₀ a₁ : ℝ) : ℕ → ℝ
  | 0 => a₀
  | 1 => a₁
  | n + 2 => ((n : ℝ) - c) * ouCoef c a₀ a₁ n / (((n : ℝ) + 2) * ((n : ℝ) + 1))

/-- A majorant for `ouCoef` when `|c| ≤ C`. -/
def ouMaj (C : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | n + 2 => ((n : ℝ) + C) / (((n : ℝ) + 2) * ((n : ℝ) + 1)) * ouMaj C n

/-- The power series `∑ bₙ sⁿ`. -/
def ouSer (b : ℕ → ℝ) (s : ℝ) : ℝ := ∑' n, b n * s ^ n

/-- The coefficient sequence of the derivative series. -/
def ouD (b : ℕ → ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) * b (n + 1)

/-- A coefficient sequence has infinite radius of convergence (absolute convergence). -/
def OuEntire (b : ℕ → ℝ) : Prop := ∀ R : ℝ, 0 ≤ R → Summable fun n => |b n| * R ^ n

/-- A family of coefficient sequences, parametrized by `c`, with summable majorants that are
uniform for `|c| ≤ C` and `|s| ≤ R`. -/
def OuUEntire (b : ℝ → ℕ → ℝ) : Prop :=
  ∀ C R : ℝ, 0 ≤ C → 0 ≤ R → ∃ u : ℕ → ℝ, Summable u ∧
    ∀ c : ℝ, |c| ≤ C → ∀ n, |b c n| * R ^ n ≤ u n

theorem ouMaj_nonneg {C : ℝ} (hC : 0 ≤ C) : ∀ n, 0 ≤ ouMaj C n
  | 0 => by simp [ouMaj]
  | 1 => by simp [ouMaj]
  | n + 2 => by
    have := ouMaj_nonneg hC n
    simp only [ouMaj]
    positivity

theorem abs_ouCoef_le {c C : ℝ} (hc : |c| ≤ C) (a₀ a₁ : ℝ) :
    ∀ n, |ouCoef c a₀ a₁ n| ≤ (|a₀| + |a₁|) * ouMaj C n
  | 0 => by simp [ouCoef, ouMaj]
  | 1 => by simp [ouCoef, ouMaj]
  | n + 2 => by
    have ih := abs_ouCoef_le hc a₀ a₁ n
    have hC : 0 ≤ C := (abs_nonneg c).trans hc
    have hD : (0 : ℝ) < ((n : ℝ) + 2) * ((n : ℝ) + 1) := by positivity
    have hm := ouMaj_nonneg hC n
    have hnc : |(n : ℝ) - c| ≤ (n : ℝ) + C := by
      calc |(n : ℝ) - c| ≤ |(n : ℝ)| + |c| := abs_sub _ _
        _ ≤ (n : ℝ) + C := by rw [Nat.abs_cast]; linarith
    simp only [ouCoef, ouMaj]
    rw [abs_div, abs_mul, abs_of_pos hD, div_le_iff₀ hD]
    calc |(n : ℝ) - c| * |ouCoef c a₀ a₁ n|
        ≤ ((n : ℝ) + C) * ((|a₀| + |a₁|) * ouMaj C n) := by
          apply mul_le_mul hnc ih (abs_nonneg _) (by positivity)
      _ = (|a₀| + |a₁|) * (((n : ℝ) + C) / (((n : ℝ) + 2) * ((n : ℝ) + 1)) * ouMaj C n) *
            (((n : ℝ) + 2) * ((n : ℝ) + 1)) := by
          field_simp

/-- Two-step ratio test. -/
theorem summable_of_two_step {t : ℕ → ℝ} (ht : ∀ n, 0 ≤ t n) {N : ℕ}
    (h : ∀ n, N ≤ n → t (n + 2) ≤ t n / 4) : Summable t := by
  set v : ℕ → ℝ := fun n => t n + 2 * t (n + 1) with hv
  have hv0 : ∀ n, 0 ≤ v n := fun n => by have := ht n; have := ht (n + 1); simp only [hv]; positivity
  have : Summable v := by
    refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hv0 _), abs_of_nonneg (hv0 _)]
    have := h n hn
    simp only [hv]
    linarith
  refine this.of_nonneg_of_le ht fun n => ?_
  simp only [hv]
  linarith [ht (n + 1)]

theorem summable_ouMaj_mul_pow {C : ℝ} (hC : 0 ≤ C) {R : ℝ} (hR : 0 ≤ R) :
    Summable fun n => ouMaj C n * R ^ n := by
  obtain ⟨N, hN⟩ := exists_nat_ge (4 * R ^ 2 * (1 + C) + 1)
  refine summable_of_two_step (fun n => mul_nonneg (ouMaj_nonneg hC n) (pow_nonneg hR n))
    (N := N) fun n hn => ?_
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hK : 0 ≤ 4 * R ^ 2 := by positivity
  have h1 : 1 ≤ (n : ℝ) := by nlinarith [mul_nonneg hK hC]
  have hnn : 0 ≤ ouMaj C n * R ^ n := mul_nonneg (ouMaj_nonneg hC n) (pow_nonneg hR n)
  have hD : (0 : ℝ) < ((n : ℝ) + 2) * ((n : ℝ) + 1) := by positivity
  have hkey : 4 * R ^ 2 * ((n : ℝ) + C) ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) := by
    have : 4 * R ^ 2 * (1 + C) ≤ n := by linarith
    nlinarith [mul_nonneg hK hC, mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ n)]
  have hr : ((n : ℝ) + C) / (((n : ℝ) + 2) * ((n : ℝ) + 1)) * R ^ 2 ≤ 1 / 4 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hD]
    nlinarith
  calc ouMaj C (n + 2) * R ^ (n + 2)
      = (((n : ℝ) + C) / (((n : ℝ) + 2) * ((n : ℝ) + 1)) * R ^ 2) * (ouMaj C n * R ^ n) := by
        simp only [ouMaj]; ring
    _ ≤ 1 / 4 * (ouMaj C n * R ^ n) := mul_le_mul_of_nonneg_right hr hnn
    _ = ouMaj C n * R ^ n / 4 := by ring

theorem continuous_ouCoef (a₀ a₁ : ℝ) : ∀ n, Continuous fun c : ℝ => ouCoef c a₀ a₁ n
  | 0 => by simp only [ouCoef]; exact continuous_const
  | 1 => by simp only [ouCoef]; exact continuous_const
  | n + 2 => by
    have ih := continuous_ouCoef a₀ a₁ n
    simp only [ouCoef]
    exact ((continuous_const.sub continuous_id).mul ih).div_const _

theorem ouUEntire_ouCoef (a₀ a₁ : ℝ) : OuUEntire fun c => ouCoef c a₀ a₁ := by
  intro C R hC hR
  refine ⟨fun n => (|a₀| + |a₁|) * (ouMaj C n * R ^ n),
    (summable_ouMaj_mul_pow hC hR).mul_left _, fun c hc n => ?_⟩
  show |ouCoef c a₀ a₁ n| * R ^ n ≤ (|a₀| + |a₁|) * (ouMaj C n * R ^ n)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (abs_ouCoef_le hc a₀ a₁ n) (pow_nonneg hR n)

theorem ouD_ouD_ouCoef (c a₀ a₁ : ℝ) (n : ℕ) :
    ouD (ouD (ouCoef c a₀ a₁)) n = ((n : ℝ) - c) * ouCoef c a₀ a₁ n := by
  have hD : (((n : ℝ) + 2) * ((n : ℝ) + 1)) ≠ 0 := by positivity
  simp only [ouD, ouCoef]
  push_cast
  field_simp
  ring

theorem nat_add_one_mul_pow_le {R : ℝ} (hR : 0 ≤ R) (n : ℕ) :
    ((n : ℝ) + 1) * R ^ n ≤ (2 * R + 2) ^ (n + 1) := by
  have h2 : ((n : ℝ) + 1) ≤ 2 ^ n := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := n))
  calc ((n : ℝ) + 1) * R ^ n ≤ 2 ^ n * R ^ n := mul_le_mul_of_nonneg_right h2 (pow_nonneg hR n)
    _ = (2 * R) ^ n := by rw [mul_pow]
    _ ≤ (2 * R + 2) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
    _ ≤ (2 * R + 2) ^ (n + 1) := pow_le_pow_right₀ (by linarith) (Nat.le_succ n)

theorem nat_mul_pow_le {R : ℝ} (hR : 0 ≤ R) (n : ℕ) : (n : ℝ) * R ^ n ≤ (2 * R) ^ n := by
  have h2 : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  calc (n : ℝ) * R ^ n ≤ 2 ^ n * R ^ n := mul_le_mul_of_nonneg_right h2 (pow_nonneg hR n)
    _ = (2 * R) ^ n := by rw [mul_pow]

theorem OuUEntire.D {b : ℝ → ℕ → ℝ} (hb : OuUEntire b) : OuUEntire fun c => ouD (b c) := by
  intro C R hC hR
  obtain ⟨u, hu, hub⟩ := hb C (2 * R + 2) hC (by positivity)
  refine ⟨fun n => u (n + 1), (summable_nat_add_iff 1).mpr hu, fun c hc n => ?_⟩
  calc |ouD (b c) n| * R ^ n = |b c (n + 1)| * (((n : ℝ) + 1) * R ^ n) := by
        simp only [ouD]
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
        ring
    _ ≤ |b c (n + 1)| * (2 * R + 2) ^ (n + 1) :=
        mul_le_mul_of_nonneg_left (nat_add_one_mul_pow_le hR n) (abs_nonneg _)
    _ ≤ u (n + 1) := hub c hc (n + 1)

theorem OuUEntire.entire {b : ℝ → ℕ → ℝ} (hb : OuUEntire b) (c : ℝ) : OuEntire (b c) := by
  intro R hR
  obtain ⟨u, hu, hub⟩ := hb |c| R (abs_nonneg c) hR
  exact hu.of_nonneg_of_le (fun n => by positivity) fun n => hub c le_rfl n

theorem OuEntire.summable {b : ℕ → ℝ} (hb : OuEntire b) (s : ℝ) :
    Summable fun n => b n * s ^ n := by
  refine Summable.of_norm ?_
  simpa [norm_mul, norm_pow] using hb |s| (abs_nonneg s)

theorem OuEntire.summable_nat_mul {b : ℕ → ℝ} (hb : OuEntire b) (s : ℝ) :
    Summable fun n : ℕ => (n : ℝ) * b n * s ^ n := by
  refine Summable.of_norm_bounded (hb (2 * |s|) (by positivity)) fun n => ?_
  have h := nat_mul_pow_le (abs_nonneg s) n
  rw [norm_mul, norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    Nat.abs_cast]
  calc (n : ℝ) * |b n| * |s| ^ n = |b n| * ((n : ℝ) * |s| ^ n) := by ring
    _ ≤ |b n| * (2 * |s|) ^ n := mul_le_mul_of_nonneg_left h (abs_nonneg _)

theorem OuEntire.D {b : ℕ → ℝ} (hb : OuEntire b) : OuEntire (ouD b) := by
  intro R hR
  have := (summable_nat_add_iff 1).mpr (hb (2 * R + 2) (by positivity))
  refine this.of_nonneg_of_le (fun n => by positivity) fun n => ?_
  calc |ouD b n| * R ^ n = |b (n + 1)| * (((n : ℝ) + 1) * R ^ n) := by
        simp only [ouD]
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (nat_add_one_mul_pow_le hR n) (abs_nonneg _)

/-- Termwise differentiation of an entire power series. -/
theorem hasDerivAt_ouSer {b : ℕ → ℝ} (hb : OuEntire b) (s : ℝ) :
    HasDerivAt (ouSer b) (ouSer (ouD b) s) s := by
  set R : ℝ := |s| + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  have hu : Summable fun n => |b n| * (2 * R + 2) ^ n := hb _ (by positivity)
  have hder : HasDerivAt (fun z => ∑' n, b n * z ^ n)
      (∑' n, b n * ((n : ℝ) * s ^ (n - 1))) s := by
    refine hasDerivAt_tsum_of_isPreconnected (u := fun n => |b n| * (2 * R + 2) ^ n)
      (g := fun n z => b n * z ^ n) (g' := fun n z => b n * ((n : ℝ) * z ^ (n - 1)))
      (t := Metric.ball 0 R) hu Metric.isOpen_ball (convex_ball 0 R).isPreconnected
      (fun n y _ => ?_) (fun n y hy => ?_) (y₀ := s) ?_ (hb.summable s) ?_
    · exact (hasDerivAt_pow n y).const_mul (b n)
    · have hy' : |y| ≤ R := by
        have := mem_ball_zero_iff.mp hy
        rw [Real.norm_eq_abs] at this
        exact this.le
      simp only [norm_mul, Real.norm_eq_abs, Nat.abs_cast, abs_pow]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have h1 : |y| ^ (n - 1) ≤ R ^ (n - 1) := pow_le_pow_left₀ (abs_nonneg y) hy' _
        have h2 : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
        have h3 : R ^ (n - 1) ≤ (R + 1) ^ n := by
          calc R ^ (n - 1) ≤ (R + 1) ^ (n - 1) := pow_le_pow_left₀ hR0 (by linarith) _
            _ ≤ (R + 1) ^ n := pow_le_pow_right₀ (by linarith) (Nat.sub_le n 1)
        calc (n : ℝ) * |y| ^ (n - 1) ≤ 2 ^ n * (R + 1) ^ n :=
              mul_le_mul h2 (h1.trans h3) (by positivity) (by positivity)
          _ = (2 * (R + 1)) ^ n := by rw [mul_pow]
          _ = (2 * R + 2) ^ n := by ring_nf
    · rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, hR]; linarith
    · rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, hR]; linarith
  have hs : Summable fun n => b n * ((n : ℝ) * s ^ (n - 1)) := by
    refine Summable.of_norm_bounded
      (hb (2 * |s| + 2) (by positivity)) fun n => ?_
    simp only [norm_mul, Real.norm_eq_abs, Nat.abs_cast, abs_pow]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h2 : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
      have h3 : |s| ^ (n - 1) ≤ (|s| + 1) ^ n := by
        calc |s| ^ (n - 1) ≤ (|s| + 1) ^ (n - 1) := pow_le_pow_left₀ (abs_nonneg s) (by linarith) _
          _ ≤ (|s| + 1) ^ n := pow_le_pow_right₀ (by linarith [abs_nonneg s]) (Nat.sub_le n 1)
      calc (n : ℝ) * |s| ^ (n - 1) ≤ 2 ^ n * (|s| + 1) ^ n :=
            mul_le_mul h2 h3 (by positivity) (by positivity)
        _ = (2 * |s| + 2) ^ n := by rw [← mul_pow]; ring_nf
  have hshift : ∑' n, b n * ((n : ℝ) * s ^ (n - 1)) = ouSer (ouD b) s := by
    rw [hs.tsum_eq_zero_add]
    simp only [ouSer, ouD]
    simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, Nat.add_sub_cancel, Nat.cast_add,
      Nat.cast_one]
    exact tsum_congr fun n => by ring
  rw [← hshift]
  exact hder

/-- The ODE relation for an entire series whose coefficients satisfy the Hermite recurrence. -/
theorem ouSer_ouD_ouD {b : ℕ → ℝ} (hb : OuEntire b) {c : ℝ}
    (hrec : ∀ n, ouD (ouD b) n = ((n : ℝ) - c) * b n) (s : ℝ) :
    ouSer (ouD (ouD b)) s = s * ouSer (ouD b) s - c * ouSer b s := by
  have h1 : ∑' n : ℕ, (n : ℝ) * b n * s ^ n = s * ouSer (ouD b) s := by
    rw [(hb.summable_nat_mul s).tsum_eq_zero_add]
    simp only [ouSer, ouD, Nat.cast_zero, zero_mul, zero_add, Nat.cast_add, Nat.cast_one]
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by ring
  have h2 : ouSer (ouD (ouD b)) s = ∑' n : ℕ, ((n : ℝ) * b n * s ^ n - c * (b n * s ^ n)) := by
    simp only [ouSer, hrec]
    exact tsum_congr fun n => by ring
  rw [h2, Summable.tsum_sub (hb.summable_nat_mul s) ((hb.summable s).mul_left c), h1,
    tsum_mul_left]
  rfl

/-- Joint continuity of the series in `(c, s)`. -/
theorem continuous_ouSer_uncurry {b : ℝ → ℕ → ℝ} (hb : OuUEntire b)
    (hc : ∀ n, Continuous fun c => b c n) : Continuous fun p : ℝ × ℝ => ouSer (b p.1) p.2 := by
  rw [continuous_iff_continuousAt]
  intro p
  set C : ℝ := |p.1| + 1
  set R : ℝ := |p.2| + 1
  have hC : 0 ≤ C := by positivity
  have hR : 0 ≤ R := by positivity
  obtain ⟨u, hu, hub⟩ := hb C R hC hR
  have hon : ContinuousOn (fun p : ℝ × ℝ => ∑' n, b p.1 n * p.2 ^ n)
      {q : ℝ × ℝ | |q.1| < C ∧ |q.2| < R} := by
    refine continuousOn_tsum (fun n => ?_) hu fun n q hq => ?_
    · exact ((hc n).comp continuous_fst |>.mul (continuous_snd.pow n)).continuousOn
    · rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]
      refine le_trans ?_ (hub q.1 hq.1.le n)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hq.2.le n) (abs_nonneg _)
  have hopen : IsOpen {q : ℝ × ℝ | |q.1| < C ∧ |q.2| < R} :=
    (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)
  exact hon.continuousAt (hopen.mem_nhds ⟨by simp [C], by simp [R]⟩)

end

end PDE.FHLane
