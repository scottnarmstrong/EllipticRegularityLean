module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Layercake
public import BSlocalmax.FaceInequalities
public import PDEFoundation.Analysis.Inequalities.Bridges.ExponentLowering
public import PDEFoundation.Analysis.Inequalities.Trudinger.CenteredMaximal
public import PDEFoundation.Analysis.Inequalities.Trudinger.PointwiseLog
public import PDEFoundation.Measure.BallMaximalWeak
public import PDEFoundation.Sobolev.Inequalities.ConvexRiesz
public import PDEFoundation.Sobolev.W1p.EuclideanGradient
public import PDEFoundation.Sobolev.W1p.ZeroGradient

/-!
# Trudinger inequality on convex domains and the sqrt(q)-Sobolev inequality on faces

This file collects the following pieces, in dependency order: TrudFar, TrudLog, TrudDist, TrudMain, TrudSqrtA, TrudSqrtB, TrudSqrtC, TrudSqrtD, TrudUnif, FaceSqrt, BoundarySobolevGen.
-/

-- ==== from TrudFar.lean ====
-- Generalization of Armstrong's Trudinger inequality from the unit ball to convex sets:
-- far part of the Riesz kernel with support radius 4 (instead of 2).


@[expose] public section

open MeasureTheory Set PDE.Trudinger
open scoped ENNReal

namespace PDE
namespace TrudingerV

variable {d : ℕ}

/-- `∫_{(1/2)^k ≤ |x - y| < 4} |x - y|^{-d} dy ≤ (k+1) 2^d |B₁|`. -/
theorem lintegral_far_kernel_le (x : Vec d) (k : ℕ) :
    ∫⁻ y in {y : Vec d | (1 / 2 : ℝ) ^ k ≤ vecEuclideanNorm (x - y) ∧ vecEuclideanNorm (x - y) < 4},
        ENNReal.ofReal (vecEuclideanNorm (x - y) ^ (-(d : ℝ))) ≤
      ENNReal.ofReal ((k + 2) * 2 ^ d) * volume (euclideanBall (0 : Vec d) 1) := by
  classical
  set ε : ℝ := (1 / 2 : ℝ) ^ k with hε
  have hεpos : 0 < ε := by positivity
  set b : ℕ → ℝ := fun j => 2 ^ j * ε with hb
  have hbpos : ∀ j, 0 < b j := fun j => by positivity
  have h4 : (2 : ℝ) ^ (k + 1 + 1) * ε = 4 := by
    have h1 : (2 : ℝ) ^ k * (1 / 2) ^ k = 1 := by rw [← mul_pow]; norm_num
    calc (2 : ℝ) ^ (k + 1 + 1) * ε = 4 * (2 ^ k * (1 / 2) ^ k) := by simp only [hε]; ring
      _ = 4 := by rw [h1]; ring
  have hpt : ∀ y ∈ {y : Vec d | ε ≤ vecEuclideanNorm (x - y) ∧ vecEuclideanNorm (x - y) < 4},
      ENNReal.ofReal (vecEuclideanNorm (x - y) ^ (-(d : ℝ))) ≤
        ∑ j ∈ Finset.range (k + 2), (euclideanBall x (2 * b j)).indicator
          (fun _ => ENNReal.ofReal (b j ^ (-(d : ℝ)))) y := by
    rintro y ⟨hy1, hy2⟩
    have hrpos : 0 < vecEuclideanNorm (x - y) := lt_of_lt_of_le hεpos hy1
    have hP : ∃ j : ℕ, vecEuclideanNorm (x - y) < 2 ^ (j + 1) * ε := by
      refine ⟨k + 1, ?_⟩
      rw [h4]; exact hy2
    have hjk : Nat.find hP ≤ k + 1 := Nat.find_min' hP (by
      rw [h4]; exact hy2)
    have hlt : vecEuclideanNorm (x - y) < 2 * b (Nat.find hP) := by
      have := Nat.find_spec hP
      simp only [hb]; rw [pow_succ] at this; linarith
    have hge : b (Nat.find hP) ≤ vecEuclideanNorm (x - y) := by
      rcases h : Nat.find hP with _ | j
      · simpa [hb] using hy1
      · have := Nat.find_min hP (m := j) (by omega)
        simp only [hb]; exact not_lt.mp this
    refine le_trans ?_ (Finset.single_le_sum (f := fun j => (euclideanBall x (2 * b j)).indicator
          (fun _ => ENNReal.ofReal (b j ^ (-(d : ℝ)))) y) (fun _ _ => bot_le)
          (Finset.mem_range.2 (Nat.lt_succ_of_le hjk)))
    rw [Set.indicator_of_mem ((mem_euclideanBall_iff_norm_sub_lt x y
      (by have := hbpos (Nat.find hP); positivity)).2 hlt)]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (hbpos _) hge (by simp))
  calc _ ≤ ∫⁻ y in {y : Vec d | ε ≤ vecEuclideanNorm (x - y) ∧ vecEuclideanNorm (x - y) < 4},
        ∑ j ∈ Finset.range (k + 2), (euclideanBall x (2 * b j)).indicator
          (fun _ => ENNReal.ofReal (b j ^ (-(d : ℝ)))) y :=
        setLIntegral_mono' ((measurableSet_le measurable_const (measurable_norm_sub x)).inter
          (measurableSet_lt (measurable_norm_sub x) measurable_const)) hpt
    _ ≤ ∫⁻ y, ∑ j ∈ Finset.range (k + 2), (euclideanBall x (2 * b j)).indicator
          (fun _ => ENNReal.ofReal (b j ^ (-(d : ℝ)))) y := setLIntegral_le_lintegral _ _
    _ = ∑ j ∈ Finset.range (k + 2), ENNReal.ofReal (b j ^ (-(d : ℝ))) *
          volume (euclideanBall x (2 * b j)) := by
        rw [lintegral_finsetSum]
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [lintegral_indicator_const (measurableSet_euclideanBall _ _)]
        · intro j _
          exact measurable_const.indicator (measurableSet_euclideanBall _ _)
    _ = ∑ j ∈ Finset.range (k + 2),
          ENNReal.ofReal (2 ^ d) * volume (euclideanBall (0 : Vec d) 1) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have h2b : 0 < 2 * b j := by have := hbpos j; positivity
        rw [volume_euclideanBall_eq_unit_mul_of_pos x h2b, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity), far_term_eq (hbpos j)]
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 3
        push_cast; ring

/-- Far part of the Riesz potential (Trudinger, Step 3), via Hölder and the shell estimate. -/
theorem lintegral_far_le (hd : 2 ≤ d) (x : Vec d) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    (hLd : ∫⁻ y, f y ^ (d : ℝ) ≤ 1) (k : ℕ) :
    ∫⁻ y in {y : Vec d | (1 / 2 : ℝ) ^ k ≤ vecEuclideanNorm (x - y) ∧ vecEuclideanNorm (x - y) < 4},
        ENNReal.ofReal (vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d)) * f y ≤
      (ENNReal.ofReal ((k + 2) * 2 ^ d) * volume (euclideanBall (0 : Vec d) 1)) ^
        (((d : ℝ) - 1) / d) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set S : Set (Vec d) :=
    {y | (1 / 2 : ℝ) ^ k ≤ vecEuclideanNorm (x - y) ∧ vecEuclideanNorm (x - y) < 4} with hS
  have hpq : (d : ℝ).HolderConjugate ((d : ℝ) / ((d : ℝ) - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent (by linarith)).2 rfl
  have hK : Measurable fun y : Vec d =>
      ENNReal.ofReal (vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d)) :=
    ENNReal.measurable_ofReal.comp ((measurable_norm_sub x).pow_const _)
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict S) hpq hf.aemeasurable
    hK.aemeasurable
  have h1 : ∫⁻ y in S, ENNReal.ofReal (vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d)) * f y =
      ∫⁻ y in S, f y * ENNReal.ofReal (vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d)) :=
    lintegral_congr fun y => mul_comm _ _
  rw [h1]
  refine le_trans (le_of_eq rfl) (hH.trans ?_)
  have hA : (∫⁻ y in S, f y ^ (d : ℝ)) ^ (1 / (d : ℝ)) ≤ 1 := by
    calc (∫⁻ y in S, f y ^ (d : ℝ)) ^ (1 / (d : ℝ)) ≤ 1 ^ (1 / (d : ℝ)) :=
          ENNReal.rpow_le_rpow ((setLIntegral_le_lintegral _ _).trans hLd) (by positivity)
      _ = 1 := ENNReal.one_rpow _
  have hB : ∫⁻ y in S, (ENNReal.ofReal (vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d))) ^
      ((d : ℝ) / ((d : ℝ) - 1)) ≤
      ENNReal.ofReal ((k + 2) * 2 ^ d) * volume (euclideanBall (0 : Vec d) 1) := by
    refine le_trans (le_of_eq (lintegral_congr fun y => ?_)) (lintegral_far_kernel_le x k)
    exact PDE.Trudinger.kernel_rpow_conj hd (vecEuclideanNorm_nonneg _)
  have hB' := ENNReal.rpow_le_rpow hB (z := 1 / ((d : ℝ) / ((d : ℝ) - 1))) (by
    have : (0 : ℝ) < d - 1 := by linarith
    positivity)
  rw [one_div_div] at hB'
  rw [one_div_div]
  refine (mul_le_mul_left hA _).trans ?_
  rw [one_mul]
  exact hB'

end TrudingerV
end PDE
end

-- ==== from TrudLog.lean ====
-- Pointwise logarithmic bound for the Riesz potential, support radius 4.


@[expose] public section

open MeasureTheory Set
open PDE.Trudinger hiding lintegral_far_le lintegral_far_kernel_le lintegral_riesz_le_log
open scoped ENNReal

namespace PDE
namespace TrudingerV

variable {d : ℕ}

/-- The pointwise logarithmic bound for the Riesz potential (Trudinger, Steps 2-4). -/
theorem lintegral_riesz_le_log (hd : 2 ≤ d) (x : Vec d) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    (hLd : ∫⁻ y, f y ^ (d : ℝ) ≤ 1)
    (hsupp : ∀ y, f y ≠ 0 → vecEuclideanNorm (x - y) < 4)
    {m : ℝ} (hm : 0 < m)
    (havg : ∀ ρ : ℝ, 0 < ρ →
      ∫⁻ y in euclideanBall x ρ, f y ≤ ENNReal.ofReal m * volume (euclideanBall x ρ)) :
    ∫⁻ y, ENNReal.ofReal (vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d)) * f y ≤
      ENNReal.ofReal (C2 d * Real.log (2 + m) ^ (((d : ℝ) - 1) / d)) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hv := unitVol_pos d
  set θ : ℝ := ((d : ℝ) - 1) / d with hθ
  have hθ0 : 0 < θ := div_pos (by linarith) (by linarith)
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one (by linarith)]; linarith
  set L : ℝ := Real.log (2 + m) with hL
  have hℓ := Real.log_two_gt_d9
  have hLℓ : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  have hL0 : 0 < L := by linarith
  set T : ℝ := L ^ θ with hT
  have hT0 : 0 < T := Real.rpow_pos_of_pos hL0 _
  have hT1 : 0.69 < T := by
    rcases le_or_gt 1 L with h1 | h1
    · have := Real.one_le_rpow h1 hθ0.le
      linarith
    · have : L ^ (1 : ℝ) ≤ L ^ θ := Real.rpow_le_rpow_of_exponent_ge hL0 h1.le hθ1
      rw [Real.rpow_one] at this
      linarith
  classical
  have hex : ∃ k : ℕ, (1 / 2 : ℝ) ^ k * m ≤ T := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hT0 hm) (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨n, ?_⟩
    rw [lt_div_iff₀ hm] at hn
    exact hn.le
  set k := Nat.find hex with hk
  have hk1 : (1 / 2 : ℝ) ^ k * m ≤ T := Nat.find_spec hex
  have hkb : (k : ℝ) + 2 ≤ 8 * L := by
    rcases hkc : Nat.find hex with _ | j
    · have : (0 : ℕ) = k := hkc.symm
      simp only [← this]; push_cast; linarith
    · have hmin := Nat.find_min hex (m := j) (by omega)
      have hj : T < (1 / 2 : ℝ) ^ j * m := not_le.mp hmin
      have h2j : (2 : ℝ) ^ j < 2 * m := by
        have hp : (0 : ℝ) < 2 ^ j := by positivity
        have : (1 / 2 : ℝ) ^ j = 1 / 2 ^ j := by rw [one_div_pow]
        rw [this, one_div, inv_mul_eq_div, lt_div_iff₀ hp] at hj
        nlinarith
      have hlogj : (j : ℝ) * Real.log 2 < Real.log 2 + L := by
        have h3 := Real.log_lt_log (by positivity) (h2j.trans (by linarith : 2 * m < 2 * (2 + m)))
        rw [Real.log_pow, Real.log_mul (by norm_num) (by linarith)] at h3
        exact h3
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have h4 : (j : ℝ) * 0.69 ≤ j * Real.log 2 := by nlinarith
      have hkj : (k : ℝ) = j + 1 := by
        have : k = j + 1 := hkc
        simp [this]
      rw [hkj]
      linarith
  set ε : ℝ := (1 / 2 : ℝ) ^ k with hε
  have hε0 : 0 < ε := by positivity
  set S : Set (Vec d) :=
    {y | ε ≤ vecEuclideanNorm (x - y) ∧ vecEuclideanNorm (x - y) < 4} with hS
  set g : Vec d → ℝ≥0∞ :=
    fun y => ENNReal.ofReal (vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d)) * f y with hg
  have hgm : Measurable g :=
    (ENNReal.measurable_ofReal.comp ((measurable_norm_sub x).pow_const _)).mul hf
  have hSm : MeasurableSet S :=
    (measurableSet_le measurable_const (measurable_norm_sub x)).inter
      (measurableSet_lt (measurable_norm_sub x) measurable_const)
  have hpt : ∀ y, g y ≤ (euclideanBall x ε).indicator g y + S.indicator g y := by
    intro y
    by_cases hfy : f y = 0
    · simp [hg, hfy]
    · have h2 := hsupp y hfy
      by_cases hy : vecEuclideanNorm (x - y) < ε
      · rw [Set.indicator_of_mem ((mem_euclideanBall_iff_norm_sub_lt x y hε0).2 hy)]
        exact le_self_add
      · rw [Set.indicator_of_mem (show y ∈ S from ⟨not_lt.mp hy, h2⟩)]
        exact le_add_self
  have hnear := lintegral_near_le hd x hε0 hm.le hf havg
  have hfar := lintegral_far_le hd x hf hLd k
  rw [← hθ] at hfar
  calc ∫⁻ y, g y ≤ ∫⁻ y, ((euclideanBall x ε).indicator g y + S.indicator g y) :=
        lintegral_mono hpt
    _ = (∫⁻ y in euclideanBall x ε, g y) + ∫⁻ y in S, g y := by
        rw [lintegral_add_left (hgm.indicator (measurableSet_euclideanBall _ _)),
          lintegral_indicator (measurableSet_euclideanBall _ _), lintegral_indicator hSm]
    _ ≤ ENNReal.ofReal (2 ^ d * T) * ENNReal.ofReal (unitVol d) +
          ENNReal.ofReal ((8 * 2 ^ d * unitVol d) ^ θ * T) := by
        refine add_le_add ?_ ?_
        · rw [ofReal_unitVol]
          refine hnear.trans (mul_le_mul_left ?_ _)
          exact ENNReal.ofReal_le_ofReal (by
            have : 2 ^ d * ε * m = 2 ^ d * (ε * m) := by ring
            rw [this]
            exact mul_le_mul_of_nonneg_left hk1 (by positivity))
        · refine hfar.trans ?_
          rw [← ofReal_unitVol, ← ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_rpow_of_nonneg (by positivity) hθ0.le]
          refine ENNReal.ofReal_le_ofReal ?_
          refine le_of_le_of_eq (Real.rpow_le_rpow (y := 8 * L * 2 ^ d * unitVol d) (by positivity) ?_ hθ0.le) ?_
          · have : ((k : ℝ) + 2) * 2 ^ d * unitVol d ≤ 8 * L * 2 ^ d * unitVol d := by
              have := unitVol_pos d
              gcongr
            exact this
          · rw [show 8 * L * 2 ^ d * unitVol d = (8 * 2 ^ d * unitVol d) * L by ring,
              Real.mul_rpow (by have := unitVol_pos d; positivity) hL0.le]
    _ = ENNReal.ofReal (C2 d * T) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by
          have := unitVol_pos d; positivity) (by positivity)]
        congr 1
        unfold C2
        ring

end TrudingerV
end PDE
end

-- ==== from TrudDist.lean ====
-- Trudinger inequality on convex sets (diameter < 4): normalized majorant, Riesz bound,
-- distribution function.


@[expose] public section

open MeasureTheory Set
open PDE.Trudinger (C2 unitVol unitVol_pos measurable_norm_sub)
open scoped ENNReal

namespace PDE
namespace TrudingerV

variable {d : ℕ} {V : Set (Vec d)}

noncomputable def normalizedMajorant (V : Set (Vec d)) (G' : Vec d → ℝ) (N : ℝ) : Vec d → ℝ≥0∞ :=
  V.indicator fun y => ENNReal.ofReal (G' y / N)

theorem measurable_normalizedMajorant (hVm : MeasurableSet V) {G' : Vec d → ℝ} (hG : Measurable G') (N : ℝ) :
    Measurable (normalizedMajorant V G' N) :=
  (ENNReal.measurable_ofReal.comp (hG.div_const N)).indicator hVm

theorem normalizedMajorant_ne_top (G' : Vec d → ℝ) (N : ℝ) (y : Vec d) :
    normalizedMajorant V G' N y ≠ ⊤ := by
  unfold normalizedMajorant
  by_cases hy : y ∈ V <;> simp [Set.indicator_of_mem, hy]

theorem normalizedMajorant_ne_zero {G' : Vec d → ℝ} {N : ℝ} {y : Vec d}
    (h : normalizedMajorant V G' N y ≠ 0) : y ∈ V := by
  by_contra hy
  simp [normalizedMajorant, hy] at h

theorem lintegral_normalizedMajorant_rpow (hVm : MeasurableSet V) {G' : Vec d → ℝ} (hG : Measurable G')
    (_hnn : ∀ y, 0 ≤ G' y) {N : ℝ} (hN : 0 < N) (hd : 0 < (d : ℝ))
    (hLd : ∫⁻ y in V, ENNReal.ofReal (G' y) ^ (d : ℝ) = ENNReal.ofReal N ^ (d : ℝ)) :
    ∫⁻ y, normalizedMajorant V G' N y ^ (d : ℝ) ≤ 1 := by
  have h1 : ∫⁻ y, normalizedMajorant V G' N y ^ (d : ℝ) =
      ∫⁻ y in V, ENNReal.ofReal (G' y / N) ^ (d : ℝ) := by
    rw [← lintegral_indicator hVm]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ V
    · simp [normalizedMajorant, hy]
    · have hd0 : d ≠ 0 := by exact_mod_cast hd.ne'
      simp [normalizedMajorant, hy, hd0]
  rw [h1]
  have h2 : ∀ y, ENNReal.ofReal (G' y / N) ^ (d : ℝ) =
      ENNReal.ofReal (1 / N) ^ (d : ℝ) * ENNReal.ofReal (G' y) ^ (d : ℝ) := fun y => by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hd.le, ← ENNReal.ofReal_mul (by positivity),
      one_div, inv_mul_eq_div]
  simp_rw [h2]
  rw [lintegral_const_mul (f := fun y => ENNReal.ofReal (G' y) ^ (d : ℝ)) _
    ((ENNReal.measurable_ofReal.comp hG).pow_const _), hLd,
    ← ENNReal.mul_rpow_of_nonneg _ _ hd.le, ← ENNReal.ofReal_mul (by positivity)]
  simp [hN.ne', one_div]

theorem lintegral_normalizedMajorant_le (hVm : MeasurableSet V) {G' : Vec d → ℝ} (hG : Measurable G')
    (_hnn : ∀ y, 0 ≤ G' y) {N : ℝ} (hN : 0 < N) (θ : ℝ)
    (hL1 : ∫⁻ y in V, ENNReal.ofReal (G' y) ≤
      ENNReal.ofReal N * volume (V) ^ θ) :
    ∫⁻ y, normalizedMajorant V G' N y ≤ volume (V) ^ θ := by
  have h1 : ∫⁻ y, normalizedMajorant V G' N y =
      ∫⁻ y in V, ENNReal.ofReal (G' y / N) := by
    rw [← lintegral_indicator hVm]
    rfl
  rw [h1]
  have h2 : ∀ y, ENNReal.ofReal (G' y / N) = ENNReal.ofReal (1 / N) * ENNReal.ofReal (G' y) :=
    fun y => by
      rw [← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_eq_div]
  simp_rw [h2]
  rw [lintegral_const_mul (f := fun y => ENNReal.ofReal (G' y)) _
    (ENNReal.measurable_ofReal.comp hG)]
  calc _ ≤ ENNReal.ofReal (1 / N) * (ENNReal.ofReal N * volume (V) ^ θ) :=
        mul_le_mul' le_rfl hL1
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        simp [hN.ne']

/-- Averages of the normalized majorant over balls centered at a point where the maximal
function is at most `m` are at most `m`. -/
theorem lintegral_ball_normalizedMajorant_le {G' : Vec d → ℝ} (_hG : Measurable G')
    (_hnn : ∀ y, 0 ≤ G' y) {N : ℝ} (_hN : 0 < N) {m : ℝ} (x : Vec d)
    (hM : uncenteredBallMaximal (fun y => (normalizedMajorant V G' N y).toReal) x ≤
      ENNReal.ofReal m) (ρ : ℝ) (hρ : 0 < ρ) :
    ∫⁻ y in euclideanBall x ρ, normalizedMajorant V G' N y ≤
      ENNReal.ofReal m * volume (euclideanBall x ρ) := by
  have hx : x ∈ euclideanBall x ρ := by
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hρ]
    simpa [vecEuclideanNorm, vecNormSq, vecDot] using hρ
  have h := (lintegralAverage_le_uncenteredBallMaximal
    (fun y => (normalizedMajorant V G' N y).toReal) hρ hx).trans hM
  have hfb : ∀ y, ENNReal.ofReal |(normalizedMajorant V G' N y).toReal| =
      normalizedMajorant V G' N y := fun y => by
    rw [abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (normalizedMajorant_ne_top _ _ _)]
  simp_rw [hfb] at h
  have hpos := volume_euclideanBall_pos x hρ
  have hfin := volume_euclideanBall_ne_top x hρ.le
  calc _ = volume (euclideanBall x ρ) *
        ((volume (euclideanBall x ρ))⁻¹ * ∫⁻ y in euclideanBall x ρ, normalizedMajorant V G' N y) := by
        rw [ENNReal.mul_inv_cancel_left hpos.ne' hfin]
    _ ≤ volume (euclideanBall x ρ) * ENNReal.ofReal m := mul_le_mul_right h _
    _ = _ := mul_comm _ _

/-- The real Riesz potential of `G'` at a point of `B₁` where the maximal function of `G'/N` is at
most `m` is at most `N C₂ (log (2 + m))^{(d-1)/d}`. -/
theorem integral_riesz_le_log (hd : 2 ≤ d) (hVm : MeasurableSet V)
    (hVD : ∀ x ∈ V, ∀ y ∈ V, vecEuclideanNorm (x - y) < 4) {G' : Vec d → ℝ} (hG : Measurable G')
    (hnn : ∀ y, 0 ≤ G' y) {N : ℝ} (hN : 0 < N)
    (hLd : ∫⁻ y in V, ENNReal.ofReal (G' y) ^ (d : ℝ) = ENNReal.ofReal N ^ (d : ℝ))
    {x : Vec d} (hx : x ∈ V) {m : ℝ} (hm : 0 < m)
    (hM : uncenteredBallMaximal (fun y => (normalizedMajorant V G' N y).toReal) x ≤
      ENNReal.ofReal m) :
    ∫ y in V, vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) * G' y ≤
      N * (C2 d * Real.log (2 + m) ^ (((d : ℝ) - 1) / d)) := by
  have hd0 : (0 : ℝ) < d := by have : (2 : ℝ) ≤ d := by exact_mod_cast hd
                               linarith
  have hJ := lintegral_riesz_le_log hd x (measurable_normalizedMajorant hVm hG N)
    (lintegral_normalizedMajorant_rpow hVm hG hnn hN hd0 hLd)
    (fun y hy => hVD x hx y (normalizedMajorant_ne_zero hy)) hm
    (lintegral_ball_normalizedMajorant_le hG hnn hN x hM)
  set K : Vec d → ℝ := fun y => vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) with hK
  have hKnn : ∀ y, 0 ≤ K y := fun y => Real.rpow_nonneg (vecEuclideanNorm_nonneg _) _
  have hKm : Measurable K := (measurable_norm_sub x).pow_const _
  have hB := hVm
  have hint : ∫ y in V, K y * G' y =
      (∫⁻ y in V, ENNReal.ofReal (K y * G' y)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y =>
      mul_nonneg (hKnn y) (hnn y)) (hKm.mul hG).aestronglyMeasurable
  have hlin : ∫⁻ y in V, ENNReal.ofReal (K y * G' y) =
      ENNReal.ofReal N * ∫⁻ y, ENNReal.ofReal (K y) * normalizedMajorant V G' N y := by
    rw [← lintegral_const_mul (f := fun y => ENNReal.ofReal (K y) * normalizedMajorant V G' N y) _
      ((ENNReal.measurable_ofReal.comp hKm).mul (measurable_normalizedMajorant hVm hG N)),
      ← lintegral_indicator hB]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ V
    · simp only [normalizedMajorant, Set.indicator_of_mem hy]
      rw [← ENNReal.ofReal_mul (hKnn y), ← ENNReal.ofReal_mul hN.le]
      congr 1
      field_simp
    · simp [normalizedMajorant, hy]
  have hnonneg : 0 ≤ N * (C2 d * Real.log (2 + m) ^ (((d : ℝ) - 1) / d)) := by
    have hlog : 0 ≤ Real.log (2 + m) := Real.log_nonneg (by linarith)
    have hu := unitVol_pos d
    unfold C2
    positivity
  change ∫ y in V, K y * G' y ≤ _
  rw [hint, hlin]
  refine ENNReal.toReal_le_of_le_ofReal hnonneg ?_
  calc ENNReal.ofReal N * ∫⁻ y, ENNReal.ofReal (K y) * normalizedMajorant V G' N y
      ≤ ENNReal.ofReal N * ENNReal.ofReal (C2 d * Real.log (2 + m) ^ (((d : ℝ) - 1) / d)) :=
        mul_le_mul' le_rfl hJ
    _ = _ := (ENNReal.ofReal_mul hN.le).symm

/-- The Riesz-potential constant `c₁ = 2^d / (d |B₁|)`. -/
noncomputable def rieszConst (V : Set (Vec d)) : ℝ := 4 ^ d / (d * (volume V).toReal)

/-- The constant of the Trudinger inequality. -/
noncomputable def trudingerConst (V : Set (Vec d)) : ℝ :=
  max (max (2 * 3 ^ d * (volume V).toReal ^ (((d : ℝ) - 1) / d)) (4 * (volume V).toReal))
    ((rieszConst V * C2 d) ^ ((d : ℝ) / ((d : ℝ) - 1)))

theorem trudingerConst_pos (hVpos : 0 < (volume V).toReal) : 0 < trudingerConst V := by
  exact lt_max_of_lt_left (lt_max_of_lt_right (by positivity))

theorem distribution_le (hd : 2 ≤ d) (hVm : MeasurableSet V) (hVfin : volume V ≠ ⊤)
    (hVpos : 0 < volume V)
    (hVD : ∀ x ∈ V, ∀ y ∈ V, vecEuclideanNorm (x - y) < 4) {G' : Vec d → ℝ} (hG : Measurable G')
    (hnn : ∀ y, 0 ≤ G' y) {N : ℝ} (hN : 0 < N)
    (hLd : ∫⁻ y in V, ENNReal.ofReal (G' y) ^ (d : ℝ) = ENNReal.ofReal N ^ (d : ℝ))
    (hL1 : ∫⁻ y in V, ENNReal.ofReal (G' y) ≤
      ENNReal.ofReal N * volume (V) ^ (((d : ℝ) - 1) / d))
    {w : Vec d → ℝ}
    (hw : ∀ᵐ x ∂volumeOn (V), w x ≤ rieszConst V *
      ∫ y in V, vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) * G' y)
    {t : ℝ} (ht : 0 < t) :
    (volume {z | z ∈ V ∧ t < w z}).toReal ≤
      trudingerConst V * Real.exp (-(1 / trudingerConst V) *
        (t / N) ^ ((d : ℝ) / ((d : ℝ) - 1))) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hv := unitVol_pos d
  have hvV : 0 < (volume V).toReal := ENNReal.toReal_pos hVpos.ne' hVfin
  set θ : ℝ := ((d : ℝ) - 1) / d with hθ
  set q : ℝ := (d : ℝ) / ((d : ℝ) - 1) with hq
  have hθ0 : 0 < θ := div_pos hd1 (by linarith)
  have hq0 : 0 < q := div_pos (by linarith) hd1
  have hqθ : q * θ = 1 := by rw [hθ, hq]; field_simp
  set c1 := rieszConst V with hc1
  have hc1pos : 0 < c1 := by rw [hc1, rieszConst]; positivity
  have hC2pos : 0 < C2 d := by unfold C2; positivity
  set C1 : ℝ := c1 * C2 d with hC1
  have hC1pos : 0 < C1 := mul_pos hc1pos hC2pos
  set C := trudingerConst V with hC
  have hCpos : 0 < C := trudingerConst_pos hvV
  have hCa : 2 * 3 ^ d * (volume V).toReal ^ θ ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCb : 4 * (volume V).toReal ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCc : C1 ^ q ≤ C := le_max_right _ _
  -- the exponent comparison
  set y : ℝ := (t / (N * C1)) ^ q with hy
  have hy0 : 0 ≤ y := by positivity
  have hyle : (1 / C) * (t / N) ^ q ≤ y := by
    have h1 : y = (t / N) ^ q / C1 ^ q := by
      rw [hy, ← Real.div_rpow (by positivity) hC1pos.le]
      congr 1; field_simp
    rw [h1, one_div_mul_eq_div]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hCc
  have hexp : Real.exp (-y) ≤ Real.exp (-(1 / C) * (t / N) ^ q) := by
    apply Real.exp_le_exp.2
    nlinarith
  by_cases hyc : y < Real.log 4
  · -- small `t`
    have hXle : (volume {z | z ∈ V ∧ t < w z}).toReal ≤ (volume V).toReal := by
      refine ENNReal.toReal_mono hVfin ?_
      exact measure_mono fun z hz => hz.1
    have h4 : 1 / 4 ≤ Real.exp (-y) := by
      have : Real.exp (-Real.log 4) ≤ Real.exp (-y) := Real.exp_le_exp.2 (by linarith)
      rwa [Real.exp_neg, Real.exp_log (by norm_num), ← one_div] at this
    calc _ ≤ (volume V).toReal := hXle
      _ ≤ C * Real.exp (-y) := by nlinarith
      _ ≤ _ := by gcongr
  · -- large `t`
    have hyc' : Real.log 4 ≤ y := not_lt.mp hyc
    have hey : 4 ≤ Real.exp y := by
      have := Real.exp_le_exp.2 hyc'
      rwa [Real.exp_log (by norm_num)] at this
    set m : ℝ := Real.exp y - 2 with hm
    have hm0 : 0 < m := by linarith
    have hmhalf : Real.exp y / 2 ≤ m := by linarith
    set f := normalizedMajorant V G' N with hf
    set b : Vec d → ℝ := fun y => (f y).toReal with hb
    set M := uncenteredBallMaximal b with hMdef
    have hfm : Measurable f := measurable_normalizedMajorant hVm hG N
    have hL1' := lintegral_normalizedMajorant_le hVm hG hnn hN θ hL1
    have hfin : ∫⁻ y, f y ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.rpow_ne_top_of_nonneg hθ0.le
        hVfin) hL1'
    have hbint : Integrable b volume :=
      integrable_toReal_of_lintegral_ne_top hfm.aemeasurable hfin
    have hbabs : ∫ x, |b x| ∂volume ≤ (volume V).toReal ^ θ := by
      have : ∫ x, |b x| ∂volume = ∫ x, b x ∂volume :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => abs_of_nonneg ENNReal.toReal_nonneg)
      rw [this, hb, integral_toReal hfm.aemeasurable (Filter.Eventually.of_forall fun x =>
        lt_top_iff_ne_top.2 (normalizedMajorant_ne_top _ _ _))]
      have := ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg hθ0.le
        hVfin) hL1'
      rw [← ENNReal.toReal_rpow] at this
      exact this
    have hweak := volume_set_lt_uncenteredBallMaximal_le b m hm0 hbint
    -- the exceptional set
    have hgood : ∀ᵐ x ∂volume, x ∈ V → w x ≤ c1 *
        ∫ y in V, vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) * G' y :=
      (ae_restrict_iff' hVm).1 hw
    have hsub : {z | z ∈ V ∧ t < w z} ⊆
        {x | ENNReal.ofReal m < M x} ∪ {x | ¬ (x ∈ V → w x ≤ c1 *
          ∫ y in V, vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) * G' y)} := by
      rintro z ⟨hzB, hzt⟩
      by_cases hz : z ∈ V → w z ≤ c1 *
          ∫ y in V, vecEuclideanNorm (z - y) ^ ((1 : ℝ) - d) * G' y
      · left
        by_contra hM
        have hM' : M z ≤ ENNReal.ofReal m := not_lt.mp hM
        have hI := integral_riesz_le_log hd hVm hVD hG hnn hN hLd hzB hm0 hM'
        have hlog : Real.log (2 + m) = y := by
          rw [hm, show 2 + (Real.exp y - 2) = Real.exp y by ring, Real.log_exp]
        rw [hlog] at hI
        have hyθ : y ^ θ = t / (N * C1) := by
          rw [hy, ← Real.rpow_mul (by positivity), hqθ, Real.rpow_one]
        rw [hyθ] at hI
        have hwz := hz hzB
        have : w z ≤ t := by
          calc w z ≤ c1 * (N * (C2 d * (t / (N * C1)))) :=
                hwz.trans (mul_le_mul_of_nonneg_left hI hc1pos.le)
            _ = t := by rw [hC1]; field_simp
        linarith
      · right; exact hz
    have hnull : volume {x | ¬ (x ∈ V → w x ≤ c1 *
          ∫ y in V, vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) * G' y)} = 0 :=
      ae_iff.1 hgood
    have hvol : volume {z | z ∈ V ∧ t < w z} ≤
        ENNReal.ofReal (3 ^ d / m * ∫ x, |b x| ∂volume) := by
      calc _ ≤ volume ({x | ENNReal.ofReal m < M x} ∪ {x | ¬ (x ∈ V → w x ≤ c1 *
          ∫ y in V, vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) * G' y)}) :=
            measure_mono hsub
        _ ≤ volume {x | ENNReal.ofReal m < M x} + 0 := by
            rw [← hnull]; exact measure_union_le _ _
        _ ≤ _ := by rw [add_zero]; exact hweak
    have hnn' : 0 ≤ 3 ^ d / m * ∫ x, |b x| ∂volume :=
      mul_nonneg (by positivity) (integral_nonneg fun x => abs_nonneg _)
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
    rw [ENNReal.toReal_ofReal hnn'] at hreal
    have hexpy : 0 < Real.exp y := Real.exp_pos y
    calc _ ≤ 3 ^ d / m * ∫ x, |b x| ∂volume := hreal
      _ ≤ 3 ^ d / (Real.exp y / 2) * (volume V).toReal ^ θ := by
          gcongr
      _ = 2 * 3 ^ d * (volume V).toReal ^ θ * Real.exp (-y) := by
          rw [Real.exp_neg]; field_simp
      _ ≤ C * Real.exp (-y) := by gcongr
      _ ≤ _ := by gcongr

end TrudingerV
end PDE
end

-- ==== from TrudMain.lean ====
-- Trudinger inequality on bounded open convex sets of Euclidean diameter < 4
-- (generalization of `PDE.Trudinger.exists_trudinger_constant_full` from the unit ball).


@[expose] public section

open MeasureTheory Set PDE
open scoped ENNReal

namespace PDE
namespace TrudingerV

/-- The Trudinger inequality (Proposition 1.18). -/
theorem trudinger_V_const (d : ℕ) (hd : 2 ≤ d) {V : Set (Vec d)}
    (hUopen : IsOpenBoundedConvexDomain V) (hvolpos : 0 < volume V)
    (hVD : ∀ x ∈ V, ∀ y ∈ V, vecEuclideanNorm (x - y) < 4) :
    ∀ u : W1pFunction (V) (ENNReal.ofReal d),
      ∀ t : ℝ, 0 < t →
        (volume {z ∈ V |
            t < |u.toFun z - integralAverage (V) u.toFun|}).toReal ≤
          (if (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal d)
                (volumeOn (V))).toReal = 0 then 0 else
            trudingerConst V * Real.exp (-(1 / trudingerConst V) * (t / (eLpNorm (fun x => vecEuclideanNorm (u.grad x))
                (ENNReal.ofReal d) (volumeOn (V))).toReal) ^
                ((d : ℝ) / ((d : ℝ) - 1)))) := by
  have hvolne : volume V ≠ ⊤ := hUopen.volume_lt_top.ne
  have hvV : 0 < (volume V).toReal := ENNReal.toReal_pos hvolpos.ne' hvolne
  intro u t ht
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hB : MeasurableSet V := hUopen.isOpen.measurableSet
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal d := ENNReal.one_le_ofReal.2 (by linarith)
  have hpne : ENNReal.ofReal d ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp0 : ENNReal.ofReal d ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  set G : Vec d → ℝ := fun x => vecEuclideanNorm (u.grad x) with hGdef
  have hGmem : MemLp G (ENNReal.ofReal d) (volumeOn (V)) :=
    u.gradMemLp.memLp_vecEuclideanNorm
  set E := eLpNorm G (ENNReal.ofReal d) (volumeOn (V)) with hE
  have hEne : E ≠ ⊤ := hGmem.eLpNorm_ne_top
  change _ ≤ (if E.toReal = 0 then 0 else _)
  split_ifs with hN0
  · -- vanishing gradient
    have hE0 : E = 0 := by
      rcases ENNReal.toReal_eq_zero_iff _ |>.1 hN0 with h | h
      · exact h
      · exact absurd h hEne
    have hG0 : G =ᵐ[volumeOn (V)] 0 :=
      (eLpNorm_eq_zero_iff hp0).1 hE0
    have hgrad : u.grad =ᵐ[volumeOn (V)] 0 := by
      filter_upwards [hG0] with x hx
      exact vecEuclideanNorm_eq_zero_iff.1 hx
    have hconst := W1pFunction.ae_eq_integralAverage_of_grad_ae_eq_zero hp1 hpne hUopen hvolpos
      (lt_top_iff_ne_top.2 hvolne) u hgrad
    have hae := (ae_restrict_iff' hB).1 hconst
    have hnull : volume {z | z ∈ V ∧ t < |u.toFun z - integralAverage (V) u.toFun|}
        = 0 := by
      refine measure_mono_null (fun z hz => ?_) (ae_iff.1 hae)
      intro hzz
      obtain ⟨hz1, hz2⟩ := hz
      rw [hzz hz1, sub_self, abs_zero] at hz2
      linarith
    change (volume {z | z ∈ V ∧ t < |u.toFun z - integralAverage (V) u.toFun|}).toReal
      ≤ 0
    rw [hnull]; simp
  · have hNpos : 0 < E.toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hN0)
    set N := E.toReal with hNdef
    have hEN : E = ENNReal.ofReal N := (ENNReal.ofReal_toReal hEne).symm
    -- measurable nonnegative representative of the gradient magnitude
    have hmeas : AEMeasurable G (volumeOn (V)) := hGmem.aestronglyMeasurable.aemeasurable
    set G' : Vec d → ℝ := fun y => |hmeas.mk G y| with hG'def
    have hG'm : Measurable G' := continuous_abs.measurable.comp hmeas.measurable_mk
    have hG'nn : ∀ y, 0 ≤ G' y := fun y => abs_nonneg _
    have hGG' : G' =ᵐ[volumeOn (V)] G := by
      filter_upwards [hmeas.ae_eq_mk] with y hy
      simp only [hG'def, ← hy]
      exact abs_of_nonneg (vecEuclideanNorm_nonneg _)
    have hLd : ∫⁻ y in V, ENNReal.ofReal (G' y) ^ (d : ℝ) =
        ENNReal.ofReal N ^ (d : ℝ) := by
      have h1 : ∫⁻ y in V, ENNReal.ofReal (G' y) ^ (d : ℝ) =
          ∫⁻ y, ‖G y‖ₑ ^ (d : ℝ) ∂(volumeOn (V)) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hGG'] with y hy
        rw [hy, Real.enorm_eq_ofReal (vecEuclideanNorm_nonneg _)]
      rw [h1, lintegral_rpow_enorm_eq_rpow_eLpNorm' hd0, ← hEN, hE,
        eLpNorm_eq_eLpNorm' hp0 hpne hGmem.aestronglyMeasurable, ENNReal.toReal_ofReal hd0.le]
    have hL1 : ∫⁻ y in V, ENNReal.ofReal (G' y) ≤
        ENNReal.ofReal N * volume (V) ^ (((d : ℝ) - 1) / d) := by
      have h1 : ∫⁻ y in V, ENNReal.ofReal (G' y) =
          eLpNorm G 1 (volumeOn (V)) := by
        rw [eLpNorm_one_eq_lintegral_enorm hGmem.aestronglyMeasurable]
        refine lintegral_congr_ae ?_
        filter_upwards [hGG'] with y hy
        rw [hy, Real.enorm_eq_ofReal (vecEuclideanNorm_nonneg _)]
      rw [h1]
      refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp1 hGmem.aestronglyMeasurable).trans ?_
      rw [Measure.restrict_apply_univ, ENNReal.toReal_ofReal hd0.le]
      simp only [ENNReal.toReal_one, div_one]
      have : (1 : ℝ) - 1 / d = ((d : ℝ) - 1) / d := by field_simp
      rw [this]
      exact mul_le_mul' (le_of_eq (hE.symm.trans hEN)) le_rfl
    -- Riesz bound
    have hRiesz := abs_sub_integralAverage_ae_le_riesz (V := V) (S := V)
      (D := 4) hUopen (fun x hx y hy => (hVD x hx y hy).le)
      (Ch1Bridges.W1pFunction.lower (U := V) hvolne hp1 u) hB
      subset_rfl hvolpos
    have hw : ∀ᵐ x ∂volumeOn (V),
        |u.toFun x - integralAverage (V) u.toFun| ≤ rieszConst V *
          ∫ y in V, vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) * G' y := by
      filter_upwards [hRiesz] with x hx
      have hI : ∫ y in V, vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) * G' y =
          ∫ y in V, vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) *
            vecEuclideanNorm (u.grad y) := by
        refine integral_congr_ae ?_
        filter_upwards [hGG'] with y hy
        rw [hy]
      rw [hI]
      have hc : (4 : ℝ) ^ d / (d * (volume V).toReal) = rieszConst V := rfl
      simpa only [Ch1Bridges.W1pFunction.lower_toFun, Ch1Bridges.W1pFunction.lower_grad, hc] using hx
    exact distribution_le hd hB hvolne hvolpos hVD hG'm hG'nn hNpos hLd hL1 hw ht

theorem exists_trudinger_constant_V (d : ℕ) (hd : 2 ≤ d) {V : Set (Vec d)}
    (hUopen : IsOpenBoundedConvexDomain V) (hvolpos : 0 < volume V)
    (hVD : ∀ x ∈ V, ∀ y ∈ V, vecEuclideanNorm (x - y) < 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : W1pFunction (V) (ENNReal.ofReal d),
      ∀ t : ℝ, 0 < t →
        (volume {z ∈ V |
            t < |u.toFun z - integralAverage (V) u.toFun|}).toReal ≤
          (if (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal d)
                (volumeOn (V))).toReal = 0 then 0 else
            C * Real.exp (-(1 / C) * (t / (eLpNorm (fun x => vecEuclideanNorm (u.grad x))
                (ENNReal.ofReal d) (volumeOn (V))).toReal) ^
                ((d : ℝ) / ((d : ℝ) - 1)))) :=
  ⟨trudingerConst V, trudingerConst_pos (ENNReal.toReal_pos hvolpos.ne' hUopen.volume_lt_top.ne),
    trudinger_V_const d hd hUopen hvolpos hVD⟩

end TrudingerV
end PDE
end

-- ==== from TrudSqrtA.lean ====
-- From a sub-Gaussian tail bound to an `L^q` bound with the optimal growth `√q`.


@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace PDE.TrudingerV

lemma rpow_le_mul_exp {m x : ℝ} (hm : 0 < m) (hx : 0 ≤ x) :
    x ^ m ≤ (m / Real.exp 1) ^ m * Real.exp x := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [Real.zero_rpow hm.ne']; positivity
  · have h := Real.log_le_sub_one_of_pos (div_pos hx hm)
    rw [Real.log_div hx.ne' hm.ne'] at h
    have h2 : (Real.log x - Real.log m) * m ≤ (x / m - 1) * m :=
      mul_le_mul_of_nonneg_right h hm.le
    have h3 : (x / m - 1) * m = x - m := by field_simp
    rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos (div_pos hm (Real.exp_pos 1)),
      Real.log_div hm.ne' (Real.exp_pos 1).ne', Real.log_exp, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith

lemma rpow_le_exp_sq {q a t : ℝ} (hq : 0 < q) (ha : 0 < a) (ht : 0 ≤ t) :
    t ^ q ≤ (q / (2 * Real.exp 1 * a)) ^ (q / 2) * Real.exp (a * t ^ 2) := by
  have h := rpow_le_mul_exp (m := q / 2) (x := a * t ^ 2) (by positivity) (by positivity)
  have h0 : (t ^ 2) ^ (q / 2) = t ^ q := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
    congr 1; push_cast; ring
  have h1 : (a * t ^ 2) ^ (q / 2) = a ^ (q / 2) * t ^ q := by
    rw [Real.mul_rpow ha.le (by positivity), h0]
  have hapos : 0 < a ^ (q / 2) := Real.rpow_pos_of_pos ha _
  have e1 : (q / (2 * Real.exp 1 * a)) ^ (q / 2) =
      (q / 2 / Real.exp 1) ^ (q / 2) / a ^ (q / 2) := by
    rw [← Real.div_rpow (by positivity) ha.le]; congr 1; field_simp
  rw [e1, div_mul_eq_mul_div, le_div_iff₀ hapos]
  rw [h1] at h
  linarith

/-- The exponential moment bound: `∫ (exp (a w²) - 1) ≤ K` from a sub-Gaussian tail. -/
lemma lintegral_exp_sub_one_le {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {w : α → ℝ} (hw : AEMeasurable w μ) {K s a : ℝ} (hK : 0 < K) (hs : 0 < s)
    (ha : a = 1 / (2 * s ^ 2))
    (htail : ∀ t : ℝ, 0 < t → (μ {z | t < |w z|}).toReal ≤ K * Real.exp (-(t / s) ^ 2)) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (a * |w z| ^ 2) - 1) ∂μ ≤ ENNReal.ofReal K := by
  have ha0 : 0 < a := by rw [ha]; positivity
  have hder : ∀ t : ℝ, HasDerivAt (fun t => Real.exp (a * t ^ 2))
      (2 * a * t * Real.exp (a * t ^ 2)) t := by
    intro t
    have := ((hasDerivAt_pow 2 t).const_mul a).exp
    convert this using 1
    simp; ring
  have hgc : Continuous fun t : ℝ => 2 * a * t * Real.exp (a * t ^ 2) := by fun_prop
  have hint : ∀ T : ℝ, ∫ t in (0 : ℝ)..T, 2 * a * t * Real.exp (a * t ^ 2) =
      Real.exp (a * T ^ 2) - 1 := by
    intro T
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t)
      (hgc.intervalIntegrable _ _)]
    simp
  have hlc := lintegral_comp_eq_lintegral_meas_lt_mul μ (f := fun z => |w z|)
    (g := fun t => 2 * a * t * Real.exp (a * t ^ 2))
    (Filter.Eventually.of_forall fun z => abs_nonneg _) (continuous_abs.measurable.comp_aemeasurable hw)
    (fun t _ => hgc.intervalIntegrable _ _)
    (by
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
      have : 0 < t := ht
      positivity)
  simp only [hint] at hlc
  rw [hlc]
  -- pointwise bound of the integrand on (0, ∞)
  have hh : ∀ t : ℝ, 0 < t → μ {z | t < |w z|} * ENNReal.ofReal (2 * a * t * Real.exp (a * t ^ 2)) ≤
      ENNReal.ofReal K * ENNReal.ofReal (2 * a * t * Real.exp (-(a * t ^ 2))) := by
    intro t ht
    have h1 : μ {z | t < |w z|} ≤ ENNReal.ofReal (K * Real.exp (-(t / s) ^ 2)) :=
      (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).2 (htail t ht)
    have h2 : K * Real.exp (-(t / s) ^ 2) * (2 * a * t * Real.exp (a * t ^ 2)) =
        K * (2 * a * t * Real.exp (-(a * t ^ 2))) := by
      have : Real.exp (-(t / s) ^ 2) * Real.exp (a * t ^ 2) = Real.exp (-(a * t ^ 2)) := by
        rw [← Real.exp_add]; congr 1; rw [ha]; field_simp; ring
      calc K * Real.exp (-(t / s) ^ 2) * (2 * a * t * Real.exp (a * t ^ 2))
          = K * (2 * a * t) * (Real.exp (-(t / s) ^ 2) * Real.exp (a * t ^ 2)) := by ring
        _ = _ := by rw [this]; ring
    calc μ {z | t < |w z|} * ENNReal.ofReal (2 * a * t * Real.exp (a * t ^ 2))
        ≤ ENNReal.ofReal (K * Real.exp (-(t / s) ^ 2)) *
            ENNReal.ofReal (2 * a * t * Real.exp (a * t ^ 2)) := mul_le_mul' h1 le_rfl
      _ = ENNReal.ofReal (K * Real.exp (-(t / s) ^ 2) * (2 * a * t * Real.exp (a * t ^ 2))) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ = ENNReal.ofReal (K * (2 * a * t * Real.exp (-(a * t ^ 2)))) := by rw [h2]
      _ = _ := ENNReal.ofReal_mul hK.le
  have hG : ∀ t : ℝ, HasDerivAt (fun t => -Real.exp (-(a * t ^ 2)))
      (2 * a * t * Real.exp (-(a * t ^ 2))) t := by
    intro t
    have := (((hasDerivAt_pow 2 t).const_mul a).neg.exp).neg
    convert this using 1
    simp; ring
  have hlim : Tendsto (fun t : ℝ => -Real.exp (-(a * t ^ 2))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => -(a * t ^ 2)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp
        (Tendsto.const_mul_atTop ha0 (tendsto_pow_atTop two_ne_zero))
    have := (Real.tendsto_exp_atBot.comp h1).neg
    simpa using this
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ 2 * a * t * Real.exp (-(a * t ^ 2)) := by
    intro t ht
    have : 0 < t := ht
    positivity
  have hI := integrableOn_Ioi_deriv_of_nonneg' (a := 0) (fun t _ => hG t) hpos hlim
  have hIv : ∫ t in Ioi (0 : ℝ), 2 * a * t * Real.exp (-(a * t ^ 2)) = 1 := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => hG t) hI hlim]
    simp
  have hL : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (2 * a * t * Real.exp (-(a * t ^ 2))) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hI
      ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hpos)), hIv]
    simp
  calc ∫⁻ t in Ioi (0 : ℝ), μ {z | t < |w z|} * ENNReal.ofReal (2 * a * t * Real.exp (a * t ^ 2))
      ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal K *
          ENNReal.ofReal (2 * a * t * Real.exp (-(a * t ^ 2))) :=
        setLIntegral_mono' measurableSet_Ioi hh
    _ = ENNReal.ofReal K := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hL, mul_one]

end PDE.TrudingerV
end

-- ==== from TrudSqrtB.lean ====
-- `L^q` norm of a function with sub-Gaussian tail grows like `√q`.


@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace PDE.TrudingerV

theorem lq_of_tail {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {w : α → ℝ} (hw : AEMeasurable w μ) {K s : ℝ} (hK : 0 < K) (hs : 0 < s)
    (htail : ∀ t : ℝ, 0 < t → (μ {z | t < |w z|}).toReal ≤ K * Real.exp (-(t / s) ^ 2))
    {q : ℝ} (hq : 1 ≤ q) :
    (∫⁻ z, ENNReal.ofReal |w z| ^ q ∂μ) ^ (1 / q) ≤
      ENNReal.ofReal (max 1 ((μ Set.univ).toReal + K) * Real.sqrt q * s) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 / (2 * s ^ 2) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (q / (2 * Real.exp 1 * a)) ^ (q / 2) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; exact Real.rpow_nonneg (by positivity) _
  have hE := lintegral_exp_sub_one_le μ hw hK hs ha htail
  have hE2 : ∫⁻ z, ENNReal.ofReal (Real.exp (a * |w z| ^ 2)) ∂μ ≤
      ENNReal.ofReal K + μ univ := by
    have h1 : ∀ z, ENNReal.ofReal (Real.exp (a * |w z| ^ 2)) =
        ENNReal.ofReal (Real.exp (a * |w z| ^ 2) - 1) + 1 := fun z => by
      have h0 : 0 ≤ Real.exp (a * |w z| ^ 2) - 1 :=
        sub_nonneg.2 (Real.one_le_exp (by positivity))
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add h0 zero_le_one]
      congr 1; ring
    simp_rw [h1]
    rw [lintegral_add_right _ measurable_const, lintegral_const, one_mul]
    exact add_le_add hE le_rfl
  have hpt : ∀ z, ENNReal.ofReal |w z| ^ q ≤
      ENNReal.ofReal c * ENNReal.ofReal (Real.exp (a * |w z| ^ 2)) := by
    intro z
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq0.le, ← ENNReal.ofReal_mul hc0]
    exact ENNReal.ofReal_le_ofReal (by rw [hc]; exact rpow_le_exp_sq hq0 ha0 (abs_nonneg _))
  have hLq : ∫⁻ z, ENNReal.ofReal |w z| ^ q ∂μ ≤
      ENNReal.ofReal c * (ENNReal.ofReal K + μ univ) := by
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul' le_rfl hE2
  set m : ℝ := (μ univ).toReal with hm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have hX : ENNReal.ofReal c * (ENNReal.ofReal K + μ univ) = ENNReal.ofReal (c * (K + m)) := by
    rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_add hK.le hm0, hm,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hX] at hLq
  have hq1 : (0 : ℝ) ≤ 1 / q := by positivity
  refine (ENNReal.rpow_le_rpow hLq hq1).trans ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hq1]
  refine ENNReal.ofReal_le_ofReal ?_
  have hY0 : 0 ≤ K + m := by positivity
  rw [Real.mul_rpow hc0 hY0]
  -- the constant
  have h1 : c ^ (1 / q) ≤ Real.sqrt q * s := by
    have e1 : c ^ (1 / q) = (q / (2 * Real.exp 1 * a)) ^ (1 / 2 : ℝ) := by
      rw [hc, ← Real.rpow_mul (by positivity)]
      congr 1; field_simp
    rw [e1, ← Real.sqrt_eq_rpow]
    have e2 : q / (2 * Real.exp 1 * a) = q * s ^ 2 / Real.exp 1 := by
      rw [ha]; field_simp
    rw [e2]
    calc Real.sqrt (q * s ^ 2 / Real.exp 1) ≤ Real.sqrt (q * s ^ 2) := by
          apply Real.sqrt_le_sqrt
          have := Real.add_one_le_exp (1 : ℝ)
          exact div_le_self (by positivity) (by linarith)
      _ = Real.sqrt q * s := by
          rw [Real.sqrt_mul hq0.le, Real.sqrt_sq hs.le]
  have h2 : (K + m) ^ (1 / q) ≤ max 1 (m + K) := by
    rcases le_or_gt (K + m) 1 with h | h
    · exact (Real.rpow_le_one hY0 h hq1).trans (le_max_left _ _)
    · calc (K + m) ^ (1 / q) ≤ (K + m) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h.le (by rw [div_le_one hq0]; exact hq)
        _ = m + K := by rw [Real.rpow_one]; ring
        _ ≤ _ := le_max_right _ _
  calc c ^ (1 / q) * (K + m) ^ (1 / q) ≤ (Real.sqrt q * s) * max 1 (m + K) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = _ := by ring

end PDE.TrudingerV
end

-- ==== from TrudSqrtC.lean ====
-- `‖u - ū‖_{L^q(V)} ≤ C √q ‖∇u‖_{L²(V)}` on bounded open convex `V ⊂ ℝ²` of diameter `< 4`.


@[expose] public section

open MeasureTheory Set Filter Topology PDE
open scoped ENNReal

namespace PDE.TrudingerV

/-- The explicit constant of the `√q` Trudinger inequality. -/
noncomputable def sqrtConst {d : ℕ} (V : Set (Vec d)) : ℝ :=
  max 1 ((volume V).toReal + trudingerConst V) * Real.sqrt (trudingerConst V)

theorem sqrtConst_pos {V : Set (Vec 2)} (hUopen : IsOpenBoundedConvexDomain V)
    (hvolpos : 0 < volume V) : 0 < sqrtConst V := by
  have : 0 < trudingerConst V :=
    trudingerConst_pos (ENNReal.toReal_pos hvolpos.ne' hUopen.volume_lt_top.ne)
  unfold sqrtConst
  positivity

theorem trudinger_sqrt_V_const {V : Set (Vec 2)} (hUopen : IsOpenBoundedConvexDomain V)
    (hvolpos : 0 < volume V)
    (hVD : ∀ x ∈ V, ∀ y ∈ V, vecEuclideanNorm (x - y) < 4) :
    ∀ q : ℝ, 1 ≤ q → ∀ u : W1pFunction V (ENNReal.ofReal ((2 : ℕ) : ℝ)),
      (∫⁻ z in V, ENNReal.ofReal |u.toFun z - integralAverage V u.toFun| ^ q) ^ (1 / q) ≤
        ENNReal.ofReal (sqrtConst V * Real.sqrt q *
          (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal ((2 : ℕ) : ℝ))
            (volumeOn V)).toReal) := by
  have hvV : 0 < (volume V).toReal := ENNReal.toReal_pos hvolpos.ne' hUopen.volume_lt_top.ne
  have hC1 : 0 < trudingerConst V := trudingerConst_pos hvV
  have hT := trudinger_V_const 2 le_rfl hUopen hvolpos hVD
  obtain ⟨C1, hC1def⟩ : ∃ C1 : ℝ, C1 = trudingerConst V := ⟨_, rfl⟩
  rw [← hC1def] at hT hC1
  haveI : IsFiniteMeasure (volumeOn V) := hUopen.isFiniteMeasure_volumeOn
  have hVm : MeasurableSet V := hUopen.isOpen.measurableSet
  intro q hq u
  have hsc : sqrtConst V = max 1 ((volume V).toReal + C1) * Real.sqrt C1 := by
    rw [sqrtConst, hC1def]
  rw [hsc]
  have hq0 : 0 < q := by linarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (eLpNorm (fun x => vecEuclideanNorm (u.grad x))
      (ENNReal.ofReal ((2 : ℕ) : ℝ)) (volumeOn V)).toReal := ⟨_, rfl⟩
  rw [← hE]
  set w : Vec 2 → ℝ := fun z => u.toFun z - integralAverage V u.toFun with hw
  have hwm : AEMeasurable w (volumeOn V) :=
    (u.memLp.aestronglyMeasurable.aemeasurable).sub_const _
  have hset : ∀ t : ℝ, volumeOn V {z | t < |w z|} = volume {z | z ∈ V ∧ t < |w z|} := by
    intro t
    rw [Measure.restrict_apply' hVm]
    congr 1; ext z; simp [and_comm]
  have hT' := hT u
  by_cases hE0 : E = 0
  · -- vanishing gradient: `w = 0` a.e.
    have hnull : ∀ t : ℝ, 0 < t → volumeOn V {z | t < |w z|} = 0 := by
      intro t ht
      have h := hT' t ht
      rw [← hE, if_pos hE0] at h
      rw [hset]
      have hfin : volume {z | z ∈ V ∧ t < |w z|} ≠ ⊤ :=
        ne_top_of_le_ne_top hUopen.volume_lt_top.ne (measure_mono fun z hz => hz.1)
      exact (ENNReal.toReal_eq_zero_iff _ |>.1 (le_antisymm h ENNReal.toReal_nonneg)).resolve_right hfin
    have hae : ∀ᵐ z ∂(volumeOn V), |w z| = 0 := by
      have : volumeOn V {z | 0 < |w z|} = 0 := by
        have hU : {z | 0 < |w z|} = ⋃ n : ℕ, {z | (1 : ℝ) / (n + 1) < |w z|} := by
          ext z
          simp only [mem_setOf_eq, mem_iUnion]
          constructor
          · intro hz
            obtain ⟨n, hn⟩ := exists_nat_one_div_lt hz
            exact ⟨n, hn⟩
          · rintro ⟨n, hn⟩
            exact lt_trans (by positivity) hn
        rw [hU]
        exact measure_iUnion_null fun n => hnull _ (by positivity)
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 this] with z hz
      simp only [mem_setOf_eq, not_lt] at hz
      exact le_antisymm hz (abs_nonneg _)
    have h0 : ∫⁻ z, ENNReal.ofReal |w z| ^ q ∂(volumeOn V) = 0 := by
      rw [lintegral_eq_zero_iff' (by
        exact (ENNReal.measurable_ofReal.comp_aemeasurable
          (continuous_abs.measurable.comp_aemeasurable hwm)).pow_const q)]
      filter_upwards [hae] with z hz
      simp [hz, hq0]
    change (∫⁻ z, ENNReal.ofReal |w z| ^ q ∂(volumeOn V)) ^ (1 / q) ≤ _
    rw [h0, ENNReal.zero_rpow_of_pos (by positivity)]
    exact bot_le
  · have hEpos : 0 < E := by
      have : 0 ≤ E := by rw [hE]; exact ENNReal.toReal_nonneg
      exact lt_of_le_of_ne this (Ne.symm hE0)
    have hs : 0 < Real.sqrt C1 * E := by positivity
    have htail : ∀ t : ℝ, 0 < t → (volumeOn V {z | t < |w z|}).toReal ≤
        C1 * Real.exp (-(t / (Real.sqrt C1 * E)) ^ 2) := by
      intro t ht
      have h := hT' t ht
      rw [← hE, if_neg hE0] at h
      rw [hset]
      refine h.trans (le_of_eq ?_)
      congr 2
      have h2 : ((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) - 1) = 2 := by norm_num
      rw [h2, Real.rpow_two]
      simp only [div_pow, mul_pow, Real.sq_sqrt hC1.le]
      field_simp
    have := lq_of_tail (volumeOn V) hwm hC1 hs htail hq
    change (∫⁻ z, ENNReal.ofReal |w z| ^ q ∂(volumeOn V)) ^ (1 / q) ≤ _
    refine this.trans (le_of_eq ?_)
    congr 1
    rw [Measure.restrict_apply_univ]
    ring

theorem trudinger_sqrt_V {V : Set (Vec 2)} (hUopen : IsOpenBoundedConvexDomain V)
    (hvolpos : 0 < volume V)
    (hVD : ∀ x ∈ V, ∀ y ∈ V, vecEuclideanNorm (x - y) < 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 1 ≤ q → ∀ u : W1pFunction V (ENNReal.ofReal ((2 : ℕ) : ℝ)),
      (∫⁻ z in V, ENNReal.ofReal |u.toFun z - integralAverage V u.toFun| ^ q) ^ (1 / q) ≤
        ENNReal.ofReal (C * Real.sqrt q *
          (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal ((2 : ℕ) : ℝ))
            (volumeOn V)).toReal) :=
  ⟨sqrtConst V, sqrtConst_pos hUopen hvolpos, trudinger_sqrt_V_const hUopen hvolpos hVD⟩

end PDE.TrudingerV
end

-- ==== from TrudSqrtD.lean ====
-- Adding the mean: `‖u‖_{L^q(V)} ≤ C √q (‖u‖_{L²(V)} + ‖∇u‖_{L²(V)})` on convex `V ⊂ ℝ²`.


@[expose] public section

open MeasureTheory Set Filter Topology PDE
open scoped ENNReal

namespace PDE.TrudingerV

/-- The explicit constant of the `√q` Sobolev inequality. -/
noncomputable def sobConst (V : Set (Vec 2)) : ℝ :=
  max (sqrtConst V) ((volume V).toReal ^ (-(1 : ℝ) / 2) * max 1 (volume V).toReal)

theorem sobConst_pos {V : Set (Vec 2)} (hUopen : IsOpenBoundedConvexDomain V)
    (hvolpos : 0 < volume V) : 0 < sobConst V :=
  lt_max_of_lt_left (sqrtConst_pos hUopen hvolpos)

theorem sobolev_sqrt_V_const {V : Set (Vec 2)} (hUopen : IsOpenBoundedConvexDomain V)
    (hvolpos : 0 < volume V)
    (hVD : ∀ x ∈ V, ∀ y ∈ V, vecEuclideanNorm (x - y) < 4) :
    ∀ q : ℝ, 1 ≤ q → ∀ u : W1pFunction V (ENNReal.ofReal ((2 : ℕ) : ℝ)),
      (∫⁻ z in V, ENNReal.ofReal |u.toFun z| ^ q) ^ (1 / q) ≤
        ENNReal.ofReal (sobConst V * Real.sqrt q *
          ((eLpNorm u.toFun (ENNReal.ofReal ((2 : ℕ) : ℝ)) (volumeOn V)).toReal +
           (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal ((2 : ℕ) : ℝ))
            (volumeOn V)).toReal)) := by
  have hC0 := sqrtConst_pos hUopen hvolpos
  have hS := trudinger_sqrt_V_const hUopen hvolpos hVD
  obtain ⟨C0, hC0def⟩ : ∃ C0 : ℝ, C0 = sqrtConst V := ⟨_, rfl⟩
  rw [← hC0def] at hS hC0
  haveI : IsFiniteMeasure (volumeOn V) := hUopen.isFiniteMeasure_volumeOn
  have hVfin : volume V ≠ ⊤ := hUopen.volume_lt_top.ne
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (volume V).toReal := ⟨_, rfl⟩
  have hmpos : 0 < m := by rw [hm]; exact ENNReal.toReal_pos hvolpos.ne' hVfin
  intro q hq u
  have hsc : sobConst V = max C0 (m ^ (-(1 : ℝ) / 2) * max 1 m) := by
    rw [sobConst, hC0def, hm]
  rw [hsc]
  have hq0 : 0 < q := by linarith
  have hsq : 1 ≤ Real.sqrt q := Real.one_le_sqrt.2 hq
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (eLpNorm u.toFun (ENNReal.ofReal ((2 : ℕ) : ℝ))
      (volumeOn V)).toReal := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (eLpNorm (fun x => vecEuclideanNorm (u.grad x))
      (ENNReal.ofReal ((2 : ℕ) : ℝ)) (volumeOn V)).toReal := ⟨_, rfl⟩
  rw [← hN, ← hE]
  have hN0 : 0 ≤ N := by rw [hN]; exact ENNReal.toReal_nonneg
  have hE0 : 0 ≤ E := by rw [hE]; exact ENNReal.toReal_nonneg
  have hmeas : AEStronglyMeasurable u.toFun (volumeOn V) := u.memLp.aestronglyMeasurable
  obtain ⟨abar, habar⟩ : ∃ a : ℝ, a = integralAverage V u.toFun := ⟨_, rfl⟩
  -- the mean is controlled by the `L²` norm
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((2 : ℕ) : ℝ) :=
    ENNReal.one_le_ofReal.2 (by norm_num)
  have hint : Integrable u.toFun (volumeOn V) :=
    (u.memLp : MemLp u.toFun _ (volumeOn V)).integrable hp1
  have hL1 : ∫ x in V, ‖u.toFun x‖ = (eLpNorm u.toFun 1 (volumeOn V)).toReal := by
    rw [integral_norm_eq_lintegral_enorm hmeas, eLpNorm_one_eq_lintegral_enorm]
    all_goals exact hmeas
  have hL1le : (eLpNorm u.toFun 1 (volumeOn V)).toReal ≤ N * m ^ (1 / 2 : ℝ) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp1 hmeas
    have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top
      (u.memLp : MemLp u.toFun _ (volumeOn V)).eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _))) h
    rw [ENNReal.toReal_mul, ← hN, ← ENNReal.toReal_rpow, Measure.restrict_apply_univ, ← hm] at h'
    have e : (1 / (1 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal ((2 : ℕ) : ℝ)).toReal) = 1 / 2 := by
      rw [ENNReal.toReal_one, ENNReal.toReal_ofReal (by norm_num)]; norm_num
    rw [e] at h'
    exact h'
  have hmean : |abar| ≤ m ^ (-(1 : ℝ) / 2) * N := by
    have e1 : abar = m⁻¹ * ∫ x in V, u.toFun x := by rw [habar, integralAverage, ← hm]
    have h1 : |∫ x in V, u.toFun x| ≤ N * m ^ (1 / 2 : ℝ) := by
      calc |∫ x in V, u.toFun x| = ‖∫ x in V, u.toFun x‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ x in V, ‖u.toFun x‖ := norm_integral_le_integral_norm _
        _ ≤ _ := by rw [hL1]; exact hL1le
    have e2 : m ^ (1 / 2 : ℝ) = m ^ (-(1 : ℝ) / 2) * m := by
      rw [← Real.rpow_add_one hmpos.ne']; norm_num
    rw [e1, abs_mul, abs_of_pos (inv_pos.2 hmpos)]
    calc m⁻¹ * |∫ x in V, u.toFun x| ≤ m⁻¹ * (N * m ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hmpos.le)
      _ = m ^ (-(1 : ℝ) / 2) * N := by rw [e2]; field_simp
  -- Minkowski
  have hw : AEMeasurable (fun z => u.toFun z - abar) (volumeOn V) := hmeas.aemeasurable.sub_const _
  have hf : AEMeasurable (fun z => ENNReal.ofReal |u.toFun z - abar|) (volumeOn V) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (continuous_abs.measurable.comp_aemeasurable hw)
  have hg : AEMeasurable (fun _ : Vec 2 => ENNReal.ofReal |abar|) (volumeOn V) :=
    aemeasurable_const
  have hM := ENNReal.lintegral_Lp_add_le (μ := volumeOn V) hf hg hq
  have hpt : ∀ z, ENNReal.ofReal |u.toFun z| ≤
      ENNReal.ofReal |u.toFun z - abar| + ENNReal.ofReal |abar| := fun z => by
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc |u.toFun z| = |(u.toFun z - abar) + abar| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  have hq1 : (0 : ℝ) ≤ 1 / q := by positivity
  have hstep : (∫⁻ z in V, ENNReal.ofReal |u.toFun z| ^ q) ^ (1 / q) ≤
      (∫⁻ z, (fun z => ENNReal.ofReal |u.toFun z - abar|) z ^ q ∂(volumeOn V)) ^ (1 / q) +
      (∫⁻ z, (fun _ : Vec 2 => ENNReal.ofReal |abar|) z ^ q ∂(volumeOn V)) ^ (1 / q) := by
    refine le_trans ?_ hM
    refine ENNReal.rpow_le_rpow (lintegral_mono fun z => ?_) hq1
    exact ENNReal.rpow_le_rpow (hpt z) hq0.le
  -- first term
  have hA := hS q hq u
  have hA' : (∫⁻ z, (fun z => ENNReal.ofReal |u.toFun z - abar|) z ^ q ∂(volumeOn V)) ^ (1 / q) ≤
      ENNReal.ofReal (C0 * Real.sqrt q * E) := by
    rw [← hE] at hA
    simpa only [habar] using hA
  -- second term
  have hmu : (volumeOn V) univ = ENNReal.ofReal m := by
    rw [Measure.restrict_apply_univ, hm, ENNReal.ofReal_toReal hVfin]
  have hB : (∫⁻ z, (fun _ : Vec 2 => ENNReal.ofReal |abar|) z ^ q ∂(volumeOn V)) ^ (1 / q) =
      ENNReal.ofReal (|abar| * m ^ (1 / q)) := by
    rw [lintegral_const, hmu, ENNReal.mul_rpow_of_nonneg _ _ hq1, ← ENNReal.rpow_mul,
      mul_one_div_cancel hq0.ne', ENNReal.rpow_one,
      ENNReal.ofReal_rpow_of_nonneg hmpos.le hq1, ← ENNReal.ofReal_mul (abs_nonneg _)]
  have hm1 : m ^ (1 / q) ≤ max 1 m := by
    rcases le_or_gt m 1 with h | h
    · exact (Real.rpow_le_one hmpos.le h hq1).trans (le_max_left _ _)
    · calc m ^ (1 / q) ≤ m ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h.le (by rw [div_le_one hq0]; exact hq)
        _ = m := Real.rpow_one m
        _ ≤ _ := le_max_right _ _
  have hconst : |abar| * m ^ (1 / q) ≤ m ^ (-(1 : ℝ) / 2) * max 1 m * N := by
    have hmq : 0 ≤ m ^ (1 / q) := Real.rpow_nonneg hmpos.le _
    calc |abar| * m ^ (1 / q) ≤ (m ^ (-(1 : ℝ) / 2) * N) * max 1 m :=
          mul_le_mul hmean hm1 hmq (by positivity)
      _ = _ := by ring
  refine hstep.trans ?_
  rw [hB]
  refine (add_le_add hA' le_rfl).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  set Cm : ℝ := m ^ (-(1 : ℝ) / 2) * max 1 m with hCm
  have hCm0 : 0 ≤ Cm := by positivity
  have h1 : C0 ≤ max C0 Cm := le_max_left _ _
  have h2 : Cm ≤ max C0 Cm := le_max_right _ _
  have hsq0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  have hmax0 : 0 ≤ max C0 Cm := le_trans hCm0 h2
  calc C0 * Real.sqrt q * E + |abar| * m ^ (1 / q)
      ≤ max C0 Cm * Real.sqrt q * E + Cm * N := by
        gcongr
    _ ≤ max C0 Cm * Real.sqrt q * E + max C0 Cm * Real.sqrt q * N := by
        have hh : Cm ≤ max C0 Cm * Real.sqrt q := by nlinarith
        gcongr
    _ = _ := by ring

theorem sobolev_sqrt_V {V : Set (Vec 2)} (hUopen : IsOpenBoundedConvexDomain V)
    (hvolpos : 0 < volume V)
    (hVD : ∀ x ∈ V, ∀ y ∈ V, vecEuclideanNorm (x - y) < 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 1 ≤ q → ∀ u : W1pFunction V (ENNReal.ofReal ((2 : ℕ) : ℝ)),
      (∫⁻ z in V, ENNReal.ofReal |u.toFun z| ^ q) ^ (1 / q) ≤
        ENNReal.ofReal (C * Real.sqrt q *
          ((eLpNorm u.toFun (ENNReal.ofReal ((2 : ℕ) : ℝ)) (volumeOn V)).toReal +
           (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal ((2 : ℕ) : ℝ))
            (volumeOn V)).toReal)) :=
  ⟨sobConst V, sobConst_pos hUopen hvolpos, sobolev_sqrt_V_const hUopen hvolpos hVD⟩

end PDE.TrudingerV
end

-- ==== from TrudUnif.lean ====
-- Uniformity of the `√q` Sobolev constant over convex sets of volume in `[v0, v1]`.


@[expose] public section

open MeasureTheory Set Filter Topology PDE
open PDE.Trudinger (C2 unitVol_pos)
open scoped ENNReal

namespace PDE.TrudingerV

/-- Upper bound for the Trudinger constant in terms of `v0 ≤ |V| ≤ v1`. -/
noncomputable def trudBound (d : ℕ) (v0 v1 : ℝ) : ℝ :=
  max (max (2 * 3 ^ d * v1 ^ (((d : ℝ) - 1) / d)) (4 * v1))
    ((4 ^ d / (d * v0) * C2 d) ^ ((d : ℝ) / ((d : ℝ) - 1)))

theorem trudingerConst_le {d : ℕ} (hd : 2 ≤ d) {V : Set (Vec d)} {v0 v1 : ℝ} (hv0 : 0 < v0)
    (h0 : v0 ≤ (volume V).toReal) (h1 : (volume V).toReal ≤ v1) :
    trudingerConst V ≤ trudBound d v0 v1 := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hθ : 0 ≤ ((d : ℝ) - 1) / d := div_nonneg (by linarith) hd0.le
  have hq : 0 ≤ (d : ℝ) / ((d : ℝ) - 1) := div_nonneg hd0.le (by linarith)
  have hC2 : 0 ≤ C2 d := by
    have := unitVol_pos d
    unfold C2; positivity
  have hvV : 0 < (volume V).toReal := lt_of_lt_of_le hv0 h0
  unfold trudingerConst trudBound rieszConst
  refine max_le_max (max_le_max ?_ (by linarith)) ?_
  · gcongr
  · refine Real.rpow_le_rpow (by positivity) ?_ hq
    gcongr

theorem sobConst_le {V : Set (Vec 2)} {v0 v1 : ℝ} (hv0 : 0 < v0)
    (h0 : v0 ≤ (volume V).toReal) (h1 : (volume V).toReal ≤ v1)
    (hC1 : 0 < trudingerConst V) :
    sobConst V ≤ max (max 1 (v1 + trudBound 2 v0 v1) * Real.sqrt (trudBound 2 v0 v1))
      (v0 ^ (-(1 : ℝ) / 2) * max 1 v1) := by
  have hT := trudingerConst_le (d := 2) le_rfl hv0 h0 h1
  have hvV : 0 < (volume V).toReal := lt_of_lt_of_le hv0 h0
  unfold sobConst sqrtConst
  refine max_le_max ?_ ?_
  · refine mul_le_mul (max_le_max le_rfl (by linarith)) (Real.sqrt_le_sqrt hT)
      (Real.sqrt_nonneg _) (le_trans zero_le_one (le_max_left _ _))
  · refine mul_le_mul ?_ (max_le_max le_rfl h1) (by positivity) (by positivity)
    exact Real.rpow_le_rpow_of_nonpos hv0 h0 (by norm_num)

/-- **Sobolev with `√q`, uniform in the domain.** -/
theorem sobolev_sqrt_V_unif {v0 v1 : ℝ} (hv0 : 0 < v0) :
    ∃ C : ℝ, 0 < C ∧ ∀ {V : Set (Vec 2)}, IsOpenBoundedConvexDomain V → 0 < volume V →
      (∀ x ∈ V, ∀ y ∈ V, vecEuclideanNorm (x - y) < 4) →
      v0 ≤ (volume V).toReal → (volume V).toReal ≤ v1 →
      ∀ q : ℝ, 1 ≤ q → ∀ u : W1pFunction V (ENNReal.ofReal ((2 : ℕ) : ℝ)),
      (∫⁻ z in V, ENNReal.ofReal |u.toFun z| ^ q) ^ (1 / q) ≤
        ENNReal.ofReal (C * Real.sqrt q *
          ((eLpNorm u.toFun (ENNReal.ofReal ((2 : ℕ) : ℝ)) (volumeOn V)).toReal +
           (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal ((2 : ℕ) : ℝ))
            (volumeOn V)).toReal)) := by
  refine ⟨max (max (max 1 (v1 + trudBound 2 v0 v1) * Real.sqrt (trudBound 2 v0 v1))
      (v0 ^ (-(1 : ℝ) / 2) * max 1 v1)) 1, lt_max_of_lt_right one_pos, ?_⟩
  intro V hUopen hvolpos hVD h0 h1 q hq u
  have hvV : 0 < (volume V).toReal := lt_of_lt_of_le hv0 h0
  have hC1 : 0 < trudingerConst V := trudingerConst_pos hvV
  refine (sobolev_sqrt_V_const hUopen hvolpos hVD q hq u).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hb := (sobConst_le hv0 h0 h1 hC1).trans (le_max_left _ (1 : ℝ))
  have hnn : 0 ≤ Real.sqrt q *
      ((eLpNorm u.toFun (ENNReal.ofReal ((2 : ℕ) : ℝ)) (volumeOn V)).toReal +
       (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal ((2 : ℕ) : ℝ))
        (volumeOn V)).toReal) := by positivity
  calc _ = sobConst V * (Real.sqrt q * _) := by ring
    _ ≤ _ * (Real.sqrt q * _) := mul_le_mul_of_nonneg_right hb hnn
    _ = _ := by ring

end PDE.TrudingerV
end

-- ==== from FaceSqrt.lean ====
-- Sobolev on a single square face with the optimal growth `√q`, uniform in `r ∈ [1/2,1]`.


@[expose] public section

open scoped ENNReal
open MeasureTheory Set PDE

namespace PDE.BSlocalmax

/-- **Sobolev with `√q` on a square face** (`n = 2`), `C¹` functions, constant uniform in
`r ∈ [1/2, 1]` and `q ≥ 1`. -/
theorem face_sobolev_two :
    ∃ C : ℝ, 0 < C ∧ ∀ r ∈ Icc (1 / 2 : ℝ) 1, ∀ q : ℝ, 1 ≤ q → ∀ g : Vec 2 → ℝ,
      ContDiff ℝ 1 g →
      (∫ y in Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-r) r), |g y| ^ q) ^ (1 / q) ≤
        C * Real.sqrt q * (∫ y in Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-r) r),
          (g y ^ 2 + vecNormSq (classicalGradient g y))) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hmain⟩ := PDE.TrudingerV.sobolev_sqrt_V_unif (v0 := 1) (v1 := 4) one_pos
  refine ⟨C * Real.sqrt 2, by positivity, ?_⟩
  intro r hr q hq g hg
  have hr0 : 0 < r := by linarith [hr.1]
  have hq0 : 0 < q := by linarith
  have hq1 : (0 : ℝ) ≤ 1 / q := by positivity
  have ht : (0 : ℝ) < 2 * r := by linarith
  obtain ⟨V, hVdef⟩ : ∃ V : Set (Vec 2), V = axisCube (fun _ : Fin 2 => -r) (2 * r) := ⟨_, rfl⟩
  have hV : IsOpenBoundedConvexDomain V := by
    rw [hVdef]; exact isOpenBoundedConvexDomain_axisCube (fun _ : Fin 2 => -r) (2 * r)
  have hVpi : V = Set.pi Set.univ (fun _ : Fin 2 => Ioo (-r) r) := by
    rw [hVdef]; exact axisCube_eq_pi_Ioo r
  have hvol : (volume V).toReal = (2 * r) ^ 2 := by
    have e := Real.volume_pi_Ioo_toReal (a := fun _ : Fin 2 => -r)
      (b := fun _ : Fin 2 => -r + 2 * r) (fun i => by show -r ≤ -r + 2 * r; linarith)
    have e2 : (volume (axisCube (fun _ : Fin 2 => -r) (2 * r))).toReal =
        ∏ _i : Fin 2, ((-r + 2 * r) - (-r)) := e
    rw [hVdef, e2]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1; ring
  have h0 : (1 : ℝ) ≤ (volume V).toReal := by rw [hvol]; nlinarith [hr.1]
  have h1 : (volume V).toReal ≤ 4 := by rw [hvol]; nlinarith [hr.2]
  have hvolpos : 0 < volume V :=
    (ENNReal.toReal_pos_iff.1 (by rw [hvol]; positivity)).1
  have hVD : ∀ x ∈ V, ∀ y ∈ V, vecEuclideanNorm (x - y) < 4 := by
    intro x hx y hy
    rw [hVpi] at hx hy
    have hx0 := hx 0 (mem_univ _)
    have hx1 := hx 1 (mem_univ _)
    have hy0 := hy 0 (mem_univ _)
    have hy1 := hy 1 (mem_univ _)
    have hsq : vecEuclideanNorm (x - y) ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
      rw [vecEuclideanNorm_sq]
      simp [vecNormSq, vecDot, Fin.sum_univ_two]
      ring
    have hn := vecEuclideanNorm_nonneg (x - y)
    obtain ⟨hx0a, hx0b⟩ := hx0
    obtain ⟨hx1a, hx1b⟩ := hx1
    obtain ⟨hy0a, hy0b⟩ := hy0
    obtain ⟨hy1a, hy1b⟩ := hy1
    have ha : (x 0 - y 0) ^ 2 < 4 := by nlinarith [hr.2]
    have hb : (x 1 - y 1) ^ 2 < 4 := by nlinarith [hr.2]
    nlinarith
  have hcomp : ∀ f : Vec 2 → ℝ, Continuous f → IntegrableOn f V := fun f hf =>
    (hf.continuousOn.integrableOn_compact
      hV.isBoundedDomain.isBounded.isCompact_closure).mono_set subset_closure
  let u : W1pFunction V (ENNReal.ofReal ((2 : ℕ) : ℝ)) :=
    w1pOfContDiff hV.isOpen hV.isBoundedDomain.isBounded hg _
  have h : (∫⁻ z in V, ENNReal.ofReal |g z| ^ q) ^ (1 / q) ≤
      ENNReal.ofReal (C * Real.sqrt q *
        ((eLpNorm g (ENNReal.ofReal ((2 : ℕ) : ℝ)) (volumeOn V)).toReal +
         (eLpNorm (fun x => vecEuclideanNorm (classicalGradient g x))
           (ENNReal.ofReal ((2 : ℕ) : ℝ)) (volumeOn V)).toReal)) :=
    hmain hV hvolpos hVD h0 h1 q hq u
  -- the norms
  have e2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  have hgg : ∀ x, |g x| ^ (2 : ℝ) = g x ^ 2 := fun x => by rw [Real.rpow_two, sq_abs]
  have hN : (eLpNorm g (ENNReal.ofReal ((2 : ℕ) : ℝ)) (volumeOn V)).toReal =
      (∫ x in V, g x ^ 2) ^ (1 / 2 : ℝ) := by
    rw [e2]
    have toR := toReal_eLpNormOn (U := V) hg.continuous (p := 2) (by norm_num)
    have : (eLpNorm g (ENNReal.ofReal 2) (volumeOn V)).toReal =
        (eLpNormOn V (ENNReal.ofReal 2) g).toReal := rfl
    rw [this, toR]
    simp only [hgg]
  have hE : (eLpNorm (fun x => vecEuclideanNorm (classicalGradient g x))
      (ENNReal.ofReal ((2 : ℕ) : ℝ)) (volumeOn V)).toReal =
      (∫ x in V, vecNormSq (classicalGradient g x)) ^ (1 / 2 : ℝ) := by
    rw [e2]
    have toR := toReal_eLpNormOn (U := V) (continuous_gradNorm hg) (p := 2) (by norm_num)
    have : (eLpNorm (fun x => vecEuclideanNorm (classicalGradient g x)) (ENNReal.ofReal 2)
        (volumeOn V)).toReal =
        (eLpNormOn V (ENNReal.ofReal 2) (fun x => vecEuclideanNorm (classicalGradient g x))).toReal :=
      rfl
    rw [this, toR]
    have hh : ∀ x, |vecEuclideanNorm (classicalGradient g x)| ^ (2 : ℝ) =
        vecNormSq (classicalGradient g x) := fun x => by
      rw [Real.rpow_two, sq_abs, vecEuclideanNorm_sq]
    simp only [hh]
  rw [hN, hE] at h
  -- left-hand side
  have hIq : IntegrableOn (fun z => |g z| ^ q) V :=
    hcomp _ ((continuous_abs.comp hg.continuous).rpow_const fun _ => Or.inr hq0.le)
  have hLHS : (∫⁻ z in V, ENNReal.ofReal |g z| ^ q) = ENNReal.ofReal (∫ z in V, |g z| ^ q) := by
    rw [ofReal_integral_eq_lintegral_ofReal hIq
      (Filter.Eventually.of_forall fun z => Real.rpow_nonneg (abs_nonneg _) _)]
    refine lintegral_congr fun z => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq0.le]
  have hXnn : 0 ≤ ∫ z in V, |g z| ^ q :=
    setIntegral_nonneg hV.isOpen.measurableSet fun z _ => Real.rpow_nonneg (abs_nonneg _) _
  rw [hLHS, ENNReal.ofReal_rpow_of_nonneg hXnn hq1] at h
  have ha : 0 ≤ ∫ x in V, g x ^ 2 :=
    setIntegral_nonneg hV.isOpen.measurableSet fun z _ => sq_nonneg _
  have hb : 0 ≤ ∫ x in V, vecNormSq (classicalGradient g x) :=
    setIntegral_nonneg hV.isOpen.measurableSet fun z _ => by
      rw [← vecEuclideanNorm_sq]; exact sq_nonneg _
  have hrhs : 0 ≤ C * Real.sqrt q * ((∫ x in V, g x ^ 2) ^ (1 / 2 : ℝ) +
      (∫ x in V, vecNormSq (classicalGradient g x)) ^ (1 / 2 : ℝ)) := by positivity
  have hreal := (ENNReal.ofReal_le_ofReal_iff hrhs).1 h
  -- `√a + √b ≤ √2 √(a+b)`
  have hc2 : Continuous (fun y => vecNormSq (classicalGradient g y)) := by
    refine ((continuous_gradNorm hg).pow 2).congr (fun y => ?_)
    show vecEuclideanNorm (classicalGradient g y) ^ 2 = _
    exact vecEuclideanNorm_sq _
  have hsum : ∫ y in V, (g y ^ 2 + vecNormSq (classicalGradient g y)) =
      (∫ x in V, g x ^ 2) + ∫ x in V, vecNormSq (classicalGradient g x) :=
    integral_add (hcomp _ (hg.continuous.pow 2)) (hcomp _ hc2)
  have hS : (∫ x in V, g x ^ 2) ^ (1 / 2 : ℝ) +
      (∫ x in V, vecNormSq (classicalGradient g x)) ^ (1 / 2 : ℝ) ≤
      Real.sqrt 2 * (∫ y in V, (g y ^ 2 + vecNormSq (classicalGradient g y))) ^ (1 / 2 : ℝ) := by
    rw [hsum, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
      ← Real.sqrt_mul (by norm_num)]
    refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
    nlinarith [sq_nonneg (Real.sqrt (∫ x in V, g x ^ 2) -
        Real.sqrt (∫ x in V, vecNormSq (classicalGradient g x))),
      Real.sq_sqrt ha, Real.sq_sqrt hb]
  have hfin : (∫ z in V, |g z| ^ q) ^ (1 / q) ≤
      C * Real.sqrt 2 * Real.sqrt q * (∫ y in V,
        (g y ^ 2 + vecNormSq (classicalGradient g y))) ^ (1 / 2 : ℝ) := by
    refine hreal.trans ?_
    calc C * Real.sqrt q * ((∫ x in V, g x ^ 2) ^ (1 / 2 : ℝ) +
          (∫ x in V, vecNormSq (classicalGradient g x)) ^ (1 / 2 : ℝ))
        ≤ C * Real.sqrt q * (Real.sqrt 2 * (∫ y in V,
            (g y ^ 2 + vecNormSq (classicalGradient g y))) ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = _ := by ring
  -- pass from the open to the closed cube
  have hae : V =ᵐ[volume] Set.pi Set.univ (fun _ : Fin 2 => Icc (-r) r) := by
    rw [hVpi]; exact Measure.pi_Ioo_ae_eq_pi_Icc
  rw [setIntegral_congr_set hae, setIntegral_congr_set hae] at hfin
  exact hfin

end PDE.BSlocalmax
end

-- ==== from BoundarySobolevGen.lean ====
-- Generalization of `boundary_sobolev` to an arbitrary exponent `p` and arbitrary `δ ∈ (0,1]`,
-- and its `n = 2` instance with the optimal growth `√q`.


@[expose] public section

open MeasureTheory Set PDE

namespace PDE.BSlocalmax

/-- Sobolev on a single face, generalized: exponent `p` and `δ`. -/
lemma face_bound_gen {n : ℕ} {p δ : ℝ} {Cf : ℝ}
    (hfs : ∀ r ∈ Icc (1 / 2 : ℝ) 1, ∀ g : Vec n → ℝ, ContDiff ℝ 1 g →
      (∫ y in Set.pi Set.univ (fun _ : Fin n => Set.Icc (-r) r),
          |g y| ^ p) ^ (δ / 2) ≤
        Cf * (∫ y in Set.pi Set.univ (fun _ : Fin n => Set.Icc (-r) r),
          (g y ^ 2 + vecNormSq (classicalGradient g y))) ^ (1 / 2 : ℝ))
    {u : Vec (n + 1) → ℝ} (hu : ContDiff ℝ 1 u) (i : Fin (n + 1)) (s : ℝ) {r : ℝ}
    (hr : r ∈ Icc (1 / 2 : ℝ) 1) :
    (faceIntegral i s r (fun x => |u x| ^ p)) ^ δ ≤
      Cf ^ 2 * faceIntegral i s r (fun x => u x ^ 2 + vecNormSq (classicalGradient u x)) := by
  have hr0 : 0 ≤ r := by linarith [hr.1]
  have hKm : MeasurableSet (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hKc : IsCompact (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hgu := contDiff_comp_face hu i (s * r)
  have h1 := hfs r hr (fun y => u (Fin.insertNth i (s * r) y)) hgu
  have hF0 : 0 ≤ ∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r),
      |u (Fin.insertNth i (s * r) y)| ^ p :=
    setIntegral_nonneg hKm (fun y _ => Real.rpow_nonneg (abs_nonneg _) _)
  have hH0 : 0 ≤ ∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r),
      (u (Fin.insertNth i (s * r) y) ^ 2 +
        vecNormSq (classicalGradient (fun y => u (Fin.insertNth i (s * r) y)) y)) :=
    setIntegral_nonneg hKm (fun y _ => add_nonneg (sq_nonneg _) (vecNormSq_nonneg' _))
  have hmono : (∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r),
      (u (Fin.insertNth i (s * r) y) ^ 2 +
        vecNormSq (classicalGradient (fun y => u (Fin.insertNth i (s * r) y)) y))) ≤
      faceIntegral i s r (fun x => u x ^ 2 + vecNormSq (classicalGradient u x)) := by
    unfold faceIntegral
    have hc1 : Continuous (fun y : Fin n → ℝ =>
        u (Fin.insertNth i (s * r) y) ^ 2 +
          vecNormSq (classicalGradient (fun y => u (Fin.insertNth i (s * r) y)) y)) :=
      (hgu.continuous.pow 2).add (continuous_vecNormSq_grad hgu)
    have hc2 : Continuous (fun y : Fin n → ℝ =>
        u (Fin.insertNth i (s * r) y) ^ 2 +
          vecNormSq (classicalGradient u (Fin.insertNth i (s * r) y))) :=
      ((hu.continuous.comp (contDiff_faceMap i (s * r)).continuous).pow 2).add
        ((continuous_vecNormSq_grad hu).comp (contDiff_faceMap i (s * r)).continuous)
    refine setIntegral_mono_on (hc1.continuousOn.integrableOn_compact hKc)
      (hc2.continuousOn.integrableOn_compact hKc) hKm (fun y _ => ?_)
    exact add_le_add le_rfl (vecNormSq_face_le hu i (s * r) y)
  have hsq : ((∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r),
      (u (Fin.insertNth i (s * r) y) ^ 2 +
        vecNormSq (classicalGradient (fun y => u (Fin.insertNth i (s * r) y)) y))) ^ (1 / 2 : ℝ)) ^ 2 =
      ∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r),
      (u (Fin.insertNth i (s * r) y) ^ 2 +
        vecNormSq (classicalGradient (fun y => u (Fin.insertNth i (s * r) y)) y)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hH0]
    norm_num
  show (∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r),
      |u (Fin.insertNth i (s * r) y)| ^ p) ^ δ ≤ _
  calc (∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r),
        |u (Fin.insertNth i (s * r) y)| ^ p) ^ δ
      = ((∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r),
        |u (Fin.insertNth i (s * r) y)| ^ p) ^
          (δ / 2)) ^ 2 := by
        rw [← Real.rpow_two, ← Real.rpow_mul hF0]; congr 1; ring
    _ ≤ (Cf * (∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r),
          (u (Fin.insertNth i (s * r) y) ^ 2 +
            vecNormSq (classicalGradient (fun y => u (Fin.insertNth i (s * r) y)) y))) ^
              (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (Real.rpow_nonneg hF0 _) h1 2
    _ = Cf ^ 2 * ∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r),
          (u (Fin.insertNth i (s * r) y) ^ 2 +
            vecNormSq (classicalGradient (fun y => u (Fin.insertNth i (s * r) y)) y)) := by
        rw [mul_pow, hsq]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmono (sq_nonneg _)

/-- **Sobolev on the cube boundaries, integrated over the shell** (generalized). -/
theorem boundary_sobolev_gen {n : ℕ} (hn : 1 ≤ n) {p δ : ℝ} (hp : 0 < p) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) {Cf : ℝ}
    (hfs : ∀ r ∈ Icc (1 / 2 : ℝ) 1, ∀ g : Vec n → ℝ, ContDiff ℝ 1 g →
      (∫ y in Set.pi Set.univ (fun _ : Fin n => Set.Icc (-r) r), |g y| ^ p) ^ (δ / 2) ≤
        Cf * (∫ y in Set.pi Set.univ (fun _ : Fin n => Set.Icc (-r) r),
          (g y ^ 2 + vecNormSq (classicalGradient g y))) ^ (1 / 2 : ℝ)) :
    ∀ {ρ σ : ℝ}, 1 / 2 ≤ ρ → ρ < σ → σ ≤ 1 →
      ∀ u : Vec (n + 1) → ℝ, ContDiff ℝ 1 u →
      ∫ r in Ioo ρ σ, (cubeBoundaryIntegral r (fun x => |u x| ^ p)) ^
          δ ≤
        Cf ^ 2 * ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ},
          (u x ^ 2 + vecNormSq (classicalGradient u x)) := by
  haveI : NeZero n := ⟨by omega⟩
  intro ρ σ hρ hρσ hσ u hu
  have hρ0 : 0 < ρ := by linarith
  have hgc : Continuous (fun x : Vec (n + 1) => |u x| ^ p) :=
    hu.continuous.abs.rpow_const (fun _ => Or.inr hp.le)
  have hWc : Continuous (fun x : Vec (n + 1) => u x ^ 2 + vecNormSq (classicalGradient u x)) :=
    (hu.continuous.pow 2).add (continuous_vecNormSq_grad hu)
  have hGc : ContinuousOn
      (fun r => cubeBoundaryIntegral r (fun x => |u x| ^ p)) (Icc ρ σ) :=
    (continuousOn_cubeBoundaryIntegral hgc).mono (fun r hr => lt_of_lt_of_le hρ0 hr.1)
  have hBc : ContinuousOn
      (fun r => cubeBoundaryIntegral r
        (fun x => u x ^ 2 + vecNormSq (classicalGradient u x))) (Icc ρ σ) :=
    (continuousOn_cubeBoundaryIntegral hWc).mono (fun r hr => lt_of_lt_of_le hρ0 hr.1)
  have hI1 : IntegrableOn (fun r => (cubeBoundaryIntegral r
      (fun x => |u x| ^ p)) ^ δ) (Ioo ρ σ) :=
    (ContinuousOn.integrableOn_Icc
      (hGc.rpow_const (fun r _ => Or.inr hδ.le))).mono_set Ioo_subset_Icc_self
  have hI2 : IntegrableOn (fun r => Cf ^ 2 * cubeBoundaryIntegral r
      (fun x => u x ^ 2 + vecNormSq (classicalGradient u x))) (Ioo ρ σ) :=
    (ContinuousOn.integrableOn_Icc (continuousOn_const.mul hBc)).mono_set Ioo_subset_Icc_self
  have hWint : IntegrableOn (fun x : Vec (n + 1) => u x ^ 2 + vecNormSq (classicalGradient u x))
      {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ} := by
    refine (hWc.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Vec (n + 1)) 1)).mono_set ?_
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hx.2.le).trans hσ
  have hpt : ∀ r ∈ Ioo ρ σ, (cubeBoundaryIntegral r
      (fun x => |u x| ^ p)) ^ δ ≤
      Cf ^ 2 * cubeBoundaryIntegral r (fun x => u x ^ 2 + vecNormSq (classicalGradient u x)) := by
    intro r hr
    have hr' : r ∈ Icc (1 / 2 : ℝ) 1 := ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have hr0 : 0 ≤ r := by linarith [hr'.1]
    have hKm : MeasurableSet (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)) :=
      MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
    have hF0 : ∀ (i : Fin (n + 1)) (s : ℝ),
        0 ≤ faceIntegral i s r (fun x => |u x| ^ p) := by
      intro i s
      unfold faceIntegral
      exact setIntegral_nonneg hKm (fun y _ => Real.rpow_nonneg (abs_nonneg _) _)
    unfold cubeBoundaryIntegral
    calc (∑ i : Fin (n + 1), ∑ s ∈ ({-1, 1} : Finset ℝ),
          faceIntegral i s r (fun x => |u x| ^ p)) ^ δ
        ≤ ∑ i : Fin (n + 1), (∑ s ∈ ({-1, 1} : Finset ℝ),
            faceIntegral i s r (fun x => |u x| ^ p)) ^ δ :=
          rpow_sum_le _ _ (fun i _ => Finset.sum_nonneg (fun s _ => hF0 i s)) hδ hδ1
      _ ≤ ∑ i : Fin (n + 1), ∑ s ∈ ({-1, 1} : Finset ℝ),
            (faceIntegral i s r (fun x => |u x| ^ p)) ^
              δ :=
          Finset.sum_le_sum (fun i _ => rpow_sum_le _ _ (fun s _ => hF0 i s) hδ hδ1)
      _ ≤ ∑ i : Fin (n + 1), ∑ s ∈ ({-1, 1} : Finset ℝ), Cf ^ 2 *
            faceIntegral i s r (fun x => u x ^ 2 + vecNormSq (classicalGradient u x)) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
            (fun s _ => face_bound_gen hfs hu i s hr'))
      _ = Cf ^ 2 * ∑ i : Fin (n + 1), ∑ s ∈ ({-1, 1} : Finset ℝ),
            faceIntegral i s r (fun x => u x ^ 2 + vecNormSq (classicalGradient u x)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
  calc ∫ r in Ioo ρ σ, (cubeBoundaryIntegral r
        (fun x => |u x| ^ p)) ^ δ
      ≤ ∫ r in Ioo ρ σ, Cf ^ 2 * cubeBoundaryIntegral r
          (fun x => u x ^ 2 + vecNormSq (classicalGradient u x)) :=
        setIntegral_mono_on hI1 hI2 measurableSet_Ioo hpt
    _ = Cf ^ 2 * ∫ r in Ioo ρ σ, cubeBoundaryIntegral r
          (fun x => u x ^ 2 + vecNormSq (classicalGradient u x)) := by
        rw [integral_const_mul]
    _ = _ := by rw [integral_shell_eq_boundaryIntegral hρ0 hWint]

/-- **Sobolev with `√q` on the boundaries of the cubes in `ℝ³`, integrated over a shell**:
`∫_ρ^σ (∫_{∂Q_r} |u|^q)^{2/q} dr ≤ C q ∫_{Q_σ∖Q_ρ} (u² + |∇u|²)` for `q ≥ 2`. -/
theorem boundary_sobolev_two :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 2 ≤ q → ∀ {ρ σ : ℝ}, 1 / 2 ≤ ρ → ρ < σ → σ ≤ 1 →
      ∀ u : Vec (2 + 1) → ℝ, ContDiff ℝ 1 u →
      ∫ r in Ioo ρ σ, (cubeBoundaryIntegral r (fun x => |u x| ^ q)) ^ (2 / q) ≤
        C * q * ∫ x in {x : Vec (2 + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ},
          (u x ^ 2 + vecNormSq (classicalGradient u x)) := by
  obtain ⟨C, hC, hf⟩ := face_sobolev_two
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro q hq ρ σ hρ hρσ hσ u hu
  have hq0 : 0 < q := by linarith
  have h := boundary_sobolev_gen (n := 2) (by norm_num) (p := q) (δ := 2 / q) hq0
    (by positivity) (by rw [div_le_one hq0]; exact hq) (Cf := C * Real.sqrt q)
    (fun r hr g hg => by
      have e : 2 / q / 2 = 1 / q := by field_simp
      rw [e]
      exact hf r hr q (by linarith) g hg) hρ hρσ hσ u hu
  refine h.trans (le_of_eq ?_)
  rw [mul_pow, Real.sq_sqrt hq0.le]

end PDE.BSlocalmax
end
