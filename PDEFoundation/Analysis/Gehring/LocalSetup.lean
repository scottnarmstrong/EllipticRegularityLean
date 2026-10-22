module

public import PDEFoundation.Analysis.Gehring.WhitneyFamilyExists
public import PDEFoundation.Analysis.Gehring.WeakType
public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.Geometry.EuclideanBall.Basic
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.Convex.Integral

/-!
# Localization set-up for the Gehring lemma (Step 4)

Let `1/2 ≤ ρ < R ≤ 3/4` (here: `0 < ρ < R ≤ 1`), `g ≥ 0` integrable with compact support and
vanishing outside `B_R`, `m = ⨍_{B_1} g > 0`. For `t ≥ T_{ρ,R} = (3 √d / (R - ρ)) ^ (d + 1) * m`
the level set `E_t` has volume at most `(2 (R - ρ) / √d) ^ d`
(`volume_gehringE_le`), and hence every selected Whitney cube `Q` meeting `B_ρ` satisfies
`ℓ(Q) ≤ (R - ρ) / (σ √d)` and `σ Q ⊆ B_R` (`WhitneyFamily.local_conclusions`).
-/

@[expose] public section

namespace PDE.Gehring

open Set MeasureTheory
open scoped ENNReal

variable {d : ℕ}

theorem euclideanBall_zero_mono {R R' : ℝ} (h : R ≤ R') (hR : 0 ≤ R) :
    euclideanBall (0 : Vec d) R ⊆ euclideanBall (0 : Vec d) R' := by
  intro x hx
  have h2 : R ^ 2 ≤ R' ^ 2 := by nlinarith
  exact lt_of_lt_of_le hx h2

/-- The unit Euclidean ball has volume at most `2 ^ d`. -/
theorem volume_euclideanBall_unit_toReal_le :
    (volume (euclideanBall (0 : Vec d) 1)).toReal ≤ 2 ^ d := by
  have hsub : euclideanBall (0 : Vec d) 1 ⊆ centeredAxisCube (0 : Vec d) 1 := by
    intro x hx
    have hn := (mem_euclideanBall_iff_vecEuclideanNorm_lt one_pos).1 hx
    rw [sub_zero] at hn
    intro i _
    have := abs_apply_le_vecEuclideanNorm x i
    have h2 := abs_lt.1 (lt_of_le_of_lt this hn)
    simp only [Pi.zero_apply, Set.mem_Ioo]
    constructor <;> linarith [h2.1, h2.2]
  have h1 := ENNReal.toReal_mono (volume_centeredAxisCube_ne_top (0 : Vec d) 1)
    (measure_mono hsub)
  rw [volume_centeredAxisCube_toReal (0 : Vec d) zero_le_one] at h1
  simpa using h1

/-- Jensen: `∫ g ^ θ ≤ ω_d (⨍_{B_1} g) ^ θ` for `g` supported in `B_R ⊆ B_1`. -/
theorem integral_rpow_theta_le (hd : 0 < d) {g : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hg : Integrable g volume) (hc : HasCompactSupport g) {R : ℝ} (hR : R ≤ 1) (hR0 : 0 ≤ R)
    (hsupp : ∀ x, x ∉ euclideanBall (0 : Vec d) R → g x = 0) :
    ∫ y, g y ^ gehringTheta d ≤
      (volume (euclideanBall (0 : Vec d) 1)).toReal *
        (integralAverage (euclideanBall (0 : Vec d) 1) g) ^ gehringTheta d := by
  set B := euclideanBall (0 : Vec d) 1 with hB
  set θ := gehringTheta d with hθdef
  have hθ := gehringTheta_pos hd
  have hθ1 := gehringTheta_lt_one d
  have hz : ∀ x, x ∉ B → g x = 0 := fun x hx =>
    hsupp x fun h => hx (euclideanBall_zero_mono hR hR0 h)
  have hint : Integrable (fun y => g y ^ θ) volume := integrable_rpow_theta hd hg0 hg hc
  have hBpos : 0 < (volume B).toReal := volume_euclideanBall_toReal_pos 0 one_pos
  have hBne0 : volume B ≠ 0 := (volume_euclideanBall_pos 0 one_pos).ne'
  have hBne : volume B ≠ ∞ := volume_euclideanBall_ne_top 0 zero_le_one
  have e1 : ∫ y in B, g y ^ θ = ∫ y, g y ^ θ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx; rw [hz x hx, Real.zero_rpow hθ.ne']
  have jens := (Real.concaveOn_rpow hθ.le hθ1.le).le_map_set_average
    (Real.continuous_rpow_const hθ.le).continuousOn isClosed_Ici hBne0 hBne
    (Filter.Eventually.of_forall fun x => hg0 x) hg.integrableOn hint.integrableOn
  rw [setAverage_eq, setAverage_eq] at jens
  simp only [smul_eq_mul, Measure.real] at jens
  have : (volume B).toReal * ((volume B).toReal⁻¹ * ∫ x in B, g x ^ θ) = ∫ x, g x ^ θ := by
    rw [← mul_assoc, mul_inv_cancel₀ hBpos.ne', one_mul, e1]
  rw [← this]
  exact mul_le_mul_of_nonneg_left jens hBpos.le

/-- The real-number core of the volume bound for `E_t`. -/
theorem core_volume_bound (hd : 0 < d) {m t δ ω : ℝ} (hm : 0 < m) (hδ : 0 < δ) (hω0 : 0 ≤ ω)
    (hω : ω ≤ 2 ^ d)
    (ht : (3 * Real.sqrt d / δ) ^ (d + 1) * m ≤ t) :
    3 ^ d / t ^ gehringTheta d * (ω * m ^ gehringTheta d) ≤ (2 * δ / Real.sqrt d) ^ d := by
  have hθ := gehringTheta_pos hd
  have hdR : (0 : ℝ) < d := Nat.cast_pos.2 hd
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 hdR
  set x : ℝ := δ / (3 * Real.sqrt d) with hx
  have hx0 : 0 < x := by positivity
  have hTpos : 0 < (3 * Real.sqrt d / δ) ^ (d + 1) * m := by positivity
  have htpos : 0 < t := lt_of_lt_of_le hTpos ht
  have hmt : m / t ≤ x ^ (d + 1) := by
    rw [div_le_iff₀ htpos]
    have : x ^ (d + 1) * ((3 * Real.sqrt d / δ) ^ (d + 1) * m) = m := by
      rw [← mul_assoc, ← mul_pow, hx]
      have : δ / (3 * Real.sqrt d) * (3 * Real.sqrt d / δ) = 1 := by field_simp
      rw [this, one_pow, one_mul]
    calc m = x ^ (d + 1) * ((3 * Real.sqrt d / δ) ^ (d + 1) * m) := this.symm
      _ ≤ x ^ (d + 1) * t := by gcongr
  have h1 : (m / t) ^ gehringTheta d ≤ x ^ d := by
    calc (m / t) ^ gehringTheta d ≤ (x ^ (d + 1)) ^ gehringTheta d :=
          Real.rpow_le_rpow (by positivity) hmt hθ.le
      _ = x ^ d := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_natCast]
          congr 1
          unfold gehringTheta; push_cast; field_simp
  have e : 3 ^ d / t ^ gehringTheta d * (ω * m ^ gehringTheta d) = 3 ^ d * ω * (m / t) ^ gehringTheta d := by
    rw [Real.div_rpow hm.le htpos.le]; ring
  rw [e]
  have h3 : (3 : ℝ) ^ d * x ^ d = (δ / Real.sqrt d) ^ d := by
    rw [← mul_pow, hx]; congr 1; field_simp
  calc 3 ^ d * ω * (m / t) ^ gehringTheta d ≤ 3 ^ d * ω * x ^ d := by gcongr
    _ = ω * (3 ^ d * x ^ d) := by ring
    _ = ω * (δ / Real.sqrt d) ^ d := by rw [h3]
    _ ≤ 2 ^ d * (δ / Real.sqrt d) ^ d := by gcongr
    _ = (2 * δ / Real.sqrt d) ^ d := by rw [← mul_pow]; congr 1; ring

/-- The volume of the level set `E_t` is small for `t ≥ T_{ρ,R}`. -/
theorem volume_gehringE_le (hd : 0 < d) {g : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hg : Integrable g volume) (hc : HasCompactSupport g) {ρ R : ℝ} (hρR : ρ < R) (hR : R ≤ 1)
    (hρ : 0 < ρ)
    (hsupp : ∀ x, x ∉ euclideanBall (0 : Vec d) R → g x = 0)
    (hm : 0 < integralAverage (euclideanBall (0 : Vec d) 1) g) {t : ℝ}
    (ht : (3 * Real.sqrt d / (R - ρ)) ^ (d + 1) * integralAverage (euclideanBall (0 : Vec d) 1) g
      ≤ t) :
    volume (gehringE g t) ≤ ENNReal.ofReal ((2 * (R - ρ) / Real.sqrt d) ^ d) := by
  set m := integralAverage (euclideanBall (0 : Vec d) 1) g with hmdef
  have hδ : 0 < R - ρ := by linarith
  have hdR : (0 : ℝ) < d := Nat.cast_pos.2 hd
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 hdR
  have hθ := gehringTheta_pos hd
  have hTpos : 0 < (3 * Real.sqrt d / (R - ρ)) ^ (d + 1) * m := by positivity
  have htpos : 0 < t := lt_of_lt_of_le hTpos ht
  have hset : gehringE g t = {x | ENNReal.ofReal (t ^ gehringTheta d) <
      cubeMaximal (fun y => g y ^ gehringTheta d) x} := by
    ext x; exact mem_gehringE_iff hd g htpos.le x
  have hweak := volume_lt_cubeMaximal_le hd (fun y => g y ^ gehringTheta d)
    (s := t ^ gehringTheta d) (Real.rpow_pos_of_pos htpos _)
  rw [← hset] at hweak
  have hint := integrable_rpow_theta hd hg0 hg hc
  have hl : ∫⁻ y, ‖g y ^ gehringTheta d‖ₑ = ENNReal.ofReal (∫ y, g y ^ gehringTheta d) := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm hint]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact Real.norm_of_nonneg (Real.rpow_nonneg (hg0 y) _)
  rw [hl] at hweak
  have hj := integral_rpow_theta_le hd hg0 hg hc hR (by linarith) hsupp
  have hcore := core_volume_bound hd hm hδ ENNReal.toReal_nonneg volume_euclideanBall_unit_toReal_le ht
  refine hweak.trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc 3 ^ d / t ^ gehringTheta d * ∫ y, g y ^ gehringTheta d
      ≤ 3 ^ d / t ^ gehringTheta d * ((volume (euclideanBall (0 : Vec d) 1)).toReal *
        m ^ gehringTheta d) := by
        gcongr
    _ ≤ _ := hcore

/-- Local conclusions for a selected Whitney cube meeting `B_ρ`: `ℓ(Q) ≤ (R - ρ) / (σ √d)` and
`σ Q ⊆ B_R`. -/
theorem WhitneyFamily.local_conclusions (hd : 0 < d) {g : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hg : Integrable g volume) (hc : HasCompactSupport g) {ρ R : ℝ} (hρR : ρ < R) (hR : R ≤ 1)
    (hρ : 0 < ρ)
    (hsupp : ∀ x, x ∉ euclideanBall (0 : Vec d) R → g x = 0)
    (hm : 0 < integralAverage (euclideanBall (0 : Vec d) 1) g) {t : ℝ}
    (ht : (3 * Real.sqrt d / (R - ρ)) ^ (d + 1) * integralAverage (euclideanBall (0 : Vec d) 1) g
      ≤ t) {σ : ℝ} (hσ : σ = 2 ∨ σ = 4) (F : WhitneyFamily d g t σ) (i : F.ι)
    (hi : (dyadicCube (F.scale i) (F.index i) ∩ euclideanBall (0 : Vec d) ρ).Nonempty) :
    (2 : ℝ) ^ (F.scale i) ≤ (R - ρ) / (σ * Real.sqrt d) ∧
      centeredAxisCube (dyadicCenter (F.scale i) (F.index i)) (σ * 2 ^ (F.scale i) / 2) ⊆
        euclideanBall (0 : Vec d) R := by
  have hσ2 : 2 ≤ σ := by rcases hσ with h | h <;> linarith
  have hσ0 : 0 < σ := by linarith
  have hδ : 0 < R - ρ := by linarith
  have hdR : (0 : ℝ) < d := Nat.cast_pos.2 hd
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 hdR
  have hp : (0 : ℝ) < 2 ^ (F.scale i) := dyadicSide_pos _
  have hvol := volume_gehringE_le hd hg0 hg hc hρR hR hρ hsupp hm ht
  have hsub := F.closedDilate_subset i
  have h1 : ENNReal.ofReal ((2 * (σ * 2 ^ (F.scale i))) ^ d) ≤
      ENNReal.ofReal ((2 * (R - ρ) / Real.sqrt d) ^ d) := by
    rw [← volume_closedCenteredAxisCube _ (by positivity)]
    exact (measure_mono hsub).trans hvol
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
  have h2 : 2 * (σ * 2 ^ (F.scale i)) ≤ 2 * (R - ρ) / Real.sqrt d :=
    le_of_pow_le_pow_left₀ hd.ne' (by positivity) h1
  have hℓ : (2 : ℝ) ^ (F.scale i) ≤ (R - ρ) / (σ * Real.sqrt d) := by
    rw [le_div_iff₀ (by positivity)]
    have := (le_div_iff₀ hsd).1 h2
    linarith
  refine ⟨hℓ, ?_⟩
  obtain ⟨x, hxQ, hxB⟩ := hi
  intro y hy
  have hxn := (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).1 hxB
  rw [sub_zero] at hxn
  have hyx : ‖y - x‖ ≤ (σ + 1) * 2 ^ (F.scale i) / 2 := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro j
    have a1 := hy j (Set.mem_univ j)
    have a2 := hxQ j
    simp only [Set.mem_Ioo, dyadicCenter] at a1
    rw [Real.norm_eq_abs, abs_le]
    simp only [Pi.sub_apply]
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  have hRn : vecEuclideanNorm (y - x) ≤ 3 / 4 * (R - ρ) := by
    calc vecEuclideanNorm (y - x) ≤ Real.sqrt d * ‖y - x‖ :=
          vecEuclideanNorm_le_sqrt_natCast_mul_norm _
      _ ≤ Real.sqrt d * ((σ + 1) * 2 ^ (F.scale i) / 2) := by gcongr
      _ ≤ Real.sqrt d * ((σ + 1) / 2 * ((R - ρ) / (σ * Real.sqrt d))) := by
          apply mul_le_mul_of_nonneg_left _ hsd.le
          have h := mul_le_mul_of_nonneg_left hℓ (show (0 : ℝ) ≤ (σ + 1) / 2 by linarith)
          linarith [h]
      _ = (σ + 1) / (2 * σ) * (R - ρ) := by field_simp
      _ ≤ 3 / 4 * (R - ρ) := by
          exact mul_le_mul_of_nonneg_right
            (by rw [div_le_iff₀ (by positivity)]; linarith) hδ.le
  have hRpos : 0 < R := by linarith
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hRpos, sub_zero]
  calc vecEuclideanNorm y = vecEuclideanNorm ((y - x) + x) := by congr 1; abel
    _ ≤ vecEuclideanNorm (y - x) + vecEuclideanNorm x := vecEuclideanNorm_add_le _ _
    _ < R := by linarith

end PDE.Gehring
