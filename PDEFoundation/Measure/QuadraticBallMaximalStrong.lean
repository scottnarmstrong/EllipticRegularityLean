module

public import PDEFoundation.Measure.BallMaximalStrongNorm

/-!
# Strong bounds for the quadratic ball maximal function

The sharp estimate follows from the scalar maximal theorem at exponent `p / 2`.
A second theorem records the uniform constant used in the regularity argument.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

private theorem eLpNorm_vecNormSq {d : ℕ} (F : Vec d → Vec d) {p : ℝ} (hp : 0 < p)
    (hg : AEStronglyMeasurable (fun x => vecEuclideanNorm (F x)) volume) :
    eLpNorm (fun x => vecNormSq (F x)) (ENNReal.ofReal (p / 2)) volume =
      eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) volume ^ (2 : ℝ) := by
  let g := fun x => vecEuclideanNorm (F x)
  simp_rw [← vecEuclideanNorm_sq]
  calc
    eLpNorm (fun x => g x ^ 2) (ENNReal.ofReal (p / 2)) volume =
        eLpNorm (fun x => ‖g x‖ ^ (2 : ℝ)) (ENNReal.ofReal (p / 2)) volume := by
      congr 2
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _), Real.rpow_two]
    _ = eLpNorm g (ENNReal.ofReal (p / 2) * ENNReal.ofReal 2) volume ^ (2 : ℝ) :=
      eLpNorm_norm_rpow g hg (by norm_num)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (div_nonneg hp.le (by norm_num))]
      congr 3
      ring

private theorem memLp_vecNormSq {d : ℕ} (F : Vec d → Vec d) {p : ℝ} (hp : 0 < p)
    (hF : MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) volume) :
    MemLp (fun x => vecNormSq (F x)) (ENNReal.ofReal (p / 2)) volume := by
  show eLpNorm (fun x => vecNormSq (F x)) (ENNReal.ofReal (p / 2)) volume < ∞
  rw [eLpNorm_vecNormSq F hp hF.aestronglyMeasurable]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hF.eLpNorm_lt_top.ne

/-- The sharp strong bound obtained from the scalar maximal theorem at exponent `p / 2`. -/
theorem eLpNorm_quadraticBallMaximal_le {d : ℕ} (F : Vec d → Vec d) {p : ℝ}
    (hp : 2 < p)
    (hF : MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) volume) :
    eLpNorm (quadraticBallMaximal F) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (Real.sqrt 2 * ((3 : ℝ) ^ d * p / (p - 2)) ^ (1 / p)) *
        eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) volume := by
  let g := fun x => vecEuclideanNorm (F x)
  let q := p / 2
  have hp0 : 0 < p := by linarith
  have hq : 1 < q := by dsimp [q]; linarith
  have hs := eLpNorm_uncenteredBallMaximal_le
    (fun x => vecNormSq (F x)) hq (memLp_vecNormSq F hp0 hF)
  have hexponent : ENNReal.ofReal p * ENNReal.ofReal (1 / 2) = ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_mul hp0.le]
    congr 1
    dsimp [q]
    ring
  have hquad :
      eLpNorm (quadraticBallMaximal F) (ENNReal.ofReal p) volume =
        eLpNorm (uncenteredBallMaximal (fun x => vecNormSq (F x)))
          (ENNReal.ofReal q) volume ^ (1 / 2 : ℝ) := by
    unfold quadraticBallMaximal
    calc
      _ = eLpNorm (fun x => ‖uncenteredBallMaximal (fun y => vecNormSq (F y)) x‖ₑ ^
          (1 / 2 : ℝ)) (ENNReal.ofReal p) volume := by simp
      _ = eLpNorm (uncenteredBallMaximal (fun x => vecNormSq (F x)))
          (ENNReal.ofReal p * ENNReal.ofReal (1 / 2)) volume ^ (1 / 2 : ℝ) :=
        eLpNorm_enorm_rpow _
          (measurable_uncenteredBallMaximal _).aestronglyMeasurable (by norm_num)
      _ = _ := by rw [hexponent]
  rw [hquad]
  refine (ENNReal.rpow_le_rpow hs (by norm_num)).trans_eq ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have hnormSq : eLpNorm (fun x => vecNormSq (F x)) (ENNReal.ofReal q) volume =
      eLpNorm g (ENNReal.ofReal p) volume ^ (2 : ℝ) := by
    simpa [q, g] using eLpNorm_vecNormSq F hp0 hF.aestronglyMeasurable
  have hnormRoot :
      eLpNorm (fun x => vecNormSq (F x)) (ENNReal.ofReal q) volume ^ (1 / 2 : ℝ) =
        eLpNorm g (ENNReal.ofReal p) volume := by
    rw [hnormSq, ← ENNReal.rpow_mul]
    norm_num
  rw [hnormRoot]
  congr 1
  have h3 : 0 < (3 : ℝ)^d := pow_pos (by norm_num) _
  have hratio : 0 < (3 : ℝ)^d * q / (q - 1) := by
    apply div_pos (mul_pos h3 (by dsimp [q]; linarith))
    linarith
  rw [ENNReal.ofReal_rpow_of_nonneg
    (mul_nonneg (by norm_num) (Real.rpow_nonneg hratio.le _)) (by norm_num)]
  apply congrArg ENNReal.ofReal
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hratio.le _)]
  rw [← Real.sqrt_eq_rpow]
  have hratioEq : (3 : ℝ) ^ d * q / (q - 1) = (3 : ℝ) ^ d * p / (p - 2) := by
    dsimp [q]
    field_simp
  rw [hratioEq]
  rw [← Real.rpow_mul (div_nonneg (mul_nonneg h3.le hp0.le) (by linarith))]
  congr 1
  dsimp [q]
  field_simp

/-- Uniform source bound for every `p ≥ 4`. -/
theorem eLpNorm_quadraticBallMaximal_le_uniform {d : ℕ} (F : Vec d → Vec d) {p : ℝ}
    (hp : 4 ≤ p)
    (hF : MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) volume) :
    eLpNorm (quadraticBallMaximal F) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (2 * (3 : ℝ) ^ ((d : ℝ) / 4)) *
        eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) volume := by
  have hp2 : 2 < p := lt_of_lt_of_le (by norm_num) hp
  refine (eLpNorm_quadraticBallMaximal_le F hp2 hF).trans ?_
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hratio0 : 0 ≤ p / (p - 2) := div_nonneg hp0.le (by linarith)
  have hratio2 : p / (p - 2) ≤ 2 := by
    apply (div_le_iff₀ (by linarith)).2
    linarith
  have hinvHalf : 1 / p ≤ (1 : ℝ) / 2 := by
    apply (div_le_div_iff_of_pos_left (by norm_num : (0 : ℝ) < 1) hp0 (by norm_num)).2
    linarith
  have hratioPow : (p / (p - 2)) ^ (1 / p) ≤ Real.sqrt 2 := by
    calc
      _ ≤ (2 : ℝ) ^ (1 / p) :=
        Real.rpow_le_rpow hratio0 hratio2 (by positivity)
      _ ≤ (2 : ℝ) ^ (1 / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hinvHalf
      _ = Real.sqrt 2 := (Real.sqrt_eq_rpow 2).symm
  have hinvQuarter : 1 / p ≤ (1 : ℝ) / 4 := by
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hp)
  have h3Pow : ((3 : ℝ) ^ (d : ℕ)) ^ (1 / p) ≤
      (3 : ℝ) ^ ((d : ℝ) / 4) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using hinvQuarter)
      (Nat.cast_nonneg _)
  have hfactor : (3 : ℝ) ^ d * p / (p - 2) =
      (3 : ℝ) ^ d * (p / (p - 2)) := by ring
  rw [hfactor]
  rw [Real.mul_rpow (pow_nonneg (by norm_num) _) hratio0]
  calc
    Real.sqrt 2 * (((3 : ℝ) ^ d) ^ (1 / p) * (p / (p - 2)) ^ (1 / p)) ≤
        Real.sqrt 2 * ((3 : ℝ) ^ ((d : ℝ) / 4) * Real.sqrt 2) := by gcongr
    _ = (3 : ℝ) ^ ((d : ℝ) / 4) * (Real.sqrt 2 * Real.sqrt 2) := by ring
    _ = (3 : ℝ) ^ ((d : ℝ) / 4) * 2 := by
      rw [Real.mul_self_sqrt (by norm_num)]
    _ = 2 * (3 : ℝ) ^ ((d : ℝ) / 4) := by ring

end PDE
