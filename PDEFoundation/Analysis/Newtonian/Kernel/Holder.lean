module

public import PDEFoundation.Analysis.Newtonian.Kernel.Deriv
public import PDEFoundation.Analysis.Newtonian.Kernel.InvPow
import Mathlib.Tactic

/-!
# Hölder estimate for the generic radial Jacobian

`kerJac_holder_aux`: for `|z - z'| ≤ |z|/2`, the Euclidean norm of `(J z - J z') v` is at most
`|k| (d+5)² 8^(d+2) · (|z - z'| / |z|^(d+1)) · |v|`.
-/

@[expose] public section

namespace PDE

namespace NewtonKernelAux

/-- The `(|z|^m)⁻¹` weight. -/
noncomputable def radialWeight {d : ℕ} (m : ℕ) (z : Vec d) : ℝ := (vecEuclideanNorm z ^ m)⁻¹

theorem kerJac_apply {d : ℕ} (k : ℝ) {z : Vec d} (hz : z ≠ 0) (v : Vec d) :
    matVecMul (kerJac k z) v =
      (k * radialWeight d z) • v - ((d : ℝ) * k * radialWeight (d + 2) z * vecDot z v) • z := by
  have hn : 0 < vecNormSq z := lt_of_le_of_ne (vecNormSq_nonneg z)
    (fun h => hz (vecNormSq_eq_zero h.symm))
  have hr : 0 < vecEuclideanNorm z := Real.sqrt_pos.mpr hn
  have hsq : vecEuclideanNorm z ^ 2 = vecNormSq z := Real.sq_sqrt hn.le
  funext i
  simp only [matVecMul, kerJac, kerProfile, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, radialWeight, vecDot]
  have e : ∀ j, ((if i = j then (1 : ℝ) else 0) - (d : ℝ) * (z i * z j) / vecNormSq z) *
        (k * ((Real.sqrt (vecNormSq z)) ^ d)⁻¹) * v j =
      (if i = j then k * (vecEuclideanNorm z ^ d)⁻¹ * v j else 0) -
        (d : ℝ) * k * (vecEuclideanNorm z ^ (d + 2))⁻¹ * (z j * v j) * z i := by
    intro j
    have hp : vecEuclideanNorm z ^ (d + 2) = vecEuclideanNorm z ^ d * vecNormSq z := by
      rw [pow_add, hsq]
    rw [hp]
    have := hr.ne'
    have h2 : vecNormSq z ≠ 0 := hn.ne'
    have h3 : vecEuclideanNorm z ^ d ≠ 0 := pow_ne_zero _ this
    unfold vecEuclideanNorm
    split_ifs
    · field_simp
    · field_simp
      ring
  rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_sub_distrib, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true, ← Finset.sum_mul, ← Finset.mul_sum]

theorem matVecMul_sub' {d : ℕ} (A B : Mat d) (v : Vec d) :
    matVecMul (A - B) v = matVecMul A v - matVecMul B v := by
  funext i
  simp [matVecMul, sub_mul, Finset.sum_sub_distrib]

theorem vecDot_sub_left {d : ℕ} (x y v : Vec d) : vecDot (x - y) v = vecDot x v - vecDot y v := by
  simp [vecDot, sub_mul, Finset.sum_sub_distrib]

theorem kerJac_sub_apply {d : ℕ} (k : ℝ) {z z' : Vec d} (hz : z ≠ 0) (hz' : z' ≠ 0) (v : Vec d) :
    matVecMul (kerJac k z - kerJac k z') v =
      (k * (radialWeight d z - radialWeight d z')) • v -
        ((d : ℝ) * k) • (((radialWeight (d + 2) z - radialWeight (d + 2) z') * vecDot z v) • z +
          (radialWeight (d + 2) z' * vecDot z v) • (z - z') +
          (radialWeight (d + 2) z' * vecDot (z - z') v) • z') := by
  rw [matVecMul_sub', kerJac_apply k hz, kerJac_apply k hz', vecDot_sub_left]
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring


theorem kerJac_holder_aux {d : ℕ} (k : ℝ) {z z' : Vec d} (hz : z ≠ 0)
    (hzz : vecEuclideanNorm (z - z') ≤ vecEuclideanNorm z / 2) (v : Vec d) :
    vecEuclideanNorm (matVecMul (kerJac k z - kerJac k z') v) ≤
      (|k| * ((d : ℝ) + 5) ^ 2 * 8 ^ (d + 2)) *
        (vecEuclideanNorm (z - z') / vecEuclideanNorm z ^ (d + 1)) * vecEuclideanNorm v := by
  set r := vecEuclideanNorm z with hr_def
  set r' := vecEuclideanNorm z' with hr'_def
  set δ := vecEuclideanNorm (z - z') with hδ_def
  have hr : 0 < r := vecEuclideanNorm_pos_iff.mpr hz
  have hδ0 : 0 ≤ δ := vecEuclideanNorm_nonneg _
  have h1 : r ≤ δ + r' := by
    have := vecEuclideanNorm_add_le (z - z') z'
    simpa using this
  have h2 : r' ≤ δ + r := by
    have := vecEuclideanNorm_add_le (z' - z) z
    rw [vecEuclideanNorm_sub_comm] at this
    simpa using this
  have hr'_lo : r / 2 ≤ r' := by linarith
  have hr'_hi : r' ≤ 3 * r / 2 := by linarith
  have hr'pos : 0 < r' := by linarith
  have hz' : z' ≠ 0 := vecEuclideanNorm_pos_iff.mp hr'pos
  have hdiff : |r - r'| ≤ δ := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [kerJac_sub_apply k hz hz' v]
  set P := r ^ (d + 1) with hP
  have hP0 : 0 < P := by positivity
  have hv0 : 0 ≤ vecEuclideanNorm v := vecEuclideanNorm_nonneg v
  set t := δ / P * vecEuclideanNorm v with ht
  have ht0 : 0 ≤ t := by positivity
  -- scalar bounds
  have hA : |radialWeight d z - radialWeight d z'| ≤ d * 8 ^ d * (δ / P) := by
    unfold radialWeight
    refine (inv_pow_sub_le d hr (by linarith) (by linarith) hr'_lo hr'_hi).trans ?_
    rw [hP, mul_div_assoc]
    gcongr
  have hB : |radialWeight (d + 2) z - radialWeight (d + 2) z'| ≤
      ((d + 2 : ℕ) : ℝ) * 8 ^ (d + 2) * (δ / (P * r ^ 2)) := by
    unfold radialWeight
    refine (inv_pow_sub_le (d + 2) hr (by linarith) (by linarith) hr'_lo hr'_hi).trans ?_
    have : r ^ (d + 2 + 1) = P * r ^ 2 := by rw [hP]; ring
    rw [this, mul_div_assoc]
    gcongr
  have hB' : radialWeight (d + 2) z' ≤ 2 ^ (d + 2) / (P * r) := by
    unfold radialWeight
    have : P * r = r ^ (d + 2) := by rw [hP]; ring
    rw [this]
    calc (r' ^ (d + 2))⁻¹ ≤ ((r / 2) ^ (d + 2))⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hr'_lo _)
      _ = 2 ^ (d + 2) / r ^ (d + 2) := by rw [div_pow]; field_simp
  have hB'0 : 0 ≤ radialWeight (d + 2) z' := by unfold radialWeight; positivity
  have hzv : |vecDot z v| ≤ r * vecEuclideanNorm v := abs_vecDot_le_vecEuclideanNorm_mul z v
  have hdv : |vecDot (z - z') v| ≤ δ * vecEuclideanNorm v := abs_vecDot_le_vecEuclideanNorm_mul _ v
  set K : ℝ := 8 ^ (d + 2) with hK
  have hK1 : (8 : ℝ) ^ d ≤ K := pow_le_pow_right₀ (by norm_num) (by omega)
  have hK2 : (2 : ℝ) ^ (d + 2) ≤ K := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hK0 : 0 < K := by positivity
  -- term bounds
  have hk0 : 0 ≤ |k| := abs_nonneg k
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have T1 : vecEuclideanNorm ((k * (radialWeight d z - radialWeight d z')) • v) ≤
      |k| * (d * K * t) := by
    rw [vecEuclideanNorm_smul, abs_mul, ht, mul_assoc]
    calc |k| * (|radialWeight d z - radialWeight d z'| * vecEuclideanNorm v)
        ≤ |k| * ((d * 8 ^ d * (δ / P)) * vecEuclideanNorm v) := by gcongr
      _ ≤ |k| * (d * K * (δ / P * vecEuclideanNorm v)) := by
          have : (d : ℝ) * 8 ^ d * (δ / P) * vecEuclideanNorm v =
            ((d : ℝ) * 8 ^ d) * (δ / P * vecEuclideanNorm v) := by ring
          rw [this]
          gcongr
  have S2 : vecEuclideanNorm (((radialWeight (d + 2) z - radialWeight (d + 2) z') * vecDot z v) • z)
      ≤ ((d : ℝ) + 2) * K * t := by
    rw [vecEuclideanNorm_smul, abs_mul]
    calc |radialWeight (d + 2) z - radialWeight (d + 2) z'| * |vecDot z v| * r
        ≤ (((d + 2 : ℕ) : ℝ) * K * (δ / (P * r ^ 2))) * (r * vecEuclideanNorm v) * r := by gcongr
      _ = ((d : ℝ) + 2) * K * t := by
          rw [ht]; push_cast; field_simp
  have S3 : vecEuclideanNorm ((radialWeight (d + 2) z' * vecDot z v) • (z - z')) ≤ K * t := by
    rw [vecEuclideanNorm_smul, abs_mul, abs_of_nonneg hB'0]
    calc radialWeight (d + 2) z' * |vecDot z v| * δ
        ≤ (2 ^ (d + 2) / (P * r)) * (r * vecEuclideanNorm v) * δ := by gcongr
      _ = 2 ^ (d + 2) * t := by rw [ht]; field_simp
      _ ≤ K * t := by gcongr
  have S4 : vecEuclideanNorm ((radialWeight (d + 2) z' * vecDot (z - z') v) • z') ≤ 2 * K * t := by
    rw [vecEuclideanNorm_smul, abs_mul, abs_of_nonneg hB'0]
    calc radialWeight (d + 2) z' * |vecDot (z - z') v| * r'
        ≤ (2 ^ (d + 2) / (P * r)) * (δ * vecEuclideanNorm v) * (3 * r / 2) := by gcongr
      _ = (3 / 2) * 2 ^ (d + 2) * t := by rw [ht]; field_simp
      _ ≤ 2 * K * t := by
          have : (3 / 2) * (2 : ℝ) ^ (d + 2) ≤ 2 * K := by linarith
          gcongr
  have hsum := vecEuclideanNorm_add_le
    (((radialWeight (d + 2) z - radialWeight (d + 2) z') * vecDot z v) • z +
          (radialWeight (d + 2) z' * vecDot z v) • (z - z'))
    ((radialWeight (d + 2) z' * vecDot (z - z') v) • z')
  have hsum2 := vecEuclideanNorm_add_le
    (((radialWeight (d + 2) z - radialWeight (d + 2) z') * vecDot z v) • z)
    ((radialWeight (d + 2) z' * vecDot z v) • (z - z'))
  rw [sub_eq_add_neg]
  refine (vecEuclideanNorm_add_le _ _).trans ?_
  rw [vecEuclideanNorm_neg, vecEuclideanNorm_smul ((d : ℝ) * k), abs_mul, abs_of_nonneg hd0]
  have hin : vecEuclideanNorm (((radialWeight (d + 2) z - radialWeight (d + 2) z') * vecDot z v) • z +
          (radialWeight (d + 2) z' * vecDot z v) • (z - z') +
          (radialWeight (d + 2) z' * vecDot (z - z') v) • z') ≤ ((d : ℝ) + 2) * K * t + K * t + 2 * K * t := by
    linarith
  have hfin : (d : ℝ) * |k| * (((d : ℝ) + 2) * K * t + K * t + 2 * K * t) + |k| * (d * K * t) ≤
      (|k| * ((d : ℝ) + 5) ^ 2 * K) * t := by
    have h0 : 0 ≤ |k| * K * t := by positivity
    have : (|k| * ((d : ℝ) + 5) ^ 2 * K) * t - ((d : ℝ) * |k| * (((d : ℝ) + 2) * K * t + K * t + 2 * K * t) + |k| * (d * K * t))
        = (|k| * K * t) * (((d : ℝ) + 5) ^ 2 - d * ((d : ℝ) + 5) - d) := by ring
    have h5 : 0 ≤ ((d : ℝ) + 5) ^ 2 - d * ((d : ℝ) + 5) - d := by linarith
    linarith [mul_nonneg h0 h5]
  calc _ ≤ |k| * (d * K * t) + (d : ℝ) * |k| * (((d : ℝ) + 2) * K * t + K * t + 2 * K * t) :=
        add_le_add T1 (mul_le_mul_of_nonneg_left hin (by positivity))
    _ ≤ (|k| * ((d : ℝ) + 5) ^ 2 * K) * t := by linarith [hfin]
    _ = _ := by rw [ht]; ring

end NewtonKernelAux

end PDE
