module

public import PDEFoundation.Analysis.Newtonian.WeakType.DecompositionStopping
public import PDEFoundation.Geometry.BoxCircumscribedContainment
public import PDEFoundation.Measure.BallVolume

/-! # The exceptional set of the Calderón–Zygmund decomposition

The dilate `Q_k*` of a stopping cube is the Euclidean ball `B(c_k, 2 r_k)`, where `c_k` is the
centre of `Q_k` and `r_k = √d · side / 2` its circumscribed radius. Then
`Σ |Q_k*| ≤ C(d) ‖F‖₁ / λ`, and for `x ∉ Q_k*`, `y ∈ Q_k` one has `|x - c_k| ≥ 2 |y - c_k|`,
the condition `|z - z'| ≤ |z| / 2` of the kernel Hölder bound with `z = x - c_k`, `z' = x - y`.
-/

@[expose] public section

open BoxIntegral MeasureTheory Set
open scoped ENNReal

namespace PDE.NewtonWeakType

noncomputable section

variable {d : ℕ} {I : Box (Fin d)} {F : Vec d → Vec d} {lam : ℝ}

/-- The centre of the `k`-th stopping cube. -/
def czCenter (S : CZStopping I F lam) (k : S.ι) : Vec d := boxCenter (S.cube k)

/-- The circumscribed Euclidean radius of the `k`-th stopping cube. -/
def czRadius (S : CZStopping I F lam) (k : S.ι) : ℝ := Real.sqrt d * S.side k / 2

/-- The dilate `Q_k*`: the concentric ball of twice the circumscribed radius. -/
def czDilate (S : CZStopping I F lam) (k : S.ι) : Set (Vec d) :=
  euclideanBall (czCenter S k) (2 * czRadius S k)

/-- The dimensional constant bounding the volume of a dilate by that of its cube. -/
def czDilateConst (d : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt d ^ d) * volume (euclideanBall (0 : Vec d) 1)

variable (S : CZStopping I F lam)

theorem czRadius_pos (hd : 0 < d) (k : S.ι) : 0 < czRadius S k := by
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have := S.side_pos k
  unfold czRadius
  positivity

theorem vecEuclideanNorm_sub_czCenter_le (hd : 0 < d) {k : S.ι} {y : Vec d}
    (hy : y ∈ (S.cube k : Set (Vec d))) :
    vecEuclideanNorm (y - czCenter S k) ≤ czRadius S k :=
  vecEuclideanNorm_sub_boxCenter_le (S.cube k) (S.side k) hd (S.width k) hy

theorem czCube_subset_czDilate (hd : 0 < d) (k : S.ι) :
    (S.cube k : Set (Vec d)) ⊆ czDilate S k := by
  intro y hy
  have h2 := czRadius_pos S hd k
  exact (mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith)).mpr
    (lt_of_le_of_lt (vecEuclideanNorm_sub_czCenter_le S hd hy) (by linarith))

/-- Outside the dilate, `|x - c| ≥ 2 r`. -/
theorem two_mul_czRadius_le_of_notMem_czDilate (hd : 0 < d) {k : S.ι} {x : Vec d}
    (hx : x ∉ czDilate S k) : 2 * czRadius S k ≤ vecEuclideanNorm (x - czCenter S k) := by
  have h2 := czRadius_pos S hd k
  by_contra h
  exact hx ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith)).mpr (not_le.mp h))

/-- For `x ∉ Q_k*` and `y ∈ Q_k`: `|x - c_k| ≥ 2 |y - c_k|`. -/
theorem two_mul_vecEuclideanNorm_le_of_notMem_czDilate (hd : 0 < d) {k : S.ι} {x y : Vec d}
    (hx : x ∉ czDilate S k) (hy : y ∈ (S.cube k : Set (Vec d))) :
    2 * vecEuclideanNorm (y - czCenter S k) ≤ vecEuclideanNorm (x - czCenter S k) :=
  calc 2 * vecEuclideanNorm (y - czCenter S k) ≤ 2 * czRadius S k :=
        by linarith [vecEuclideanNorm_sub_czCenter_le S hd hy]
    _ ≤ _ := two_mul_czRadius_le_of_notMem_czDilate S hd hx

/-- The Hölder-kernel condition `|z - z'| ≤ |z| / 2` with `z = x - c_k`, `z' = x - y`. -/
theorem vecEuclideanNorm_sub_le_half_of_notMem_czDilate (hd : 0 < d) {k : S.ι} {x y : Vec d}
    (hx : x ∉ czDilate S k) (hy : y ∈ (S.cube k : Set (Vec d))) :
    vecEuclideanNorm ((x - czCenter S k) - (x - y)) ≤ vecEuclideanNorm (x - czCenter S k) / 2 := by
  have h := two_mul_vecEuclideanNorm_le_of_notMem_czDilate S hd hx hy
  have e : (x - czCenter S k) - (x - y) = y - czCenter S k := by abel
  rw [e]
  linarith

/-- The volume of a dilate is a dimensional constant times the volume of its cube. -/
theorem volume_czDilate (hd : 0 < d) (k : S.ι) :
    volume (czDilate S k) = czDilateConst d * volume (S.cube k : Set (Vec d)) := by
  have hr : 0 < 2 * czRadius S k := by linarith [czRadius_pos S hd k]
  have hℓ := S.side_pos k
  have hvol : volume (S.cube k : Set (Vec d)) = ENNReal.ofReal (S.side k ^ d) := by
    rw [← volume_box_toReal_eq_pow_of_commonWidth (S.cube k) (S.side k) (S.width k),
      ENNReal.ofReal_toReal ((S.cube k).measure_coe_lt_top volume).ne]
  have hR : (2 * czRadius S k) ^ d = Real.sqrt d ^ d * S.side k ^ d := by
    rw [← mul_pow]
    unfold czRadius
    ring_nf
  unfold czDilate czDilateConst
  rw [volume_euclideanBall_eq_unit_mul_of_pos _ hr, hvol, hR,
    ENNReal.ofReal_mul (by positivity)]
  ring

/-- **Exceptional set bound.** `Σ |Q_k*| ≤ C(d) ‖F‖₁ / λ`, in `lintegral` form. -/
theorem tsum_volume_czDilate_le (hd : 0 < d) :
    ∑' k, volume (czDilate S k) ≤
      czDilateConst d * ENNReal.ofReal lam⁻¹ *
        ∫⁻ x in (I : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (F x)) := by
  have hlam := S.lam_pos
  have hsum : ∑' k, volume (S.cube k : Set (Vec d)) ≤
      ENNReal.ofReal lam⁻¹ * ∫⁻ x in (I : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (F x)) := by
    have h := S.tsum_volume_le
    rw [ENNReal.ofReal_inv_of_pos hlam]
    calc _ = (ENNReal.ofReal lam)⁻¹ * (ENNReal.ofReal lam * ∑' k, volume (S.cube k : Set (Vec d))) := by
          rw [ENNReal.inv_mul_cancel_left (by simpa using hlam) ENNReal.ofReal_ne_top]
      _ ≤ _ := mul_le_mul_right h _
  calc
    ∑' k, volume (czDilate S k) = czDilateConst d * ∑' k, volume (S.cube k : Set (Vec d)) := by
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr fun k => volume_czDilate S hd k
    _ ≤ czDilateConst d * (ENNReal.ofReal lam⁻¹ *
        ∫⁻ x in (I : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (F x))) :=
      mul_le_mul_right hsum _
    _ = _ := by rw [mul_assoc]

end

end PDE.NewtonWeakType
