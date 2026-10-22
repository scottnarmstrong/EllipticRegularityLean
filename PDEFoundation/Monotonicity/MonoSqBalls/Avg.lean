module

public import PDEFoundation.Monotonicity.Core.Bridge
public import PDEFoundation.Sobolev.Mean
import PDEFoundation.Monotonicity.MonoSqBalls.SphereBound
import PDEFoundation.Measure.BallVolume

/-!
# Ball averages versus sphere means

For continuous `g` write `a(t) = ⨍_{B_t} g` and `m(t) = ⨍_{∂B_t} g`.  Then
`a'(t) = (d/t) (m(t) - a(t))`, and a bound `m(s) ≤ (s/r)² m(r)` on `(0, r)` gives
`a(r) ≤ d/(d+2) m(r)`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.MonoSqBalls

variable {d : ℕ}

theorem integral_one_euclideanBall {r : ℝ} (hr : 0 < r) :
    ∫ _y in euclideanBall (0 : Vec d) r, (1 : ℝ) =
      r ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal := by
  rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real,
    volume_euclideanBall_toReal_eq_unit_mul_of_pos _ hr]

theorem sphereArea_eq [NeZero d] :
    sphereArea d = d * (volume (euclideanBall (0 : Vec d) 1)).toReal := by
  have h1 := hasDerivAt_integral_euclideanBall (d := d) (g := fun _ => (1 : ℝ))
    continuous_const (r := 1) one_pos
  have h2 : HasDerivAt (fun s : ℝ => s ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal)
      (d * 1 ^ (d - 1) * (volume (euclideanBall (0 : Vec d) 1)).toReal) 1 :=
    (hasDerivAt_pow d (1 : ℝ)).mul_const _
  have h3 := h2.congr_of_eventuallyEq (f₁ := fun s => ∫ _y in euclideanBall (0 : Vec d) s, (1 : ℝ))
    (by
      filter_upwards [Ioi_mem_nhds (one_pos : (0 : ℝ) < 1)] with s hs
      exact integral_one_euclideanBall hs)
  have h4 := h1.unique h3
  rw [sphereIntegral_eq_mul_sphereMean, sphereMean_const] at h4
  simpa using h4

theorem hasDerivAt_integralAverage [NeZero d] {g : Vec d → ℝ} (hg : Continuous g) {r : ℝ}
    (hr : 0 < r) :
    HasDerivAt (fun t => integralAverage (euclideanBall (0 : Vec d) t) g)
      (d / r * (sphereMean 0 r g - integralAverage (euclideanBall 0 r) g)) r := by
  have hI := hasDerivAt_integral_euclideanBall hg hr
  have hω : 0 < (volume (euclideanBall (0 : Vec d) 1)).toReal :=
    volume_euclideanBall_toReal_pos 0 one_pos
  have hP : HasDerivAt (fun t : ℝ => t ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal)
      (d * r ^ (d - 1) * (volume (euclideanBall (0 : Vec d) 1)).toReal) r :=
    (hasDerivAt_pow d r).mul_const _
  have hP0 : r ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal ≠ 0 := by positivity
  have hprod := (hP.inv hP0).mul hI
  refine (hprod.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [Ioi_mem_nhds hr] with t ht
    simp only [integralAverage, volume_euclideanBall_toReal_eq_unit_mul_of_pos _ ht,
      Pi.mul_apply, Pi.inv_apply]
  · simp only [integralAverage, volume_euclideanBall_toReal_eq_unit_mul_of_pos _ hr,
      sphereIntegral_eq_mul_sphereMean, sphereArea_eq, Pi.inv_apply]
    have hd1 : r ^ d = r * r ^ (d - 1) := by
      rw [← pow_succ']; congr 1; have := NeZero.pos d; omega
    have hdne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
    rw [hd1]
    have : r ^ (d - 1) ≠ 0 := by positivity
    field_simp
    ring

theorem integralAverage_le [NeZero d] {g : Vec d → ℝ} (hg : Continuous g) {r : ℝ} (hr : 0 < r)
    (hle : ∀ s ∈ Ioo 0 r, sphereMean (0 : Vec d) s g ≤ (s / r) ^ 2 * sphereMean 0 r g) :
    integralAverage (euclideanBall (0 : Vec d) r) g ≤ d / (d + 2) * sphereMean 0 r g := by
  have hpolar := integral_euclideanBall_eq_intervalIntegral_sphereIntegral hg hr
  have hc := continuous_sphereIntegral hg (0 : Vec d)
  set c : ℝ := sphereArea d * sphereMean 0 r g / r ^ 2 with hcdef
  have hbound : ∫ t in (0 : ℝ)..r, sphereIntegral 0 t g ≤
      ∫ t in (0 : ℝ)..r, c * t ^ (d + 1) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hr.le (hc.intervalIntegrable _ _)
      ((continuous_const.mul (continuous_pow _)).intervalIntegrable _ _) fun t ht => ?_
    rw [sphereIntegral_eq_mul_sphereMean]
    have hpow : t ^ (d + 1) = t ^ (d - 1) * t ^ 2 := by
      rw [← pow_add]; congr 1; have := NeZero.pos d; omega
    have hnn : 0 ≤ sphereArea d * t ^ (d - 1) := (mul_pos sphereArea_pos (pow_pos ht.1 _)).le
    calc sphereArea d * t ^ (d - 1) * sphereMean 0 t g
        ≤ sphereArea d * t ^ (d - 1) * ((t / r) ^ 2 * sphereMean 0 r g) :=
          mul_le_mul_of_nonneg_left (hle t ht) hnn
      _ = c * t ^ (d + 1) := by rw [hcdef, hpow]; field_simp
  have hint : ∫ t in (0 : ℝ)..r, c * t ^ (d + 1) = c * (r ^ (d + 2) / (d + 2)) := by
    rw [intervalIntegral.integral_const_mul, integral_pow]
    push_cast
    simp only [zero_pow (Nat.succ_ne_zero _), sub_zero]
    ring
  have hω : 0 < (volume (euclideanBall (0 : Vec d) 1)).toReal :=
    volume_euclideanBall_toReal_pos 0 one_pos
  have hV : 0 < r ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal := by positivity
  have hdne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hd2 : (d : ℝ) + 2 ≠ 0 := by positivity
  unfold integralAverage
  rw [volume_euclideanBall_toReal_eq_unit_mul_of_pos _ hr, hpolar]
  calc (r ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal)⁻¹ *
        ∫ t in (0 : ℝ)..r, sphereIntegral 0 t g
      ≤ (r ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal)⁻¹ *
          (c * (r ^ (d + 2) / (d + 2))) :=
        mul_le_mul_of_nonneg_left (hbound.trans_eq hint) (inv_nonneg.mpr hV.le)
    _ = d / (d + 2) * sphereMean 0 r g := by
      rw [hcdef, sphereArea_eq]
      have : r ^ (d + 2) = r ^ d * r ^ 2 := pow_add _ _ _
      rw [this]
      field_simp

end PDE.MonoSqBalls
