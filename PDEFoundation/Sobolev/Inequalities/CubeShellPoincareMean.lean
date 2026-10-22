module

public import PDEFoundation.Sobolev.Inequalities.CubeShellPoincare

/-! # Centering the cube-shell estimate at its genuine integral mean -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

/-- The integral mean minimizes squared deviation on a set of positive,
finite volume. -/
theorem setIntegral_sq_sub_integralAverage_le
    {d : ℕ} {S : Set (Vec d)} {f : Vec d → ℝ}
    (hf : MemL2On S f) (hSpos : 0 < volume S)
    (hStop : volume S < ∞) (c : ℝ) :
    (∫ x in S, (f x - integralAverage S f) ^ 2) ≤
      ∫ x in S, (f x - c) ^ 2 := by
  let a : ℝ := integralAverage S f
  let : IsFiniteMeasure (volumeOn S) :=
    isFiniteMeasure_restrict.mpr hStop.ne
  have hfint : IntegrableOn f S volume := hf.integrable (by norm_num)
  have hsq : IntegrableOn (fun x => f x ^ 2) S volume := by
    simpa only [pow_two] using! hf.integrable_mul hf
  have hsqsub (b : ℝ) :
      IntegrableOn (fun x => (f x - b) ^ 2) S volume := by
    have hconst : IntegrableOn (fun _x : Vec d => b ^ 2) S volume :=
      integrableOn_const hStop.ne
    have hexpand : (fun x => (f x - b) ^ 2) =
        fun x => f x ^ 2 + (-2 * b) * f x + b ^ 2 := by
      funext x
      ring
    rw [hexpand]
    exact (hsq.add (hfint.const_mul (-2 * b))).add hconst
  have hcenter : ∫ x in S, (f x - a) ∂volume = 0 :=
    meanZeroOn_sub_integralAverage hfint hSpos hStop
  have hcrossInt : IntegrableOn
      (fun x => 2 * (f x - a) * (a - c)) S volume := by
    have ha : IntegrableOn (fun _x : Vec d => a) S volume :=
      integrableOn_const hStop.ne
    simpa only [Pi.sub_apply, mul_assoc, mul_comm, mul_left_comm] using!
      (hfint.sub ha).mul_const (2 * (a - c))
  have hconstInt : IntegrableOn
      (fun _x : Vec d => (a - c) ^ 2) S volume :=
    integrableOn_const hStop.ne
  have hexpand : (fun x => (f x - c) ^ 2) = fun x =>
      (f x - a) ^ 2 + 2 * (f x - a) * (a - c) + (a - c) ^ 2 := by
    funext x
    ring
  have hsplitOuter :
      (∫ x in S, ((f x - a) ^ 2 +
          2 * (f x - a) * (a - c)) + (a - c) ^ 2 ∂volume) =
        (∫ x in S, (f x - a) ^ 2 +
          2 * (f x - a) * (a - c) ∂volume) +
          ∫ _x in S, (a - c) ^ 2 ∂volume :=
    integral_add ((hsqsub a).add hcrossInt) hconstInt
  have hsplitInner :
      (∫ x in S, (f x - a) ^ 2 +
          2 * (f x - a) * (a - c) ∂volume) =
        (∫ x in S, (f x - a) ^ 2 ∂volume) +
          ∫ x in S, 2 * (f x - a) * (a - c) ∂volume :=
    integral_add (hsqsub a) hcrossInt
  have hcross :
      (∫ x in S, 2 * (f x - a) * (a - c) ∂volume) = 0 := by
    calc
      _ = 2 * (a - c) * ∫ x in S, (f x - a) ∂volume := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = 0 := by rw [hcenter]; ring
  have hidentity :
      (∫ x in S, (f x - c) ^ 2 ∂volume) =
        (∫ x in S, (f x - a) ^ 2 ∂volume) +
          (volume S).toReal * (a - c) ^ 2 := by
    rw [hexpand, hsplitOuter, hsplitInner, hcross, add_zero, setIntegral_const]
    simp only [smul_eq_mul, measureReal_def]
  change (∫ x in S, (f x - a) ^ 2 ∂volume) ≤
    ∫ x in S, (f x - c) ^ 2 ∂volume
  rw [hidentity]
  exact le_add_of_nonneg_right
    (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))

/-- Quantitative `L²` Poincaré inequality on a `d`-dimensional cube shell,
centered at the genuine shell mean. -/
theorem poincare_sq_on_cubeShell_average
    {d : ℕ} (hd : 2 ≤ d) {U : Set (Vec d)}
    (u : H1Function U) (x₀ : Vec d) {r : ℝ}
    (hr : 0 < r) (hShellU : cubeShell x₀ r ⊆ U) :
    ∫ x in cubeShell x₀ r,
      (u x - integralAverage (cubeShell x₀ r) u) ^ 2 ≤
      cubeShellPoincareConst d * r ^ 2 *
        ∫ x in cubeShell x₀ r, vecNormSq (u.grad x) := by
  have hStop : volume (cubeShell x₀ r) < ∞ := by
    apply lt_of_le_of_lt
      (measure_mono (show cubeShell x₀ r ⊆ centeredAxisCube x₀ (2 * r) from
        fun _ hx => hx.1))
    exact (volume_centeredAxisCube_ne_top x₀ (2 * r)).lt_top
  have hSpos : 0 < volume (cubeShell x₀ r) := by
    let T := cubeShellSlab x₀ r (⟨0, by omega⟩ : Fin d) true
    have hTpos : 0 < volume T :=
      (cubeShellSlab_domain x₀ r _ true).volume_pos
        (cubeShellSlab_nonempty x₀ hr _ true)
    exact lt_of_lt_of_le hTpos
      (measure_mono (cubeShellSlab_subset x₀ r _ true))
  have huS : MemL2On (cubeShell x₀ r) u :=
    memLpOn_mono hShellU u.memL2
  exact (setIntegral_sq_sub_integralAverage_le huS hSpos hStop
    (integralAverage
      (cubeShellSlab x₀ r ⟨0, by omega⟩ true) u)).trans
    (poincare_sq_on_cubeShell_rootAverage hd u x₀ hr hShellU)

end PDE
