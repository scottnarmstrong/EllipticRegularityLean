module

public import PDEFoundation.Analysis.Inequalities.JohnNirenbergBall.GridLayer

/-!
# Estimates on one layer cube (Steps 4 and 5, per cube)

For a grid cube `Q` of scale `k` meeting the layer `A_k`, and `h = (u)_H`:
the integral `∫_Q |u - h|` and the distribution `|{x ∈ Q : |u - h| > t}|`.
-/

@[expose] public section

namespace PDE.JohnNirenbergBall

open BoxIntegral MeasureTheory Set PDE.JohnNirenberg
open scoped ENNReal

variable {d : ℕ} {R : ℝ} {x : Vec d} {u : Vec d → ℝ} {M : ℝ}

/-- The decay rate `a = (2 ^ (d + 1) e ω)⁻¹` of the cube estimate. -/
noncomputable def jnRate (d : ℕ) : ℝ := 1 / ((2 : ℝ) ^ d * Real.exp 1 * (2 * cubeBallRatio d))

theorem jnRate_pos (hd : 0 < d) : 0 < jnRate d := by
  have := cubeBallRatio_pos hd
  unfold jnRate; positivity

section Level

variable (hd : 0 < d) (hR : 0 < R) (hloc : LocallyIntegrableOn u (euclideanBall x R) volume)
  (hM : BMOBound (euclideanBall x R) u M) (hMpos : 0 < M)

include hd hR hloc hM hMpos

/-- Integrability and the basic comparisons on a layer cube. -/
theorem layerCube_facts {k : ℕ} {n : Fin d → ℤ} (hn : IsLayerIndex hd hR x k n) :
    IntegrableOn u (gridCube hd hR k n : Set (Vec d)) volume ∧
    integralAverage (gridCube hd hR k n : Set (Vec d))
        (fun z => |u z - integralAverage (gridCube hd hR k n : Set (Vec d)) u|) ≤
      2 * (cubeBallRatio d * M) ∧
    |integralAverage (gridCube hd hR k n : Set (Vec d)) u -
        integralAverage (euclideanBall x (3 * R / 4)) u| ≤ chainConst d * (k + 1) * M := by
  have hb := layerIndex_center_bounds hd hR hn
  have hQU : euclideanClosedBall (boxCenter (gridCube hd hR k n))
      (Real.sqrt d * gridSide d R k / 2) ⊆ euclideanBall x R := by
    rw [sqrt_mul_gridSide_div_two hd k]
    exact closedBall_subset_of_boundaryLayer hR k hb.1
  have h1 := box_oscillation_bounds hd hloc hM (gridCube hd hR k n) (gridCube_width hd hR k n) hQU
  exact ⟨h1.1, by
    have := dyadicDescendant_oscillation_le hd hloc hM (gridCube hd hR k n)
      (gridCube_width hd hR k n) hQU []
    simpa using this, abs_integralAverage_box_sub_H_le hd hR hloc hM hMpos.le k _
      (gridCube_width hd hR k n) (sqrt_mul_gridSide_div_two hd k) hb.1 hb.2⟩

/-- Step 4, per cube: `∫_Q |u - (u)_H| ≤ (2 ω + K (k + 1)) M |Q|`. -/
theorem lintegral_enorm_sub_H_le {k : ℕ} {n : Fin d → ℤ} (hn : IsLayerIndex hd hR x k n) :
    ∫⁻ z in (gridCube hd hR k n : Set (Vec d)), ‖u z - integralAverage (euclideanBall x (3 * R / 4)) u‖ₑ ≤
      ENNReal.ofReal ((2 * cubeBallRatio d + chainConst d * (k + 1)) * M) *
        volume (gridCube hd hR k n : Set (Vec d)) := by
  obtain ⟨hint, hosc, hcmp⟩ := layerCube_facts hd hR hloc hM hMpos hn
  set Q := (gridCube hd hR k n : Set (Vec d)) with hQ
  set h := integralAverage (euclideanBall x (3 * R / 4)) u
  set uQ := integralAverage Q u
  have hQtop : volume Q < ∞ := (gridCube hd hR k n).measure_coe_lt_top volume
  have hQpos : 0 < (volume Q).toReal := volume_box_toReal_pos _
  have hfint : IntegrableOn (fun z => u z - h) Q volume := hint.sub (integrableOn_const hQtop.ne)
  have hfnorm : IntegrableOn (fun z => ‖u z - h‖) Q volume := hfint.norm
  have hgint : IntegrableOn (fun z => |u z - uQ|) Q volume :=
    (hint.sub (integrableOn_const hQtop.ne)).abs
  rw [← ofReal_integral_norm_eq_lintegral_enorm hfint]
  have hω := cubeBallRatio_pos hd
  have hK := chainConst_pos hd
  rw [← ENNReal.ofReal_toReal hQtop.ne, ← ENNReal.ofReal_mul
    (mul_nonneg (add_nonneg (mul_nonneg two_pos.le hω.le)
      (mul_nonneg hK.le (by positivity))) hMpos.le)]
  apply ENNReal.ofReal_le_ofReal
  have hpt : ∀ z, ‖u z - h‖ ≤ |u z - uQ| + |uQ - h| := by
    intro z
    rw [Real.norm_eq_abs]
    calc |u z - h| = |(u z - uQ) + (uQ - h)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  have hI : ∫ z in Q, |u z - uQ| ≤ 2 * (cubeBallRatio d * M) * (volume Q).toReal := by
    have : ∫ z in Q, |u z - uQ| = (volume Q).toReal *
        integralAverage Q (fun z => |u z - uQ|) := by
      unfold integralAverage; field_simp
    rw [this, mul_comm]
    exact mul_le_mul_of_nonneg_right hosc hQpos.le
  calc ∫ z in Q, ‖u z - h‖ ≤ ∫ z in Q, (|u z - uQ| + |uQ - h|) :=
        setIntegral_mono hfnorm (hgint.add (integrableOn_const hQtop.ne)) hpt
    _ = (∫ z in Q, |u z - uQ|) + |uQ - h| * (volume Q).toReal := by
        rw [integral_add hgint (integrableOn_const hQtop.ne), setIntegral_const, smul_eq_mul,
          measureReal_def, mul_comm]
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_right hcmp hQpos.le
        nlinarith [this]

/-- Step 5, per cube: the distribution of `u - (u)_H` on a layer cube. -/
theorem volume_tail_layerCube_le {k : ℕ} {n : Fin d → ℤ} (hn : IsLayerIndex hd hR x k n)
    {t : ℝ} (_ht : 0 < t) :
    volume {z ∈ (gridCube hd hR k n : Set (Vec d)) |
        t < |u z - integralAverage (euclideanBall x (3 * R / 4)) u|} ≤
      ENNReal.ofReal (min 1 (Real.exp 2 *
          Real.exp (-((t / M - chainConst d * (k + 1)) * jnRate d)))) *
        volume (gridCube hd hR k n : Set (Vec d)) := by
  obtain ⟨hint, hosc, hcmp⟩ := layerCube_facts hd hR hloc hM hMpos hn
  set Q := (gridCube hd hR k n : Set (Vec d)) with hQ
  set h := integralAverage (euclideanBall x (3 * R / 4)) u
  set uQ := integralAverage Q u
  have hQtop : volume Q < ∞ := (gridCube hd hR k n).measure_coe_lt_top volume
  set S := {z ∈ Q | t < |u z - h|} with hS
  have hSQ : volume S ≤ volume Q := measure_mono fun z hz => hz.1
  have hQ' : volume Q = ENNReal.ofReal (volume Q).toReal := (ENNReal.ofReal_toReal hQtop.ne).symm
  set E := Real.exp 2 * Real.exp (-((t / M - chainConst d * (k + 1)) * jnRate d)) with hE
  have hEpos : 0 < E := by positivity
  have h1 : volume S ≤ ENNReal.ofReal 1 * volume Q := by simpa using hSQ
  have hT : ∀ z ∈ S, z ∈ {z ∈ Q | t - chainConst d * (k + 1) * M < |u z - uQ|} := by
    rintro z ⟨hzQ, hz⟩
    refine ⟨hzQ, ?_⟩
    have : |u z - h| ≤ |u z - uQ| + |uQ - h| := by
      calc |u z - h| = |(u z - uQ) + (uQ - h)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    linarith
  have hexpeq : ∀ t' : ℝ, t' / ((2 : ℝ) ^ d * Real.exp 1 * (2 * (cubeBallRatio d * M))) =
      (t' / M) * jnRate d := by
    intro t'
    have hω := cubeBallRatio_pos hd
    unfold jnRate; field_simp
  have h2 : volume S ≤ ENNReal.ofReal E * volume Q := by
    by_cases ht' : t - chainConst d * (k + 1) * M ≤ 0
    · refine hSQ.trans ?_
      have hexp : 1 ≤ E := by
        have h0 : t / M - chainConst d * (k + 1) ≤ 0 := by
          have : t / M ≤ chainConst d * (k + 1) := by
            rw [div_le_iff₀ hMpos]; linarith
          linarith
        have h0' : 0 ≤ -((t / M - chainConst d * (k + 1)) * jnRate d) := by
          have := jnRate_pos hd
          nlinarith
        have h1' := Real.one_le_exp h0'
        have h2' : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
        rw [hE]; nlinarith [Real.exp_pos 2]
      calc volume Q = ENNReal.ofReal 1 * volume Q := by simp
        _ ≤ ENNReal.ofReal E * volume Q := by gcongr
    · push Not at ht'
      have hcube := volume_lt_abs_sub_box_le hd hloc hM hMpos (gridCube hd hR k n)
        (gridCube_width hd hR k n)
        (by rw [sqrt_mul_gridSide_div_two hd k]
            exact closedBall_subset_of_boundaryLayer hR k (layerIndex_center_bounds hd hR hn).1)
        (t := t - chainConst d * (k + 1) * M)
      rw [hexpeq] at hcube
      have hEq : (t - chainConst d * (k + 1) * M) / M = t / M - chainConst d * (k + 1) := by
        field_simp
      rw [hEq] at hcube
      have hTtop : volume {z ∈ Q | t - chainConst d * (k + 1) * M < |u z - uQ|} < ∞ :=
        lt_of_le_of_lt (measure_mono fun z hz => hz.1) hQtop
      calc volume S ≤ volume {z ∈ Q | t - chainConst d * (k + 1) * M < |u z - uQ|} :=
            measure_mono hT
        _ = ENNReal.ofReal (volume {z ∈ Q | t - chainConst d * (k + 1) * M < |u z - uQ|}).toReal :=
            (ENNReal.ofReal_toReal hTtop.ne).symm
        _ ≤ ENNReal.ofReal (E * (volume Q).toReal) := ENNReal.ofReal_le_ofReal hcube
        _ = ENNReal.ofReal E * volume Q := by
            rw [ENNReal.ofReal_mul hEpos.le, ENNReal.ofReal_toReal hQtop.ne]
  rw [ENNReal.ofReal_min]
  rcases min_choice (ENNReal.ofReal 1) (ENNReal.ofReal E) with h | h <;> rw [h]
  · exact h1
  · exact h2

end Level

end PDE.JohnNirenbergBall
