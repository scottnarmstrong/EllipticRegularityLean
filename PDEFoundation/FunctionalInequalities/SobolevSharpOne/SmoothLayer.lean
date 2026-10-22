module

public import PDEFoundation.FunctionalInequalities.SobolevSharpOne.ErosionBound
public import PDEFoundation.FunctionalInequalities.SobolevSharpOne.BMStep
public import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Smooth case: the layer-cake form of the Brunn--Minkowski erosion step

For `f = |ψ|`, `M s = |{f ≥ s}|`, `N h s = |A_s|` (erosion set) and `E = d |B_1|^{1/d}`, we show
`h * ∫_0^∞ E * N h s ^ ((d-1)/d) ds ≤ h * (∫ |∇ψ| + ω_g(h) |K_h|)` (ENNReal form).
-/

@[expose] public section

open Set MeasureTheory Filter Topology
open scoped Pointwise ENNReal

namespace PDE.SobolevSharp

variable {d : ℕ}

/-- The constant `d * |B_1|^{1/d}` as an extended real. -/
noncomputable def sharpConst (d : ℕ) : ℝ≥0∞ :=
  (d : ℝ≥0∞) * volume (euclideanBall (0 : Vec d) 1) ^ ((1 : ℝ) / d)

theorem ofReal_mul_toReal_rpow {c : ℝ} (hc : 0 ≤ c) {m : ℝ≥0∞} (hm : m ≠ ⊤) {e : ℝ}
    (he : 0 ≤ e) : ENNReal.ofReal (c * m.toReal ^ e) = ENNReal.ofReal c * m ^ e := by
  rw [ENNReal.ofReal_mul hc, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg he,
    ENNReal.ofReal_toReal hm]

theorem ofReal_sharpConst_mul (hd : 0 < d) (h : ℝ) (hh : 0 ≤ h) {m : ℝ≥0∞} (hm : m ≠ ⊤) :
    ENNReal.ofReal ((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal ^ ((1 : ℝ) / d) * h *
        m.toReal ^ (((d : ℝ) - 1) / d)) =
      ENNReal.ofReal h * (sharpConst d * m ^ (((d : ℝ) - 1) / d)) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have he : 0 ≤ ((d : ℝ) - 1) / d := div_nonneg (by linarith) (by linarith)
  have hB := volume_euclideanBall_ne_top (0 : Vec d) (R := 1) zero_le_one
  have hc : 0 ≤ (d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal ^ ((1 : ℝ) / d) := by
    positivity
  have hre : (d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal ^ ((1 : ℝ) / d) * h *
      m.toReal ^ (((d : ℝ) - 1) / d) = h * (((d : ℝ) *
        (volume (euclideanBall (0 : Vec d) 1)).toReal ^ ((1 : ℝ) / d)) *
        m.toReal ^ (((d : ℝ) - 1) / d)) := by ring
  rw [hre, ENNReal.ofReal_mul hh, ofReal_mul_toReal_rpow hc hm he]
  have : ENNReal.ofReal ((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal ^
      ((1 : ℝ) / d)) = sharpConst d := by
    have h1 : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
    rw [ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_rpow_of_nonneg
      ENNReal.toReal_nonneg h1, ENNReal.ofReal_toReal hB, ENNReal.ofReal_natCast]
    rfl
  rw [this]

section Pointwise

variable {f : Vec d → ℝ}

/-- Pointwise (extended) form of the Brunn--Minkowski step, for `d ≥ 2`. -/
theorem bm_step_ennreal (hd : 2 ≤ d)
    (BM : ∀ A B : Set (Vec d), IsCompact A → IsCompact B → A.Nonempty → B.Nonempty →
      volume A ^ ((1 : ℝ) / d) + volume B ^ ((1 : ℝ) / d) ≤ volume (A + B) ^ ((1 : ℝ) / d))
    (hf : Continuous f) (hfc : HasCompactSupport f) {h s : ℝ} (hh : 0 < h) (hs : 0 < s) :
    ENNReal.ofReal h * (sharpConst d * volume (erosionSet f h s) ^ (((d : ℝ) - 1) / d)) +
        volume (erosionSet f h s) ≤ volume {x | s ≤ f x} := by
  have hN : volume (erosionSet f h s) ≠ ⊤ := (isCompact_erosionSet hf hfc hh.le hs).measure_ne_top
  have hM : volume {x | s ≤ f x} ≠ ⊤ := (isCompact_superlevel hf hfc hs).measure_ne_top
  have key := bm_step_of_two_le hd BM hf hfc hh hs
  rw [← ofReal_sharpConst_mul (by omega) h hh.le hN]
  have h1 := ENNReal.ofReal_le_ofReal key
  rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hN,
    ENNReal.ofReal_toReal hM] at h1
  calc _ ≤ (volume {x | s ≤ f x} - volume (erosionSet f h s)) + volume (erosionSet f h s) :=
        add_le_add_left h1 _
    _ = volume {x | s ≤ f x} :=
        tsub_add_cancel_of_le (measure_mono (erosionSet_subset_superlevel hh.le))

end Pointwise

section Integrated

variable {ψ : Vec d → ℝ}

theorem erode_nonneg_abs (hψ : Continuous ψ) (hc : HasCompactSupport ψ) {h : ℝ} (hh : 0 ≤ h)
    (x : Vec d) : 0 ≤ erode (fun y => |ψ y|) h x := by
  rw [← mem_erosionSet_iff (continuous_abs_comp hψ) (hasCompactSupport_abs_comp hc) hh]
  intro v _
  exact abs_nonneg _

theorem integrable_abs_comp (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Integrable fun y => |ψ y| :=
  (continuous_abs_comp hψ).integrable_of_hasCompactSupport (hasCompactSupport_abs_comp hc)

theorem integrable_erode_abs (hψ : Continuous ψ) (hc : HasCompactSupport ψ) {h : ℝ}
    (hh : 0 ≤ h) : Integrable (erode (fun y => |ψ y|) h) := by
  refine (integrable_abs_comp hψ hc).mono'
    (continuous_erode (continuous_abs_comp hψ) hh).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (erode_nonneg_abs hψ hc hh x)]
  exact erode_le_self (continuous_abs_comp hψ) (hasCompactSupport_abs_comp hc) hh

/-- The layer-cake form of the erosion estimate. -/
theorem sharp_step_integrated (hd : 2 ≤ d)
    (BM : ∀ A B : Set (Vec d), IsCompact A → IsCompact B → A.Nonempty → B.Nonempty →
      volume A ^ ((1 : ℝ) / d) + volume B ^ ((1 : ℝ) / d) ≤ volume (A + B) ^ ((1 : ℝ) / d))
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) {h : ℝ} (hh : 0 < h) :
    ∫⁻ s in Ioi (0 : ℝ), sharpConst d *
        volume (erosionSet (fun y => |ψ y|) h s) ^ (((d : ℝ) - 1) / d) ≤
      ENNReal.ofReal ((∫ x, gradNorm ψ x) +
        modulus (gradNorm ψ) h * (volume (supportNbhd ψ h)).toReal) := by
  have hf := continuous_abs_comp hψ.continuous
  have hfc := hasCompactSupport_abs_comp hc
  set I := ∫⁻ s in Ioi (0 : ℝ), sharpConst d *
        volume (erosionSet (fun y => |ψ y|) h s) ^ (((d : ℝ) - 1) / d) with hI
  have hL1 := lintegral_eq_lintegral_meas_le (volume : Measure (Vec d))
    (f := fun y => |ψ y|) (Eventually.of_forall fun x => abs_nonneg _) hf.measurable.aemeasurable
  have hL2 := lintegral_eq_lintegral_meas_le (volume : Measure (Vec d))
    (f := erode (fun y => |ψ y|) h)
    (Eventually.of_forall fun x => erode_nonneg_abs hψ.continuous hc hh.le x)
    (measurable_erode hf hh.le).aemeasurable
  have hpt : ∀ s ∈ Ioi (0 : ℝ), ENNReal.ofReal h * (sharpConst d *
      volume (erosionSet (fun y => |ψ y|) h s) ^ (((d : ℝ) - 1) / d)) +
      volume {x | s ≤ erode (fun y => |ψ y|) h x} ≤ volume {x | s ≤ |ψ x|} := by
    intro s hs
    rw [← erosionSet_eq_preimage hf hfc hh.le]
    exact bm_step_ennreal hd BM hf hfc hh hs
  have hint : ENNReal.ofReal h * I + ∫⁻ x, ENNReal.ofReal (erode (fun y => |ψ y|) h x) ≤
      ∫⁻ x, ENNReal.ofReal |ψ x| := by
    rw [hL1, hL2, hI, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (le_lintegral_add _ _).trans ?_
    exact setLIntegral_mono' measurableSet_Ioi hpt
  have hfi := integrable_abs_comp hψ.continuous hc
  have hei := integrable_erode_abs hψ.continuous hc hh.le
  have hnn : 0 ≤ ∫ x, erode (fun y => |ψ y|) h x :=
    integral_nonneg fun x => erode_nonneg_abs hψ.continuous hc hh.le x
  have hR := integral_abs_sub_erode_le hψ hc hh.le
  rw [integral_sub hfi hei] at hR
  have hω := modulus_nonneg (continuous_gradNorm hψ) (hasCompactSupport_gradNorm hc) hh.le
  have hG : 0 ≤ ∫ x, gradNorm ψ x := integral_nonneg fun x => vecEuclideanNorm_nonneg _
  have hRn : 0 ≤ (∫ x, gradNorm ψ x) +
      modulus (gradNorm ψ) h * (volume (supportNbhd ψ h)).toReal :=
    add_nonneg hG (mul_nonneg hω ENNReal.toReal_nonneg)
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (Eventually.of_forall fun x => abs_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hei
      (Eventually.of_forall fun x => erode_nonneg_abs hψ.continuous hc hh.le x)] at hint
  have h2 : ENNReal.ofReal (∫ x, |ψ x|) ≤ ENNReal.ofReal (∫ x, erode (fun y => |ψ y|) h x) +
      ENNReal.ofReal h * ENNReal.ofReal ((∫ x, gradNorm ψ x) +
        modulus (gradNorm ψ) h * (volume (supportNbhd ψ h)).toReal) := by
    rw [← ENNReal.ofReal_mul hh.le, ← ENNReal.ofReal_add hnn (mul_nonneg hh.le hRn)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  rw [add_comm] at hint
  exact (ENNReal.mul_le_mul_iff_right (by simpa using hh) ENNReal.ofReal_ne_top).mp
    ((ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).mp (hint.trans h2))

end Integrated

end PDE.SobolevSharp
