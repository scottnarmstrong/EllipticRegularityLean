module

public import PDEFoundation.Analysis.Gehring.Absorption
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# The truncated maximal function (Lemma 4.6)

`∫ V_L^{1+ε} ≤ K I_L` and `∫ h V_L^ε ≤ 2 ‖h‖_{L^{1+ε}} I_L^{ε/(1+ε)}`.
-/

@[expose] public section

namespace PDE.Gehring

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

/-- **`∫ V_L^{1+ε} ≤ K I_L`** with `K = 2 · 3^d (1+ε) c^{-b} / b`, `b = 1-θ+ε`. -/
theorem lintegral_truncV_le (hd : 0 < d) {g : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hgm : Measurable g) (hg : Integrable g volume)
    {ε L : ℝ} (hε : 0 < ε) (hL : 0 < L) :
    ∫⁻ x, (truncV g L x) ^ (1 + ε) ≤
      ENNReal.ofReal (2 * 3 ^ d * (1 + ε) *
        (gehringC d ^ (-(1 - gehringTheta d + ε)) / (1 - gehringTheta d + ε))) *
        truncMoment g L ε := by
  have hθ := gehringTheta_pos hd
  have hθ1 := gehringTheta_lt_one d
  set c := gehringC d with hcdef
  set θ := gehringTheta d with hθdef
  set b := 1 - θ + ε with hb
  have hVm : Measurable (gehringV g) := by
    have hlsc : LowerSemicontinuous (cubeMaximal fun y => g y ^ gehringTheta d) :=
      lowerSemicontinuous_iff_isOpen_preimage.2 fun s => isOpen_lt_cubeMaximal _ s
    exact hlsc.measurable.pow_const _
  have hlay := lintegral_layer (Φ := gehringV g) (w := fun _ => (1 : ℝ≥0∞))
    hVm.aemeasurable aemeasurable_const (p := 1 + ε) (by linarith) hL
  simp only [one_mul, setLIntegral_const] at hlay
  have hlay' : ∫⁻ x, (truncV g L x) ^ (1 + ε) =
      ∫⁻ t in Ioo 0 L, ENNReal.ofReal ((1 + ε) * t ^ ε) * volume (gehringE g t) := by
    show ∫⁻ x, (min (gehringV g x) (ENNReal.ofReal L)) ^ (1 + ε) = _
    rw [← hlay]
    refine setLIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
    rw [add_sub_cancel_left]
    rfl
  have hweak : ∀ t ∈ Ioo (0 : ℝ) L, ENNReal.ofReal ((1 + ε) * t ^ ε) * volume (gehringE g t) ≤
      ENNReal.ofReal (2 * 3 ^ d * (1 + ε)) * (ENNReal.ofReal (t ^ (ε - θ)) *
        ∫⁻ y in {y | c * t < g y}, ENNReal.ofReal (g y ^ θ)) := by
    intro t ht
    have h1 := volume_gehringE_le hd hg0 hg ht.1
    have key : ENNReal.ofReal ((1 + ε) * t ^ ε) * ENNReal.ofReal (2 * 3 ^ d / t ^ θ) =
        ENNReal.ofReal (2 * 3 ^ d * (1 + ε)) * ENNReal.ofReal (t ^ (ε - θ)) := by
      have htp : 0 < t := ht.1
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Real.rpow_sub htp]
      ring
    calc ENNReal.ofReal ((1 + ε) * t ^ ε) * volume (gehringE g t)
        ≤ ENNReal.ofReal ((1 + ε) * t ^ ε) * (ENNReal.ofReal (2 * 3 ^ d / t ^ θ) *
          ∫⁻ y in {y | c * t < g y}, ENNReal.ofReal (g y ^ θ)) := by gcongr
      _ = (ENNReal.ofReal ((1 + ε) * t ^ ε) * ENNReal.ofReal (2 * 3 ^ d / t ^ θ)) *
          ∫⁻ y in {y | c * t < g y}, ENNReal.ofReal (g y ^ θ) := by ring
      _ = _ := by rw [key]; ring
  have hcore := core_bound hd hg0 hgm hε hL
  rw [hlay']
  calc ∫⁻ t in Ioo 0 L, ENNReal.ofReal ((1 + ε) * t ^ ε) * volume (gehringE g t)
      ≤ ∫⁻ t in Ioo 0 L, ENNReal.ofReal (2 * 3 ^ d * (1 + ε)) *
          (ENNReal.ofReal (t ^ (ε - θ)) *
            ∫⁻ y in {y | c * t < g y}, ENNReal.ofReal (g y ^ θ)) :=
        setLIntegral_mono' measurableSet_Ioo hweak
    _ = ENNReal.ofReal (2 * 3 ^ d * (1 + ε)) * ∫⁻ t in Ioo 0 L, ENNReal.ofReal (t ^ (ε - θ)) *
          ∫⁻ y in {y | c * t < g y}, ENNReal.ofReal (g y ^ θ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 * 3 ^ d * (1 + ε)) * (ENNReal.ofReal (c ^ (-b) / b) *
          truncMoment g L ε) := by gcongr
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

end PDE.Gehring
