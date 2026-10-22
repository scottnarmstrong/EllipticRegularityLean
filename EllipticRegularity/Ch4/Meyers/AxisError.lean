module

public import EllipticRegularity.Ch4.Meyers.AxisCutoff
public import EllipticRegularity.Ch4.Meyers.NonIntegrability

/-!
# The cutoff error term at the codimension-two set

For `f ∈ L²(U)` and a test function `φ`, `∫_U f φ ∂_i η_ε → 0`: the gradient of the cutoff is of
size `1/ε` on a set of volume `O(ε²)`, and `‖f‖_{L²}` of that set tends to zero.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE.Ch4Meyers

open MeasureTheory Set Filter

variable {d : ℕ} {w : Fin d → ℝ}

theorem tendsto_lintegral_sq_indicator_zero {ν : Measure (Vec d)} {f : Vec d → ℝ}
    (hf : MemLp f 2 ν) {A : ℕ → Set (Vec d)} (hA : Tendsto (fun n => ν (A n)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x in A n, ‖f x‖ₑ ^ (2 : ℝ) ∂ν) atTop (𝓝 0) := by
  have hfin : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂ν ≠ ∞ := by
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2) (by norm_num)
      (by norm_num) hf.eLpNorm_lt_top
    simpa using this.ne
  exact tendsto_setLIntegral_zero hfin hA

theorem tendsto_lintegral_axis_error (hw : ∀ i, w i = 0 ∨ w i = 1) {i0 i1 : Fin d}
    (hi : i0 ≠ i1) (h0 : w i0 = 1) (h1 : w i1 = 1) {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (φ : WeakTestFunction U) (i : Fin d)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x in U,
      ENNReal.ofReal |f x * φ x * fderiv ℝ (axisCutoff w (ε n)) x (basisVec i)|)
      atTop (𝓝 0) := by
  set ν : Measure (Vec d) := volume.restrict U with hν
  obtain ⟨C, hC⟩ := φ.contDiff.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hC0 : 0 ≤ C := (norm_nonneg (φ 0)).trans (hC 0)
  obtain ⟨R₀, hR₀⟩ := isBounded_iff_forall_norm_le.mp φ.hasCompactSupport.isCompact.isBounded
  set R : ℝ := |R₀| with hRdef
  have hR : ∀ x ∈ tsupport φ.toFun, ∀ j, |x j| ≤ R := fun x hx j =>
    (le_trans (by simpa [Real.norm_eq_abs] using norm_le_pi_norm x j) (hR₀ x hx)).trans
      (le_abs_self _)
  have hR0 : 0 ≤ R := abs_nonneg _
  set M : ℝ := (2 * R) ^ numOther i0 i1 with hM
  have hM0 : 0 ≤ M := by positivity
  let A : ℕ → Set (Vec d) := fun n => {x | axisSq w x ≤ 4 * ε n ^ 2} ∩ tsupport φ.toFun
  have hAmeas : ∀ n, MeasurableSet (A n) := fun n =>
    (isClosed_le (contDiff_axisSq w).continuous continuous_const).measurableSet.inter
      (isClosed_tsupport _).measurableSet
  have hAbox : ∀ n, A n ⊆ dyadicBox i0 i1 (2 * ε n) R := by
    intro n x hx j _
    obtain ⟨hs, hxt⟩ := hx
    have hs : axisSq w x ≤ 4 * ε n ^ 2 := hs
    simp only [mem_Icc]
    split_ifs with hj
    · have hb : ∀ k, w k = 1 → |x k| ≤ 2 * ε n := by
        intro k hk
        have := sq_le_axisSq hw x hk
        exact abs_le_of_sq_le_sq (by nlinarith) (by linarith [hε n])
      rcases hj with rfl | rfl
      · exact abs_le.mp (hb _ h0)
      · exact abs_le.mp (hb _ h1)
    · exact abs_le.mp (hR x hxt j)
  have hvolA : ∀ n, ν (A n) ≤ ENNReal.ofReal ((2 * (2 * ε n)) ^ 2 * M) := by
    intro n
    calc ν (A n) ≤ volume (A n) := Measure.restrict_le_self _
      _ ≤ volume (dyadicBox i0 i1 (2 * ε n) R) := measure_mono (hAbox n)
      _ = _ := volume_dyadicBox hi (by linarith [hε n]) hR0
  have hνA0 : Tendsto (fun n => ν (A n)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
      (Eventually.of_forall fun n => bot_le) (Eventually.of_forall hvolA)
    have : Tendsto (fun n => (2 * (2 * ε n)) ^ 2 * M) atTop (𝓝 0) := by
      have := (((hε0.const_mul 2).const_mul 2).pow 2).mul_const M
      simpa using this
    simpa using ENNReal.tendsto_ofReal this
  have ha : Tendsto (fun n => ∫⁻ x in A n, ‖f x‖ₑ ^ (2 : ℝ) ∂ν) atTop (𝓝 0) :=
    tendsto_lintegral_sq_indicator_zero hf hνA0
  -- the pointwise bound
  have hpoint : ∀ n x, ENNReal.ofReal |f x * φ x * fderiv ℝ (axisCutoff w (ε n)) x (basisVec i)| ≤
      ENNReal.ofReal (11 * C / ε n) * (A n).indicator (fun x => ‖f x‖ₑ) x := by
    intro n x
    by_cases hx : x ∈ A n
    · rw [indicator_of_mem hx, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (by
        have := hε n; positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hd := abs_partial_axisCutoff_le hw (hε n) x i
      have hs1 : axisSq w x ≤ 4 * ε n ^ 2 := hx.1
      simp only [hs1, ↓reduceIte, mul_one] at hd
      rw [abs_mul, abs_mul]
      have hφx : |φ x| ≤ C := by simpa [Real.norm_eq_abs] using hC x
      calc |f x| * |φ x| * |fderiv ℝ (axisCutoff w (ε n)) x (basisVec i)|
          ≤ |f x| * C * (11 / ε n) := by
            gcongr
        _ = 11 * C / ε n * |f x| := by ring
    · rw [indicator_of_notMem hx, mul_zero, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero]
      by_cases hs : axisSq w x ≤ 4 * ε n ^ 2
      · have hxt : x ∉ tsupport φ.toFun := fun h => hx ⟨hs, h⟩
        have : φ x = 0 := image_eq_zero_of_notMem_tsupport hxt
        simp [this]
      · have hd := abs_partial_axisCutoff_le hw (hε n) x i
        simp only [hs, ↓reduceIte, mul_zero] at hd
        have : fderiv ℝ (axisCutoff w (ε n)) x (basisVec i) = 0 := abs_nonpos_iff.mp hd
        simp [this]
  -- Hölder
  have hholder : ∀ n, ∫⁻ x in A n, ‖f x‖ₑ ∂ν ≤
      (∫⁻ x in A n, ‖f x‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) * ν (A n) ^ (1 / (2 : ℝ)) := by
    intro n
    have hm : AEMeasurable (fun x => ‖f x‖ₑ) (ν.restrict (A n)) :=
      hf.aestronglyMeasurable.enorm.mono_measure Measure.restrict_le_self
    have := ENNReal.lintegral_mul_le_Lp_mul_Lq (ν.restrict (A n)) Real.HolderConjugate.two_two
      hm (aemeasurable_const (b := (1 : ℝ≥0∞)))
    simpa using this
  have hconst : ∀ n, ENNReal.ofReal (11 * C / ε n) *
      ENNReal.ofReal ((2 * (2 * ε n)) ^ 2 * M) ^ (1 / (2 : ℝ)) =
      ENNReal.ofReal (44 * C * Real.sqrt M) := by
    intro n
    have hεn := hε n
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity), show (2 * (2 * ε n)) ^ 2 =
      (4 * ε n) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    field_simp
    ring
  have hbound : ∀ n, ∫⁻ x in U,
      ENNReal.ofReal |f x * φ x * fderiv ℝ (axisCutoff w (ε n)) x (basisVec i)| ≤
      ENNReal.ofReal (44 * C * Real.sqrt M) *
        (∫⁻ x in A n, ‖f x‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) := by
    intro n
    calc ∫⁻ x in U, ENNReal.ofReal |f x * φ x * fderiv ℝ (axisCutoff w (ε n)) x (basisVec i)|
        ≤ ∫⁻ x, ENNReal.ofReal (11 * C / ε n) * (A n).indicator (fun x => ‖f x‖ₑ) x ∂ν :=
          lintegral_mono (hpoint n)
      _ = ENNReal.ofReal (11 * C / ε n) * ∫⁻ x in A n, ‖f x‖ₑ ∂ν := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator (hAmeas n)]
      _ ≤ ENNReal.ofReal (11 * C / ε n) *
            ((∫⁻ x in A n, ‖f x‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) * ν (A n) ^ (1 / (2 : ℝ))) :=
          mul_le_mul_right (hholder n) _
      _ ≤ ENNReal.ofReal (11 * C / ε n) *
            ((∫⁻ x in A n, ‖f x‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) *
              ENNReal.ofReal ((2 * (2 * ε n)) ^ 2 * M) ^ (1 / (2 : ℝ))) := by
          gcongr
          exact hvolA n
      _ = _ := by
          rw [← hconst n]; ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
    (Eventually.of_forall fun n => bot_le) (Eventually.of_forall hbound)
  have := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0 |>.comp ha
  have h2 : Tendsto (fun n => ENNReal.ofReal (44 * C * Real.sqrt M) *
      (∫⁻ x in A n, ‖f x‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ))) atTop
      (𝓝 (ENNReal.ofReal (44 * C * Real.sqrt M) * (0 : ℝ≥0∞) ^ (1 / (2 : ℝ)))) :=
    ENNReal.Tendsto.const_mul this (Or.inr ENNReal.ofReal_ne_top)
  simpa [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using h2

end PDE.Ch4Meyers
