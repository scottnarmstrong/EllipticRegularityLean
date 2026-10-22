module

public import EllipticRegularity.Parabolic.WeakHarnack.MeasuresCylinders
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Conversion between the statement's form and normalized `eLpNorm` bounds

Pure measure theory, no PDE.  See `weakHarnackAvg_le_essInf_of_eps` for the combined statement:
the `ε ↓ 0` argument together with the translation between
* `(vol(Q⁻)⁻¹ ∫⁻_{Q⁻} ofReal(u)^r)^(1/r)` and `‖v‖_{L^r(posCyl 1/2, normalized on posCyl 1)}`,
* `essInf (ofReal ∘ v)` over `Q⁺ = negCylInner d (1/2)` and `‖1/v‖_{L^∞(Q⁺)}`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace PDE.Parabolic.WeakHarnack

variable {d : ℕ}

/-- The left-hand side of the statement `PDE.parabWeakHarnack` for a function `u`
(`Q⁻ = B_{1/2} × (-3/4,-1/2)`, exponent `r`). -/
noncomputable def weakHarnackAvg (d : ℕ) (r : ℝ) (u : Vec d × ℝ → ℝ) : ℝ≥0∞ :=
  ((volume (euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioo (-3 / 4 : ℝ) (-1 / 2)))⁻¹ *
    ∫⁻ z in euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioo (-3 / 4 : ℝ) (-1 / 2),
      ENNReal.ofReal (u z) ^ r) ^ (1 / r)

/-- The volume ratio `vol(posCyl 1) / vol(posCyl 1/2) = 2 (3/2)^d`. -/
noncomputable def posVolRatio (d : ℕ) : ℝ := 2 * (3 / 2 : ℝ) ^ d

theorem posVolRatio_pos (d : ℕ) : 0 < posVolRatio d := by unfold posVolRatio; positivity

theorem volume_posCyl_one_eq :
    volume (posCyl d 1) = ENNReal.ofReal (posVolRatio d) * volume (posCyl d (1 / 2)) := by
  rw [posCyl_one, posCyl_half, volume_prod_ball, volume_prod_ball,
    volume_euclideanBall_eq_unit_mul_of_pos _ (by norm_num : (0 : ℝ) < 3 / 4),
    volume_euclideanBall_eq_unit_mul_of_pos _ (by norm_num : (0 : ℝ) < 1 / 2),
    Real.volume_Ioo, Real.volume_Ioo]
  have h1 : (3 / 4 : ℝ) ^ d = (3 / 2) ^ d * (1 / 2) ^ d := by rw [← mul_pow]; norm_num
  have h2 : ENNReal.ofReal ((3 / 4 : ℝ) ^ d) =
      ENNReal.ofReal ((3 / 2 : ℝ) ^ d) * ENNReal.ofReal ((1 / 2 : ℝ) ^ d) := by
    rw [h1, ENNReal.ofReal_mul (by positivity)]
  have h3 : ENNReal.ofReal ((-3 / 8 : ℝ) - (-7 / 8)) = ENNReal.ofReal 2 *
      ENNReal.ofReal ((-1 / 2 : ℝ) - (-3 / 4)) := by
    rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num
  have h4 : ENNReal.ofReal (posVolRatio d) = ENNReal.ofReal 2 * ENNReal.ofReal ((3 / 2 : ℝ) ^ d) := by
    rw [posVolRatio, ENNReal.ofReal_mul (by norm_num)]
  rw [h2, h3, h4]
  ring

/-- The inverse of `vol(Q⁻)` in terms of that of `posCyl 1`. -/
theorem inv_volume_posCyl_half :
    (volume (posCyl d (1 / 2)))⁻¹ =
      ENNReal.ofReal (posVolRatio d) * (volume (posCyl d 1))⁻¹ := by
  have hQ0 : volume (posCyl d (1 / 2)) ≠ 0 := (volume_posCyl_pos (by norm_num)).ne'
  have hQt := volume_posCyl_ne_top (d := d) (σ := 1 / 2) le_rfl
  have hr0 : ENNReal.ofReal (posVolRatio d) ≠ 0 := by
    simpa using posVolRatio_pos d
  rw [volume_posCyl_one_eq, ENNReal.mul_inv (Or.inl hr0) (Or.inl ENNReal.ofReal_ne_top),
    ← mul_assoc, ENNReal.mul_inv_cancel hr0 ENNReal.ofReal_ne_top, one_mul]

/-- `eLpNorm` over the normalized measure of `posCyl 1`, restricted to `Q⁻ = posCyl 1/2`. -/
theorem eLpNorm_posCyl_half {r : ℝ} (hr : 0 < r) {v : Vec d × ℝ → ℝ} (hv : Measurable v) :
    eLpNorm v (ENNReal.ofReal r) ((cylMeasure (posCyl d 1)).restrict (posCyl d (1 / 2))) =
      ((volume (posCyl d 1))⁻¹ * ∫⁻ z in posCyl d (1 / 2), ‖v z‖ₑ ^ r) ^ (1 / r) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hr) ENNReal.ofReal_ne_top
      hv.aestronglyMeasurable,
    cylMeasure_restrict (measurableSet_posCyl _) (posCyl_mono (by norm_num) (by norm_num)),
    lintegral_smul_measure, ENNReal.toReal_ofReal hr.le, smul_eq_mul]

/-- Conversion (a): monotone comparison of the statement's average with the normalized `L^r` norm. -/
theorem weakHarnackAvg_le_eLpNorm {r : ℝ} (hr : 0 < r) (u : Vec d × ℝ → ℝ) {v : Vec d × ℝ → ℝ}
    (hv : Measurable v) (huv : ∀ᵐ z ∂(volume.restrict (posCyl d (1 / 2))), u z ≤ v z) :
    weakHarnackAvg d r u ≤ ENNReal.ofReal ((posVolRatio d) ^ (1 / r)) *
      eLpNorm v (ENNReal.ofReal r) ((cylMeasure (posCyl d 1)).restrict (posCyl d (1 / 2))) := by
  have hle : ∫⁻ z in posCyl d (1 / 2), ENNReal.ofReal (u z) ^ r ≤
      ∫⁻ z in posCyl d (1 / 2), ‖v z‖ₑ ^ r := by
    apply lintegral_mono_ae
    filter_upwards [huv] with z hz
    refine ENNReal.rpow_le_rpow ?_ hr.le
    calc ENNReal.ofReal (u z) ≤ ENNReal.ofReal (v z) := ENNReal.ofReal_le_ofReal hz
      _ ≤ ‖v z‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  rw [eLpNorm_posCyl_half hr hv, ← ENNReal.ofReal_rpow_of_nonneg (posVolRatio_pos d).le
    (by positivity), ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  unfold weakHarnackAvg
  rw [← posCyl_half]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  rw [inv_volume_posCyl_half, mul_assoc]
  gcongr

/-- Conversion (c), monotonicity: `LHS(u) ≤ LHS(u + ε)`. -/
theorem weakHarnackAvg_mono {r : ℝ} (hr : 0 < r) (u v : Vec d × ℝ → ℝ) (huv : ∀ z, u z ≤ v z) :
    weakHarnackAvg d r u ≤ weakHarnackAvg d r v := by
  unfold weakHarnackAvg
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  gcongr with z
  exact huv z

/-! ### The essential infimum over `Q⁺` -/

/-- `L^∞` norm over the normalized measure of `negCyl 1`, restricted to `Q⁺`, is the essential
supremum for Lebesgue measure on `Q⁺`. -/
theorem eLpNorm_top_negCylInner {g : Vec d × ℝ → ℝ} (hg : Measurable g) :
    eLpNorm g ⊤ ((cylMeasure (negCyl d 1)).restrict (negCylInner d (1 / 2))) =
      essSup (fun z => ‖g z‖ₑ) (volume.restrict (negCylInner d (1 / 2))) := by
  have h0 : (volume (negCyl d 1))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (volume_negCyl_ne_top (by norm_num))
  have hsub : negCylInner d (1 / 2) ⊆ negCyl d 1 :=
    (negCylInner_mono (by norm_num) (by norm_num)).trans
      ((negCylInner_one (d := d)).subset.trans (negCyl_mono (by norm_num) (by norm_num)))
  rw [cylMeasure_restrict (measurableSet_negCylInner _) hsub,
    eLpNorm_exponent_top hg.aestronglyMeasurable, eLpNormEssSup_eq_essSup_enorm,
    essSup_ennreal_smul_measure h0]

/-- Conversion (b), first half: `‖1/v‖_{L^∞(Q⁺)}⁻¹ = essInf (ofReal ∘ v)`. -/
theorem eLpNorm_top_inv_negCylInner {v : Vec d × ℝ → ℝ} (hv : Measurable v)
    (hpos : ∀ᵐ z ∂(volume.restrict (negCylInner d (1 / 2))), 0 < v z) :
    (eLpNorm (fun z => 1 / v z) ⊤ ((cylMeasure (negCyl d 1)).restrict (negCylInner d (1 / 2))))⁻¹ =
      essInf (fun z => ENNReal.ofReal (v z)) (volume.restrict (negCylInner d (1 / 2))) := by
  rw [eLpNorm_top_negCylInner (by fun_prop)]
  unfold essSup essInf
  rw [ENNReal.inv_limsup]
  apply Filter.liminf_congr
  filter_upwards [hpos] with z hz
  rw [Real.enorm_eq_ofReal_abs, abs_of_pos (by positivity), one_div,
    ENNReal.ofReal_inv_of_pos hz, inv_inv]

/-- Conversion (b), second half: the essential infimum is additive in constants. -/
theorem essInf_ofReal_add_const {α : Type*} [MeasurableSpace α] {μ : Measure α} (hμ : μ ≠ 0)
    {u : α → ℝ} (hu : ∀ᵐ z ∂μ, 0 ≤ u z) {ε : ℝ} (hε : 0 ≤ ε) :
    essInf (fun z => ENNReal.ofReal (u z + ε)) μ =
      essInf (fun z => ENNReal.ofReal (u z)) μ + ENNReal.ofReal ε := by
  have : NeBot (ae μ) := ae_neBot.2 hμ
  have h1 : essInf (fun z => ENNReal.ofReal (u z + ε)) μ =
      essInf (fun z => ENNReal.ofReal (u z) + ENNReal.ofReal ε) μ := by
    apply essInf_congr_ae
    filter_upwards [hu] with z hz
    exact ENNReal.ofReal_add hz hε
  rw [h1]
  unfold essInf
  exact liminf_add_const _ _ _ (by isBoundedDefault) (by isBoundedDefault)

/-- Conversion (c), the `ε ↓ 0` step. -/
theorem le_mul_essInf_of_forall_eps {α : Type*} [MeasurableSpace α] {μ : Measure α} (hμ : μ ≠ 0)
    {u : α → ℝ} (hu : ∀ᵐ z ∂μ, 0 ≤ u z) {X : ℝ≥0∞} {C : ℝ} (hC : 0 < C)
    (h : ∀ ε : ℝ, 0 < ε → X ≤ ENNReal.ofReal C * essInf (fun z => ENNReal.ofReal (u z + ε)) μ) :
    X ≤ ENNReal.ofReal C * essInf (fun z => ENNReal.ofReal (u z)) μ := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε' hε' _
  have hε : 0 < (ε' : ℝ) / C := by positivity
  refine (h _ hε).trans ?_
  rw [essInf_ofReal_add_const hμ hu hε.le, mul_add, ← ENNReal.ofReal_mul hC.le,
    mul_div_cancel₀ _ hC.ne', ENNReal.ofReal_coe_nnreal]

/-- Conversion (d): combining the two normalized bounds for a positive function `v ≥ u`. -/
theorem weakHarnackAvg_le_of_bounds {r : ℝ} (hr : 0 < r) {u v : Vec d × ℝ → ℝ} (hv : Measurable v)
    (huv : ∀ᵐ z ∂(volume.restrict (posCyl d (1 / 2))), u z ≤ v z)
    (hpos : ∀ᵐ z ∂(volume.restrict (negCylInner d (1 / 2))), 0 < v z)
    {C₁ C₂ k : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 < C₂)
    (h1 : eLpNorm v (ENNReal.ofReal r) ((cylMeasure (posCyl d 1)).restrict (posCyl d (1 / 2))) ≤
      ENNReal.ofReal (C₁ * Real.exp k))
    (h2 : eLpNorm (fun z => 1 / v z) ⊤
        ((cylMeasure (negCyl d 1)).restrict (negCylInner d (1 / 2))) ≤
      ENNReal.ofReal (C₂ * Real.exp (-k))) :
    weakHarnackAvg d r u ≤ ENNReal.ofReal ((posVolRatio d) ^ (1 / r) * C₁ * C₂) *
      essInf (fun z => ENNReal.ofReal (v z)) (volume.restrict (negCylInner d (1 / 2))) := by
  have hE : ENNReal.ofReal (Real.exp k / C₂) ≤
      essInf (fun z => ENNReal.ofReal (v z)) (volume.restrict (negCylInner d (1 / 2))) := by
    rw [← eLpNorm_top_inv_negCylInner hv hpos]
    have hp : 0 < C₂ * Real.exp (-k) := by positivity
    calc ENNReal.ofReal (Real.exp k / C₂) = (ENNReal.ofReal (C₂ * Real.exp (-k)))⁻¹ := by
          rw [← ENNReal.ofReal_inv_of_pos hp, Real.exp_neg]
          congr 1; field_simp
      _ ≤ _ := ENNReal.inv_le_inv.2 h2
  have hk : ENNReal.ofReal (Real.exp k) ≤ ENNReal.ofReal C₂ *
      essInf (fun z => ENNReal.ofReal (v z)) (volume.restrict (negCylInner d (1 / 2))) := by
    calc ENNReal.ofReal (Real.exp k) = ENNReal.ofReal C₂ * ENNReal.ofReal (Real.exp k / C₂) := by
          rw [← ENNReal.ofReal_mul hC₂.le]; congr 1; field_simp
      _ ≤ _ := by gcongr
  refine (weakHarnackAvg_le_eLpNorm hr u hv huv).trans ?_
  have hR : 0 ≤ (posVolRatio d) ^ (1 / r) := Real.rpow_nonneg (posVolRatio_pos d).le _
  calc ENNReal.ofReal ((posVolRatio d) ^ (1 / r)) * eLpNorm v (ENNReal.ofReal r)
        ((cylMeasure (posCyl d 1)).restrict (posCyl d (1 / 2)))
      ≤ ENNReal.ofReal ((posVolRatio d) ^ (1 / r)) * ENNReal.ofReal (C₁ * Real.exp k) := by
        gcongr
    _ = ENNReal.ofReal ((posVolRatio d) ^ (1 / r) * C₁) * ENNReal.ofReal (Real.exp k) := by
        rw [← ENNReal.ofReal_mul hR, ← ENNReal.ofReal_mul (mul_nonneg hR hC₁)]
        congr 1; ring
    _ ≤ ENNReal.ofReal ((posVolRatio d) ^ (1 / r) * C₁) * (ENNReal.ofReal C₂ *
        essInf (fun z => ENNReal.ofReal (v z)) (volume.restrict (negCylInner d (1 / 2)))) := by
        gcongr
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg hR hC₁)]

/-- **Final assembly** (conversions (a)-(d)): if for every `ε > 0` there is a level `k` such that
`v = u + ε` satisfies `‖v‖_{L^r(posCyl 1/2)} ≤ C₁ e^k` and `‖1/v‖_{L^∞(Q⁺)} ≤ C₂ e^{-k}` (normalized
`eLpNorm`s, constants independent of `ε` and `k`), then the statement's inequality holds for `u`
with constant `(2 (3/2)^d)^{1/r} C₁ C₂`. -/
theorem weakHarnackAvg_le_essInf_of_eps {r : ℝ} (hr : 0 < r) {u : Vec d × ℝ → ℝ} (hu : Measurable u)
    (hu0 : ∀ᵐ z ∂(volume.restrict (negCylInner d (1 / 2))), 0 ≤ u z)
    {C₁ C₂ : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (h : ∀ ε : ℝ, 0 < ε → ∃ k : ℝ,
      eLpNorm (fun z => u z + ε) (ENNReal.ofReal r)
          ((cylMeasure (posCyl d 1)).restrict (posCyl d (1 / 2))) ≤
        ENNReal.ofReal (C₁ * Real.exp k) ∧
      eLpNorm (fun z => 1 / (u z + ε)) ⊤
          ((cylMeasure (negCyl d 1)).restrict (negCylInner d (1 / 2))) ≤
        ENNReal.ofReal (C₂ * Real.exp (-k))) :
    weakHarnackAvg d r u ≤ ENNReal.ofReal ((posVolRatio d) ^ (1 / r) * C₁ * C₂) *
      essInf (fun z => ENNReal.ofReal (u z)) (volume.restrict (negCylInner d (1 / 2))) := by
  have hμ : (volume.restrict (negCylInner d (1 / 2)) : Measure (Vec d × ℝ)) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]
    exact (volume_negCylInner_pos (by norm_num)).ne'
  have hR : 0 < (posVolRatio d) ^ (1 / r) := Real.rpow_pos_of_pos (posVolRatio_pos d) _
  refine le_mul_essInf_of_forall_eps hμ hu0 (by positivity) ?_
  intro ε hε
  obtain ⟨k, hk1, hk2⟩ := h ε hε
  exact weakHarnackAvg_le_of_bounds hr (v := fun z => u z + ε) (hu.add_const ε)
    (Filter.Eventually.of_forall fun z => by linarith)
    (by filter_upwards [hu0] with z hz; linarith) hC₁.le hC₂ hk1 hk2

end PDE.Parabolic.WeakHarnack
