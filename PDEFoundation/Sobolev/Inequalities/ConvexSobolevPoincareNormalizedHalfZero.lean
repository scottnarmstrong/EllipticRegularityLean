module

public import PDEFoundation.Sobolev.Inequalities.ConvexSobolevPoincareNormalizedPerLayer
public import PDEFoundation.Sobolev.Inequalities.ConvexSobolevPoincareNormalizedLayer
public import PDEFoundation.Geometry.ConvexNormalization
public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.Measure.NormalizedLp

/-!
# Step 1: functions vanishing on half of a normalized domain, `p = 1`

For a bounded open convex `W` with `B₁ ⊆ W ⊆ B_{R_d}`, every nonnegative `v ∈ W^{1,1}(W)` whose
zero set has at least half the volume of `W` satisfies
`‖v‖_{L^{d/(d-1)}(W)} ≤ K_d ‖∇ v‖_{L¹(W)}`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE

variable {d : ℕ} {W : Set (Vec d)}

/-- The conjugate exponent `d' = d / (d - 1)` as a real number. -/
noncomputable def sobolevOneConjugate (d : ℕ) : ℝ := (d : ℝ) / (d - 1)

/-- The constant `M_d = 2 (2 R_d)^d / (d |B₁|)` of Step 1. -/
noncomputable def halfZeroRieszConstant (d : ℕ) : ℝ :=
  2 * (2 * convexNormalizationRadius d) ^ d /
    (d * (volume (euclideanBall (0 : Vec d) 1)).toReal)

/-- The constant `2^{d'} d |B₁|` of the weak-type bound. -/
noncomputable def halfZeroWeakConstant (d : ℕ) : ℝ :=
  2 ^ sobolevOneConjugate d * d * (volume (euclideanBall (0 : Vec d) 1)).toReal

/-- The constant `K_d = 4 M_d (2^{d'} d |B₁|)^{1/d'}` of Step 1. -/
noncomputable def halfZeroConstant (d : ℕ) : ℝ :=
  4 * halfZeroRieszConstant d * halfZeroWeakConstant d ^ (sobolevOneConjugate d)⁻¹

theorem halfZeroConstant_nonneg (d : ℕ) : 0 ≤ halfZeroConstant d := by
  unfold halfZeroConstant halfZeroRieszConstant halfZeroWeakConstant convexNormalizationRadius
  positivity

theorem sobolevOneConjugate_ge_one (hd : 2 ≤ d) : 1 ≤ sobolevOneConjugate d := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  unfold sobolevOneConjugate
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem two_mul_zpow_le {j k : ℤ} (h : j < k) : (2 : ℝ) * 2 ^ j ≤ 2 ^ k := by
  have : (2 : ℝ) ^ (j + 1) ≤ 2 ^ k := zpow_le_zpow_right₀ (by norm_num) (by omega)
  rw [zpow_add_one₀ (by norm_num)] at this
  linarith

/-- The layers of `v` have gradients supported on disjoint sets, so their `L¹` norms sum to at
most the `L¹` norm of `∇ v`. -/
theorem tsum_lintegral_layer_grad_le (hW : IsOpenBoundedConvexDomain W) (v : W1pFunction W 1) :
    ∑' k : ℤ, ∫⁻ y in W,
        ENNReal.ofReal (vecEuclideanNorm ((v.layer hW ((2 : ℝ) ^ k)).grad y)) ≤
      ∫⁻ y in W, ENNReal.ofReal (vecEuclideanNorm (v.grad y)) := by
  set g : Vec d → ℝ≥0∞ := fun y => ENNReal.ofReal (vecEuclideanNorm (v.grad y)) with hgdef
  have hg : AEMeasurable g (volumeOn W) :=
    ENNReal.measurable_ofReal.comp_aemeasurable v.aemeasurable_vecEuclideanNorm_grad
  have hv : AEMeasurable v.toFun (volumeOn W) := v.memLp.aestronglyMeasurable.aemeasurable
  let A : ℤ → Set (Vec d) := fun k => {y | (2 : ℝ) ^ k < v.toFun y ∧ v.toFun y < 2 * 2 ^ k}
  have hAn : ∀ k, NullMeasurableSet (A k) (volumeOn W) := fun k =>
    (nullMeasurableSet_lt aemeasurable_const hv).inter (nullMeasurableSet_lt hv aemeasurable_const)
  have hterm : ∀ k y, ENNReal.ofReal (vecEuclideanNorm ((v.layer hW ((2 : ℝ) ^ k)).grad y)) =
      (A k).indicator g y := by
    intro k y
    rw [W1pFunction.layer_grad]
    by_cases hy : y ∈ A k
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
      simp [vecEuclideanNorm_eq_zero_iff.2 (rfl : (0 : Vec d) = 0)]
  simp_rw [hterm]
  rw [← lintegral_tsum (fun k => hg.indicator₀ (hAn k))]
  refine lintegral_mono fun y => ?_
  have hunique : ∀ j k, y ∈ A j → y ∈ A k → j = k := by
    intro j k hj hk
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · linarith [hj.2, hk.1, two_mul_zpow_le hlt]
    · linarith [hk.2, hj.1, two_mul_zpow_le hlt]
  by_cases h : ∃ j, y ∈ A j
  · obtain ⟨j, hj⟩ := h
    rw [tsum_eq_single j]
    · rw [Set.indicator_of_mem hj]
    · intro k hk
      exact Set.indicator_of_notMem (fun hyk => hk (hunique k j hyk hj)) _
  · push Not at h
    simp [Set.indicator_of_notMem (h _)]

/-- **Step 1** (Theorem 1.9). If `B₁ ⊆ W ⊆ B_{R_d}` and `v ≥ 0` is a
`W^{1,1}(W)` function whose zero set has at least half the volume of `W`, then
`‖v‖_{L^{d/(d-1)}(W)} ≤ K_d ‖∇ v‖_{L¹(W)}`. -/
theorem eLpNormOn_halfZero_le (hd : 2 ≤ d) (hW : IsOpenBoundedConvexDomain W)
    (h1 : euclideanBall (0 : Vec d) 1 ⊆ W)
    (hR : W ⊆ euclideanBall (0 : Vec d) (convexNormalizationRadius d))
    (v : W1pFunction W 1) (hv0 : ∀ x, 0 ≤ v.toFun x)
    (hhalf : volume W ≤ 2 * volumeOn W {x | v.toFun x = 0}) :
    eLpNormOn W (ENNReal.ofReal (sobolevOneConjugate d)) v.toFun ≤
      ENNReal.ofReal (halfZeroConstant d) * euclideanFieldELpNormOn W 1 v.grad := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 hdpos
  have hRpos : 0 < convexNormalizationRadius d := by
    unfold convexNormalizationRadius; positivity
  set R := convexNormalizationRadius d with hRdef
  set ω := (volume (euclideanBall (0 : Vec d) 1)).toReal with hω
  have hωpos : 0 < ω :=
    ENNReal.toReal_pos (volume_euclideanBall_pos 0 one_pos).ne'
      (volume_euclideanBall_ne_top 0 zero_le_one)
  have := hW.isFiniteMeasure_volumeOn
  have hWD : HasEuclideanDiameterLE W (2 * R) := by
    intro x hx y hy
    have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt hRpos).1 (hR hx)
    have hy' := (mem_euclideanBall_iff_vecEuclideanNorm_lt hRpos).1 (hR hy)
    rw [sub_zero] at hx' hy'
    calc vecEuclideanNorm (x - y) = vecEuclideanNorm (x + -y) := by rw [sub_eq_add_neg]
      _ ≤ vecEuclideanNorm x + vecEuclideanNorm (-y) := vecEuclideanNorm_add_le _ _
      _ ≤ 2 * R := by rw [vecEuclideanNorm_neg]; linarith
  have hvm : AEMeasurable v.toFun (volumeOn W) := v.memLp.aestronglyMeasurable.aemeasurable
  obtain ⟨S, hSm, hSW, hS0, hSvol⟩ := exists_measurable_zero_set hW.measurableSet hvm hhalf
  have hSfin : volume S ≠ ⊤ := ne_top_of_le_ne_top hW.volume_ne_top (measure_mono hSW)
  have hballS : volume (euclideanBall (0 : Vec d) 1) ≤ 2 * volume S :=
    (measure_mono h1).trans hSvol
  have hSpos : 0 < volume S := by
    by_contra h
    have h0 : volume S = 0 := by simpa using h
    rw [h0, mul_zero] at hballS
    exact (volume_euclideanBall_pos (0 : Vec d) one_pos).ne' (le_zero_iff.1 hballS)
  have hωS : ω ≤ 2 * (volume S).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hSfin) hballS
    simpa [ENNReal.toReal_mul] using this
  have hSreal : 0 < (volume S).toReal := ENNReal.toReal_pos hSpos.ne' hSfin
  set M := halfZeroRieszConstant d with hMdef
  have hMpos : 0 < M := by
    have : 0 < halfZeroRieszConstant d := by unfold halfZeroRieszConstant; positivity
    exact this
  have hMS : (2 * R) ^ d / (d * (volume S).toReal) ≤ M := by
    rw [hMdef, halfZeroRieszConstant, div_le_div_iff₀ (by positivity) (by positivity)]
    have hp : 0 < (2 * R) ^ d := by positivity
    nlinarith [mul_nonneg (mul_nonneg hp.le hdpos.le) (sub_nonneg.2 hωS)]
  set q := sobolevOneConjugate d with hq
  have hq1 : 1 ≤ q := sobolevOneConjugate_ge_one hd
  have hq0 : 0 < q := by linarith
  set C₀ := halfZeroWeakConstant d with hC₀def
  have hC₀ : 0 ≤ C₀ := by
    have : 0 ≤ halfZeroWeakConstant d := by unfold halfZeroWeakConstant; positivity
    exact this
  set ℓ : ℤ → ℝ≥0∞ := fun k => ∫⁻ y in W,
    ENNReal.ofReal (vecEuclideanNorm ((v.layer hW ((2 : ℝ) ^ k)).grad y)) with hℓ
  have hlayer : ∀ k : ℤ, volumeOn W {x | (2 : ℝ) ^ (k + 1) ≤ v.toFun x} ≤
      ENNReal.ofReal C₀ * (ENNReal.ofReal (M / 2 ^ k) * ℓ k) ^ q := by
    intro k
    have h2 : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [zpow_add_one₀ (by norm_num)]; ring
    rw [h2]
    exact volumeOn_setOf_two_mul_le_layer hd hW hWD hSm hSW hSpos hMpos hMS v hS0
      (by positivity)
  set G : ℝ≥0∞ := ∫⁻ y in W, ENNReal.ofReal (vecEuclideanNorm (v.grad y)) with hG
  have hsum : ∫⁻ x, ENNReal.ofReal (v.toFun x) ^ q ∂(volumeOn W) ≤
      ENNReal.ofReal C₀ * ENNReal.ofReal (4 * M) ^ q * G ^ q := by
    calc ∫⁻ x, ENNReal.ofReal (v.toFun x) ^ q ∂(volumeOn W)
        ≤ ∑' k : ℤ, ENNReal.ofReal ((2 : ℝ) ^ (k + 2)) ^ q *
            volumeOn W {x | (2 : ℝ) ^ (k + 1) ≤ v.toFun x} :=
          lintegral_ofReal_rpow_le_tsum_dyadic _ hv0 hvm hq0
      _ ≤ ∑' k : ℤ, ENNReal.ofReal C₀ * ENNReal.ofReal (4 * M) ^ q * ℓ k ^ q := by
          refine ENNReal.tsum_le_tsum fun k => ?_
          have h4 : ENNReal.ofReal ((2 : ℝ) ^ (k + 2)) * ENNReal.ofReal (M / 2 ^ k) =
              ENNReal.ofReal (4 * M) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [zpow_add₀ (by norm_num)]
            field_simp
            norm_num
          calc ENNReal.ofReal ((2 : ℝ) ^ (k + 2)) ^ q *
                volumeOn W {x | (2 : ℝ) ^ (k + 1) ≤ v.toFun x}
              ≤ ENNReal.ofReal ((2 : ℝ) ^ (k + 2)) ^ q *
                (ENNReal.ofReal C₀ * (ENNReal.ofReal (M / 2 ^ k) * ℓ k) ^ q) := by
                gcongr; exact hlayer k
            _ = ENNReal.ofReal C₀ * (ENNReal.ofReal ((2 : ℝ) ^ (k + 2)) *
                (ENNReal.ofReal (M / 2 ^ k) * ℓ k)) ^ q := by
                rw [ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal ((2 : ℝ) ^ (k + 2)))
                  (ENNReal.ofReal (M / 2 ^ k) * ℓ k) hq0.le]
                ring
            _ = _ := by
                rw [← mul_assoc (ENNReal.ofReal ((2 : ℝ) ^ (k + 2))), h4,
                  ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal (4 * M)) (ℓ k) hq0.le]
                ring
      _ = ENNReal.ofReal C₀ * ENNReal.ofReal (4 * M) ^ q * ∑' k : ℤ, ℓ k ^ q :=
          ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal C₀ * ENNReal.ofReal (4 * M) ^ q * (∑' k : ℤ, ℓ k) ^ q := by
          gcongr; exact tsum_rpow_le_rpow_tsum _ hq1
      _ ≤ ENNReal.ofReal C₀ * ENNReal.ofReal (4 * M) ^ q * G ^ q := by
          gcongr; exact tsum_lintegral_layer_grad_le hW v
  have hGeq : euclideanFieldELpNormOn W 1 v.grad = G := by
    unfold euclideanFieldELpNormOn eLpNormOn
    rw [eLpNorm_one_eq_lintegral_enorm v.aemeasurable_vecEuclideanNorm_grad.aestronglyMeasurable]
    refine lintegral_congr fun y => ?_
    rw [Real.enorm_eq_ofReal (vecEuclideanNorm_nonneg _)]
  have hq0' : q ≠ 0 := hq0.ne'
  calc eLpNormOn W (ENNReal.ofReal q) v.toFun
      = (∫⁻ x, ENNReal.ofReal (v.toFun x) ^ q ∂(volumeOn W)) ^ (1 / q) := by
        unfold eLpNormOn
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq0).ne' ENNReal.ofReal_ne_top
          v.memLp.aestronglyMeasurable,
          ENNReal.toReal_ofReal hq0.le]
        congr 1
        refine lintegral_congr fun x => ?_
        rw [Real.enorm_eq_ofReal (hv0 x)]
    _ ≤ (ENNReal.ofReal C₀ * ENNReal.ofReal (4 * M) ^ q * G ^ q) ^ (1 / q) :=
        ENNReal.rpow_le_rpow hsum (by positivity)
    _ = ENNReal.ofReal (halfZeroConstant d) * euclideanFieldELpNormOn W 1 v.grad := by
        rw [hGeq, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul, mul_one_div_cancel hq0', ENNReal.rpow_one, ENNReal.rpow_one,
          ENNReal.ofReal_rpow_of_nonneg hC₀ (by positivity)]
        have hK : halfZeroConstant d = C₀ ^ (1 / q) * (4 * M) := by
          simp only [halfZeroConstant, ← hMdef, ← hC₀def, ← hq]
          rw [one_div]; ring
        rw [hK, ENNReal.ofReal_mul (p := C₀ ^ (1 / q)) (by positivity)]

end PDE
