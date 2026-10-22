module

public import PDEFoundation.Sobolev.Inequalities.ConvexSobolevPoincareNormalizedHalfZero
public import PDEFoundation.Sobolev.Inequalities.ConvexSobolevPoincareNormalizedPower
public import PDEFoundation.Sobolev.Inequalities.SobolevPoincare
public import PDEFoundation.Measure.EuclideanFieldMeasurability
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Step 2 for bounded functions

For `1 < p < d` and a bounded nonnegative `v ∈ W^{1,p}(W)` on a normalized convex domain whose
zero set has at least half the volume, the composition `v^γ` with `γ = p (d - 1) / (d - p)` lies in
`W^{1,1}(W)`, has the same zero set, and satisfies `|∇ v^γ| = γ v^(γ-1) |∇ v|`.  Step 1 and
Hölder's inequality give `∫ v^{p*} ≤ (K_d γ ‖∇ v‖_{L^p})^{p*}`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE

/-- The constant `γ_p = p (d - 1) / (d - p)` of the Sobolev--Poincaré inequality. -/
noncomputable def sobolevGamma (d : ℕ) (p : ℝ) : ℝ := p * ((d : ℝ) - 1) / ((d : ℝ) - p)

section Exponents

variable {d : ℕ} {p : ℝ}

theorem sobolevGamma_gt_one (hd : 2 ≤ d) (hp : 1 < p) (hpd : p < d) : 1 < sobolevGamma d p := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  unfold sobolevGamma
  rw [lt_div_iff₀ (by linarith)]
  nlinarith

theorem sobolevGamma_mul_conj (hd : 2 ≤ d) (hp : 1 < p) (hpd : p < d) :
    sobolevGamma d p * sobolevOneConjugate d = sobolevConjugate d p := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (d : ℝ) - p ≠ 0 := by linarith
  have h2 : (d : ℝ) - 1 ≠ 0 := by linarith
  unfold sobolevGamma sobolevOneConjugate sobolevConjugate
  field_simp

theorem sobolevGamma_sub_one_mul (hd : 2 ≤ d) (hp : 1 < p) (hpd : p < d) :
    (sobolevGamma d p - 1) * Real.conjExponent p = sobolevConjugate d p := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (d : ℝ) - p ≠ 0 := by linarith
  have h3 : p - 1 ≠ 0 := by linarith
  unfold sobolevGamma sobolevConjugate Real.conjExponent
  field_simp
  ring

theorem inv_sobolevOneConjugate_eq (hd : 2 ≤ d) (hp : 1 < p) (hpd : p < d) :
    (sobolevOneConjugate d)⁻¹ = (sobolevConjugate d p)⁻¹ + (Real.conjExponent p)⁻¹ := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (d : ℝ) - p ≠ 0 := by linarith
  have h2 : (d : ℝ) - 1 ≠ 0 := by linarith
  have h3 : p - 1 ≠ 0 := by linarith
  unfold sobolevOneConjugate sobolevConjugate Real.conjExponent
  field_simp
  ring

theorem sobolevOneConjugate_eq_sobolevConjugate_one :
    sobolevOneConjugate d = sobolevConjugate d 1 := by
  unfold sobolevOneConjugate sobolevConjugate
  ring

end Exponents

/-- **Step 2 for bounded functions.** The integral form of the half-zero Sobolev inequality
for `1 < p < d`. -/
theorem lintegral_rpow_le_of_bounded {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp : 1 < p) (hpd : p < d)
    {W : Set (Vec d)} (hW : IsOpenBoundedConvexDomain W)
    (h1 : euclideanBall (0 : Vec d) 1 ⊆ W)
    (hR : W ⊆ euclideanBall (0 : Vec d) (convexNormalizationRadius d))
    (v : W1pFunction W (ENNReal.ofReal p)) (hv0 : ∀ x, 0 ≤ v.toFun x)
    {n : ℝ} (hn : 0 < n) (hvn : ∀ x, v.toFun x ≤ n)
    (hhalf : volume W ≤ 2 * volumeOn W {x | v.toFun x = 0}) :
    ∫⁻ x, ENNReal.ofReal (v.toFun x) ^ sobolevConjugate d p ∂(volumeOn W) ≤
      (ENNReal.ofReal (halfZeroConstant d * sobolevGamma d p) *
        euclideanFieldELpNormOn W (ENNReal.ofReal p) v.grad) ^ sobolevConjugate d p := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hfin := hW.isFiniteMeasure_volumeOn
  have hP1 : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  have hPtop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  set γ := sobolevGamma d p with hγdef
  have hγ1 : 1 < γ := sobolevGamma_gt_one hd hp hpd
  have hγ0 : 0 ≤ γ := by linarith
  set qs := sobolevConjugate d p with hqsdef
  set d' := sobolevOneConjugate d with hd'def
  set p' := Real.conjExponent p with hp'def
  have hqs0 : 0 < qs := sobolevConjugate_pos (by linarith) hpd
  have hd'0 : 0 < d' := by linarith [sobolevOneConjugate_ge_one hd]
  have hHC : p'.HolderConjugate p := (Real.HolderConjugate.conjExponent hp).symm
  have hp'0 : 0 < p' := hHC.pos
  have hE1 : γ * d' = qs := sobolevGamma_mul_conj hd hp hpd
  have hE2 : (γ - 1) * p' = qs := sobolevGamma_sub_one_mul hd hp hpd
  have hE3 : d'⁻¹ = qs⁻¹ + p'⁻¹ := inv_sobolevOneConjugate_eq hd hp hpd
  have hG := contDiff_powerCutoff (n := n) hγ1.le
  have hM : 0 ≤ γ * n ^ (γ - 1) := by positivity
  have hder := abs_deriv_powerCutoff_le hγ1.le hn.le
  let w : W1pFunction W 1 := (v.compContDiffOfDerivBounded hW hP1 hPtop hG hM hder).toOne hP1
  have hwx : ∀ x, w.toFun x = (v.toFun x) ^ γ := fun x =>
    powerCutoff_of_mem hγ1.le (hv0 x) (hvn x)
  have hw0 : ∀ x, 0 ≤ w.toFun x := fun x => by rw [hwx]; exact Real.rpow_nonneg (hv0 x) _
  have hsub : {x | v.toFun x = 0} ⊆ {x | w.toFun x = 0} := by
    intro x hx
    have hx' : v.toFun x = 0 := hx
    show w.toFun x = 0
    rw [hwx, hx', Real.zero_rpow (by linarith)]
  have hwhalf : volume W ≤ 2 * volumeOn W {x | w.toFun x = 0} :=
    hhalf.trans (mul_le_mul' le_rfl (measure_mono hsub))
  have hstep1 := eLpNormOn_halfZero_le hd hW h1 hR w hw0 hwhalf
  set I := ∫⁻ x, ENNReal.ofReal (v.toFun x) ^ qs ∂(volumeOn W) with hI
  have hvm : AEMeasurable v.toFun (volumeOn W) := v.memLp.aestronglyMeasurable.aemeasurable
  have hL : eLpNormOn W (ENNReal.ofReal (sobolevOneConjugate d)) w.toFun = I ^ (1 / d') := by
    unfold eLpNormOn
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hd'0).ne'
      ENNReal.ofReal_ne_top w.memLp.aestronglyMeasurable, ENNReal.toReal_ofReal hd'0.le]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [hwx, Real.enorm_eq_ofReal (Real.rpow_nonneg (hv0 x) _),
      ← ENNReal.ofReal_rpow_of_nonneg (hv0 x) hγ0, ← ENNReal.rpow_mul, hE1]
  set g : Vec d → ℝ≥0∞ := fun y => ENNReal.ofReal (vecEuclideanNorm (v.grad y)) with hgdef
  have hgm : AEMeasurable g (volumeOn W) :=
    ENNReal.measurable_ofReal.comp_aemeasurable v.aemeasurable_vecEuclideanNorm_grad
  set f : Vec d → ℝ≥0∞ := fun y => ENNReal.ofReal (v.toFun y) ^ (γ - 1) with hfdef
  have hfm : AEMeasurable f (volumeOn W) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable hvm).pow_const _
  have hgrad : ∀ y, ENNReal.ofReal (vecEuclideanNorm (w.grad y)) =
      ENNReal.ofReal γ * (f y * g y) := by
    intro y
    have hw : w.grad y = (γ * (v.toFun y) ^ (γ - 1)) • v.grad y := by
      funext i
      change deriv (powerCutoff γ n) (v.toFun y) * v.grad y i = _
      rw [deriv_powerCutoff_of_mem hγ1.le (hv0 y) (hvn y)]
      rfl
    have hpos : 0 ≤ γ * (v.toFun y) ^ (γ - 1) :=
      mul_nonneg hγ0 (Real.rpow_nonneg (hv0 y) _)
    rw [hw, vecEuclideanNorm_smul, abs_of_nonneg hpos, ENNReal.ofReal_mul hpos, ENNReal.ofReal_mul hγ0,
      ← ENNReal.ofReal_rpow_of_nonneg (hv0 y) (by linarith), mul_assoc]
  have hRHS : euclideanFieldELpNormOn W 1 w.grad =
      ENNReal.ofReal γ * ∫⁻ y, (f * g) y ∂(volumeOn W) := by
    unfold euclideanFieldELpNormOn eLpNormOn
    rw [eLpNorm_one_eq_lintegral_enorm
      (aestronglyMeasurable_vecEuclideanNorm_of_coord fun i =>
        (w.grad_memLp i).aestronglyMeasurable)]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun y => ?_
    rw [Real.enorm_eq_ofReal (vecEuclideanNorm_nonneg _), hgrad]
    rfl
  have hfp : ∫⁻ y, f y ^ p' ∂(volumeOn W) = I := by
    refine lintegral_congr fun y => ?_
    rw [hfdef]
    simp only
    rw [← ENNReal.rpow_mul, hE2]
  have hGp : (∫⁻ y, g y ^ p ∂(volumeOn W)) ^ (1 / p) =
      euclideanFieldELpNormOn W (ENNReal.ofReal p) v.grad := by
    unfold euclideanFieldELpNormOn eLpNormOn
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 (by linarith)).ne'
      hPtop (aestronglyMeasurable_vecEuclideanNorm_of_coord fun i =>
        (v.grad_memLp i).aestronglyMeasurable), ENNReal.toReal_ofReal (by linarith)]
    congr 1
    refine lintegral_congr fun y => ?_
    rw [Real.enorm_eq_ofReal (vecEuclideanNorm_nonneg _)]
  set Gp := euclideanFieldELpNormOn W (ENNReal.ofReal p) v.grad with hGpdef
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq (volumeOn W) hHC hfm hgm
  rw [hfp, hGp] at hholder
  -- the main inequality
  have hA : I ^ (1 / d') ≤ ENNReal.ofReal (halfZeroConstant d) *
      (ENNReal.ofReal γ * (I ^ (1 / p') * Gp)) := by
    rw [← hL]
    refine hstep1.trans ?_
    rw [hRHS]
    gcongr
  -- finiteness of `I`
  have hIfin : I ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _ : Vec d, ENNReal.ofReal n ^ qs ∂(volumeOn W)) ?_ ?_
    · rw [lintegral_const]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hqs0.le ENNReal.ofReal_ne_top)
        (measure_ne_top _ _)
    · refine lintegral_mono fun x => ?_
      gcongr
      exact hvn x
  rcases eq_or_ne I 0 with hI0 | hI0
  · rw [hI0]; exact zero_le
  have hcancel : I ^ (1 / p') ≠ 0 ∧ I ^ (1 / p') ≠ ⊤ := by
    constructor
    · exact (ENNReal.rpow_pos (pos_iff_ne_zero.2 hI0) hIfin).ne'
    · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hIfin
  have hsplit : I ^ (1 / d') = I ^ (1 / qs) * I ^ (1 / p') := by
    rw [← ENNReal.rpow_add _ _ hI0 hIfin]
    congr 1
    rw [one_div, one_div, one_div, hE3]
  have hB : I ^ (1 / qs) ≤ ENNReal.ofReal (halfZeroConstant d * γ) * Gp := by
    have h2 : I ^ (1 / qs) * I ^ (1 / p') ≤
        (ENNReal.ofReal (halfZeroConstant d * γ) * Gp) * I ^ (1 / p') := by
      rw [← hsplit]
      refine hA.trans (le_of_eq ?_)
      have hK : 0 ≤ halfZeroConstant d := by
        unfold halfZeroConstant halfZeroRieszConstant halfZeroWeakConstant
        have : 0 < Real.sqrt d := Real.sqrt_pos.2 (by linarith)
        have hR : 0 < convexNormalizationRadius d := by
          unfold convexNormalizationRadius; positivity
        have hω : 0 ≤ (volume (euclideanBall (0 : Vec d) 1)).toReal := ENNReal.toReal_nonneg
        positivity
      rw [ENNReal.ofReal_mul hK]
      ring
    exact (ENNReal.mul_le_mul_iff_left hcancel.1 hcancel.2).1 (by simpa [mul_comm] using h2)
  calc I = (I ^ (1 / qs)) ^ qs := by
        rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hqs0.ne', ENNReal.rpow_one]
    _ ≤ (ENNReal.ofReal (halfZeroConstant d * γ) * Gp) ^ qs :=
        ENNReal.rpow_le_rpow hB hqs0.le

end PDE
