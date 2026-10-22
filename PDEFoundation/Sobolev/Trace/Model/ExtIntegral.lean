module

public import PDEFoundation.Sobolev.Trace.Model.ExtGrad
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Integrals of the majorants

The Jensen majorant integrates to `∫ |g|^p` in `x'` for every `t > 0`, and the oscillation
majorant integrates in `t` to a multiple of the Gagliardo integrand (Fubini and
`∫_r^∞ t^{-(n+p)} dt = r^{-(n+p-1)}/(n+p-1)`).
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {n : ℕ}

theorem measurable_dil (n : ℕ) : Measurable fun q : Vec n × ℝ => dil n (extKernel n) q.1 q.2 :=
  (measurable_snd.inv.pow_const n).mul
    ((continuous_extKernel n).measurable.comp (measurable_snd.inv.smul measurable_fst))

theorem measurable_extPsi (p : ℝ) {g : Vec n → ℝ} (hgm : Measurable g) :
    Measurable fun q : Vec n × ℝ => extPsi n p g q.1 q.2 := by
  have hF : Measurable fun r : (Vec n × ℝ) × Vec n =>
      ENNReal.ofReal (dil n (extKernel n) (r.1.1 - r.2) r.1.2) *
        ENNReal.ofReal (|g r.2| ^ p) := by
    refine (ENNReal.measurable_ofReal.comp ?_).mul (ENNReal.measurable_ofReal.comp ?_)
    · exact (measurable_dil n).comp ((measurable_fst.fst.sub measurable_snd).prodMk
        measurable_fst.snd)
    · exact (continuous_abs.measurable.comp (hgm.comp measurable_snd)).pow_const p
  exact hF.lintegral_prod_right' (ν := volume)

theorem measurable_extPhi (p : ℝ) {g : Vec n → ℝ} (hgm : Measurable g) :
    Measurable fun q : Vec n × ℝ => extPhi n p g q.1 q.2 := by
  have hS : MeasurableSet {r : (Vec n × ℝ) × Vec n | vecEuclideanNorm (r.1.1 - r.2) ≤ r.1.2} :=
    measurableSet_le ((continuous_vecEuclideanNorm n).measurable.comp
      (measurable_fst.fst.sub measurable_snd)) measurable_fst.snd
  have hF : Measurable fun r : (Vec n × ℝ) × Vec n =>
      {r : (Vec n × ℝ) × Vec n | vecEuclideanNorm (r.1.1 - r.2) ≤ r.1.2}.indicator
        (fun r => ENNReal.ofReal (|g r.2 - g r.1.1| ^ p)) r := by
    refine Measurable.indicator ?_ hS
    refine ENNReal.measurable_ofReal.comp (Measurable.pow_const ?_ p)
    exact continuous_abs.measurable.comp ((hgm.comp measurable_snd).sub (hgm.comp measurable_fst.fst))
  have h2 := hF.lintegral_prod_right' (ν := volume)
  have h3 : Measurable fun q : Vec n × ℝ => ENNReal.ofReal (q.2 ^ (-((n : ℝ) + p))) :=
    ENNReal.measurable_ofReal.comp (measurable_snd.pow_const _)
  refine h3.mul ?_
  convert h2 using 2
  refine lintegral_congr fun y => ?_
  rename_i q
  by_cases hy : vecEuclideanNorm (q.1 - y) ≤ q.2 <;> simp [Set.indicator, eBallSet, hy]

theorem lintegral_ofReal_dil {t : ℝ} (ht : 0 < t) :
    ∫⁻ z, ENNReal.ofReal (dil n (extKernel n) z t) = 1 := by
  rw [← lintegral_sub_left_eq_self (fun z => ENNReal.ofReal (dil n (extKernel n) z t)) (0 : Vec n)]
  exact lintegral_ofReal_dil_sub ht 0

theorem lintegral_extPsi (p : ℝ) {g : Vec n → ℝ} (hgm : Measurable g) {t : ℝ} (ht : 0 < t) :
    ∫⁻ x, extPsi n p g x t = ∫⁻ y, ENNReal.ofReal (|g y| ^ p) := by
  unfold extPsi
  have hmeas : Measurable (Function.uncurry fun (x y : Vec n) =>
      ENNReal.ofReal (dil n (extKernel n) (x - y) t) * ENNReal.ofReal (|g y| ^ p)) := by
    refine (ENNReal.measurable_ofReal.comp ?_).mul (ENNReal.measurable_ofReal.comp ?_)
    · exact (continuous_dil n (isProfile_extKernel n) t).measurable.comp
        (measurable_fst.sub measurable_snd)
    · exact (continuous_abs.measurable.comp (hgm.comp measurable_snd)).pow_const p
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  refine lintegral_congr fun y => ?_
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  have : ∫⁻ x, ENNReal.ofReal (dil n (extKernel n) (x - y) t) = 1 := by
    rw [lintegral_sub_right_eq_self (fun z => ENNReal.ofReal (dil n (extKernel n) z t)) y]
    exact lintegral_ofReal_dil ht
  rw [this, one_mul]

theorem lintegral_Ici_rpow {s r : ℝ} (hs : 1 < s) (hr : 0 < r) :
    ∫⁻ t in Ici r, ENNReal.ofReal (t ^ (-s)) = ENNReal.ofReal (r ^ (-(s - 1)) / (s - 1)) := by
  rw [← setLIntegral_congr (Ioi_ae_eq_Ici (a := r)),
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt (by linarith) hr)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht =>
        Real.rpow_nonneg (hr.trans ht).le _)),
    integral_Ioi_rpow_of_lt (by linarith) hr]
  congr 1
  have : -s + 1 = -(s - 1) := by ring
  rw [this]
  have h2 : (-(s - 1)) ≠ 0 := by linarith
  field_simp

theorem lintegral_Ioi_ball_le {s r c : ℝ} (hs : 1 < s) (hr : 0 < r) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-s)) *
        {t : ℝ | r ≤ t}.indicator (fun _ => ENNReal.ofReal c) t ≤
      ENNReal.ofReal c * ENNReal.ofReal (r ^ (-(s - 1)) / (s - 1)) := by
  have h1 : ∀ t : ℝ, ENNReal.ofReal (t ^ (-s)) *
      {t : ℝ | r ≤ t}.indicator (fun _ => ENNReal.ofReal c) t =
      (Ici r).indicator (fun t => ENNReal.ofReal c * ENNReal.ofReal (t ^ (-s))) t := by
    intro t
    by_cases ht : r ≤ t
    · simp [ht, mul_comm]
    · simp [ht]
  simp_rw [h1]
  refine (setLIntegral_le_lintegral _ _).trans ?_
  rw [lintegral_indicator measurableSet_Ici, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_Ici_rpow hs hr]

theorem extPhi_eq (p : ℝ) (g : Vec n → ℝ) (x : Vec n) (t : ℝ) :
    extPhi n p g x t = ∫⁻ y, ENNReal.ofReal (t ^ (-((n : ℝ) + p))) *
      (eBallSet n x t).indicator (fun y => ENNReal.ofReal (|g y - g x| ^ p)) y := by
  unfold extPhi
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

theorem lintegral_Ioi_extPhi_inner {p : ℝ} (hp : 1 < p) (g : Vec n → ℝ) (x y : Vec n) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-((n : ℝ) + p))) *
        (eBallSet n x t).indicator (fun y => ENNReal.ofReal (|g y - g x| ^ p)) y ≤
      ENNReal.ofReal (1 / ((n : ℝ) + p - 1)) *
        ENNReal.ofReal (|g x - g y| ^ p / vecEuclideanNorm (x - y) ^ ((n : ℝ) + p - 1)) := by
  have hp0 : 0 < p := by linarith
  have hs : 1 < (n : ℝ) + p := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hq : 0 < (n : ℝ) + p - 1 := by linarith
  have hr0 : 0 ≤ vecEuclideanNorm (x - y) := vecEuclideanNorm_nonneg _
  have h1 : ∀ t : ℝ, ENNReal.ofReal (t ^ (-((n : ℝ) + p))) *
      (eBallSet n x t).indicator (fun y => ENNReal.ofReal (|g y - g x| ^ p)) y =
      ENNReal.ofReal (t ^ (-((n : ℝ) + p))) *
        {t : ℝ | vecEuclideanNorm (x - y) ≤ t}.indicator
          (fun _ => ENNReal.ofReal (|g y - g x| ^ p)) t := by
    intro t
    by_cases ht : vecEuclideanNorm (x - y) ≤ t
    · simp only [Set.indicator, eBallSet, Set.mem_ofPred_eq, ht, ite_true]
    · simp only [Set.indicator, eBallSet, Set.mem_ofPred_eq, ht, ite_false]
  simp_rw [h1]
  rcases hr0.eq_or_lt with h0 | hpos
  · have hxy : x = y := by
      have := vecEuclideanNorm_eq_zero_iff.1 h0.symm
      exact sub_eq_zero.1 this
    subst hxy
    simp [Real.zero_rpow hp0.ne']
  · refine (lintegral_Ioi_ball_le hs hpos).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), abs_sub_comm]
    congr 1
    have : (n : ℝ) + p - 1 = ((n : ℝ) + p) - 1 := rfl
    rw [Real.rpow_neg hpos.le]
    field_simp

theorem lintegral_Ioi_extPhi_le {p : ℝ} (hp : 1 < p) {g : Vec n → ℝ} (hgm : Measurable g)
    (x : Vec n) :
    ∫⁻ t in Ioi (0 : ℝ), extPhi n p g x t ≤ ENNReal.ofReal (1 / ((n : ℝ) + p - 1)) *
      ∫⁻ y, ENNReal.ofReal (|g x - g y| ^ p / vecEuclideanNorm (x - y) ^ ((n : ℝ) + p - 1)) := by
  simp_rw [extPhi_eq]
  have hS : MeasurableSet {q : ℝ × Vec n | vecEuclideanNorm (x - q.2) ≤ q.1} :=
    measurableSet_le ((continuous_vecEuclideanNorm n).measurable.comp
      (measurable_const.sub measurable_snd)) measurable_fst
  have hind : Measurable fun q : ℝ × Vec n =>
      (eBallSet n x q.1).indicator (fun y => ENNReal.ofReal (|g y - g x| ^ p)) q.2 := by
    have : Measurable ({q : ℝ × Vec n | vecEuclideanNorm (x - q.2) ≤ q.1}.indicator
        fun q => ENNReal.ofReal (|g q.2 - g x| ^ p)) := by
      refine Measurable.indicator ?_ hS
      exact ENNReal.measurable_ofReal.comp (Measurable.pow_const
        (continuous_abs.measurable.comp ((hgm.comp measurable_snd).sub_const _)) p)
    convert this using 1
    funext q
    by_cases h : vecEuclideanNorm (x - q.2) ≤ q.1 <;>
      simp [Set.indicator, eBallSet, h]
  have hmeas : Measurable (Function.uncurry fun (t : ℝ) (y : Vec n) =>
      ENNReal.ofReal (t ^ (-((n : ℝ) + p))) *
        (eBallSet n x t).indicator (fun y => ENNReal.ofReal (|g y - g x| ^ p)) y) :=
    (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)).mul hind
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  calc ∫⁻ y, ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-((n : ℝ) + p))) *
        (eBallSet n x t).indicator (fun y => ENNReal.ofReal (|g y - g x| ^ p)) y
      ≤ ∫⁻ y, ENNReal.ofReal (1 / ((n : ℝ) + p - 1)) *
          ENNReal.ofReal (|g x - g y| ^ p / vecEuclideanNorm (x - y) ^ ((n : ℝ) + p - 1)) :=
        lintegral_mono fun y => lintegral_Ioi_extPhi_inner hp g x y
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end PDE.TraceLane
