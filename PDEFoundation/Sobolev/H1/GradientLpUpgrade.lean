module

public import PDEFoundation.Sobolev.H1.HigherIntegrabilityClamps
public import PDEFoundation.Sobolev.Inequalities.ConvexPoincare
public import PDEFoundation.Sobolev.W1p.EuclideanGradient
public import PDEFoundation.Sobolev.W1p.Mean
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Upgrading `H¹` representatives with higher-integrable gradients

On a bounded open convex domain of positive volume, an `H¹` representative
whose chosen gradient has coordinatewise finite `L^p` norm, for real `p ≥ 2`,
has the same value and gradient representatives in `W^{1,p}`.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

namespace H1Function

variable {d : ℕ} {U : Set (Vec d)}

private theorem abs_higherIntegrabilityClamp_le
    (hU : IsOpenBoundedConvexDomain U)
    (p : ℝ) (hp : 2 ≤ p) (u : H1Function U)
    (hgrad : GradMemLpOn U (ENNReal.ofReal p) u.grad)
    (k : ℝ) (hk : 0 ≤ k) (x : Vec d) :
    |(u.higherIntegrabilityClamp hU p hp hgrad k hk).toFun x| ≤ |u.toFun x| := by
  rw [higherIntegrabilityClamp_toFun]
  change |max (-k) (min (u.toFun x) k)| ≤ |u.toFun x|
  rcases le_total (u.toFun x) (-k) with hlow | hlow
  · rw [min_eq_left (hlow.trans (neg_le_self hk)), max_eq_left hlow,
      abs_neg, abs_of_nonneg hk, abs_of_nonpos (hlow.trans (neg_nonpos.mpr hk))]
    linarith only [hlow]
  · rw [max_eq_right (le_min hlow (neg_le_self hk))]
    rcases le_total (u.toFun x) k with hhigh | hhigh
    · rw [min_eq_left hhigh]
    · rw [min_eq_right hhigh]
      rw [abs_of_nonneg hk, abs_of_nonneg (hk.trans hhigh)]
      exact hhigh

theorem abs_integralAverage_higherIntegrabilityClamp_le
    (hU : IsOpenBoundedConvexDomain U) (hUPos : 0 < volume U)
    (p : ℝ) (hp : 2 ≤ p) (u : H1Function U)
    (hgrad : GradMemLpOn U (ENNReal.ofReal p) u.grad)
    (k : ℝ) (hk : 0 ≤ k) :
    ‖integralAverage U
        (u.higherIntegrabilityClamp hU p hp hgrad k hk).toFun‖ₑ ≤
      eLpMeanNormOn U 2 u.toFun := by
  let _ : IsProbabilityMeasure (normalizedVolumeOn U) :=
    isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top
      hUPos hU.volume_lt_top
  let w := u.higherIntegrabilityClamp hU p hp hgrad k hk
  calc
    ‖integralAverage U w.toFun‖ₑ =
        ‖∫ x, w.toFun x ∂normalizedVolumeOn U‖ₑ := by
      rw [integral_normalizedVolumeOn_eq_integralAverage]
    _ ≤ ∫⁻ x, ‖w.toFun x‖ₑ ∂normalizedVolumeOn U :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ eLpNorm w.toFun 1 (normalizedVolumeOn U) :=
      lintegral_enorm_le_eLpNorm_one
    _ ≤ eLpNorm u.toFun 1 (normalizedVolumeOn U) := by
      apply eLpNorm_mono_ae
        (memLp_normalizedVolumeOn_of_memLpOn w.memLp hUPos).aestronglyMeasurable
      exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
        exact abs_higherIntegrabilityClamp_le hU p hp u hgrad k hk x
    _ ≤ eLpNorm u.toFun 2 (normalizedVolumeOn U) := by
      simpa using eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (μ := normalizedVolumeOn U) (p := (1 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
        (by norm_num)
        (memLp_normalizedVolumeOn_of_memLpOn u.memL2 hUPos).aestronglyMeasurable
    _ = eLpMeanNormOn U 2 u.toFun := rfl

theorem higherIntegrabilityClamp_grad_eLpNorm_le
    (hU : IsOpenBoundedConvexDomain U)
    (p : ℝ) (hp : 2 ≤ p) (u : H1Function U)
    (hgrad : GradMemLpOn U (ENNReal.ofReal p) u.grad)
    (k : ℝ) (hk : 0 ≤ k) :
    euclideanFieldELpNormOn U (ENNReal.ofReal p)
        (u.higherIntegrabilityClamp hU p hp hgrad k hk).grad ≤
      euclideanFieldELpNormOn U (ENNReal.ofReal p) u.grad := by
  apply eLpNorm_mono_ae
    (u.higherIntegrabilityClamp hU p hp hgrad k hk).gradMemLp.memLp_vecEuclideanNorm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [higherIntegrabilityClamp_grad]
    change |vecEuclideanNorm
        ({y | -k < u.toFun y ∧ u.toFun y < k}.indicator u.grad x)| ≤
      |vecEuclideanNorm (u.grad x)|
    by_cases hx : x ∈ {y | -k < u.toFun y ∧ u.toFun y < k}
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx,
        show vecEuclideanNorm (0 : Vec d) = 0 from vecEuclideanNorm_eq_zero_iff.2 rfl,
        abs_zero,
        abs_of_nonneg (vecEuclideanNorm_nonneg _)]
      exact vecEuclideanNorm_nonneg _

theorem tendsto_higherIntegrabilityClamp_toFun
    (hU : IsOpenBoundedConvexDomain U)
    (p : ℝ) (hp : 2 ≤ p) (u : H1Function U)
    (hgrad : GradMemLpOn U (ENNReal.ofReal p) u.grad) (x : Vec d) :
    Tendsto
      (fun n : ℕ =>
        (u.higherIntegrabilityClamp hU p hp hgrad (n + 1 : ℝ) (by positivity)).toFun x)
      atTop (𝓝 (u.toFun x)) := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_ge |u.toFun x|
  apply tendsto_atTop_of_eventually_const (i₀ := N)
  intro n hn
  rw [higherIntegrabilityClamp_toFun]
  change max (-(n + 1 : ℝ)) (min (u.toFun x) (n + 1 : ℝ)) = u.toFun x
  have habs : |u.toFun x| ≤ (n + 1 : ℝ) := by
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith only [hN, hNn]
  rw [min_eq_left (le_of_abs_le habs), max_eq_right (neg_le_of_abs_le habs)]

/-- An `H¹` representative with coordinatewise `L^p` gradient control is the
same literal representative in `W^{1,p}` for every finite real `p ≥ 2`. -/
noncomputable def toW1pOfGradMemLp
    (hd : 0 < d) (hU : IsOpenBoundedConvexDomain U)
    (hUPos : 0 < volume U) (p : ℝ) (hp : 2 ≤ p)
    (u : H1Function U)
    (hgrad : GradMemLpOn U (ENNReal.ofReal p) u.grad) :
    W1pFunction U (ENNReal.ofReal p) := by
  classical
  letI : IsFiniteMeasure (volumeOn U) :=
    hU.isBoundedDomain.isFiniteMeasure_volumeOn
  refine
    { toFun := u.toFun
      grad := u.grad
      memLp := ?_
      gradMemLp := hgrad
      hasWeakGradient := u.hasWeakGradient }
  obtain ⟨M, hM, hbound⟩ := hU.isBoundedDomain
  have hdiam : HasEuclideanDiameterLE U (Real.sqrt d * (2 * M)) := by
    intro x hx y hy
    have hnorm : ‖x - y‖ ≤ 2 * M := by
      apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      intro i
      simpa only [Pi.sub_apply, Real.norm_eq_abs, two_mul] using
        (abs_sub (x i) (y i)).trans (add_le_add (hbound x hx i) (hbound y hy i))
    exact (vecEuclideanNorm_le_sqrt_natCast_mul_norm (x - y)).trans
      (mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _))
  have hdReal : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hD : 0 ≤ Real.sqrt d * (2 * M) :=
    (mul_pos (Real.sqrt_pos.2 hdReal) (by positivity)).le
  let w : ℕ → W1pFunction U (ENNReal.ofReal p) := fun n =>
    u.higherIntegrabilityClamp hU p hp hgrad (n + 1 : ℝ) (by positivity)
  let A : ℝ≥0∞ := eLpMeanNormOn U 2 u.toFun
  let G : ℝ≥0∞ := euclideanFieldELpNormOn U (ENNReal.ofReal p) u.grad
  let C : ℝ≥0∞ :=
    ENNReal.ofReal ((2 : ℝ) ^ d * (Real.sqrt d * (2 * M))) * G +
      A * (volumeOn U Set.univ) ^ (1 / (ENNReal.ofReal p).toReal)
  have hboundLp : ∀ n, eLpNorm (w n).toFun (ENNReal.ofReal p) (volumeOn U) ≤ C := by
    intro n
    let _ : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    let v := (w n).subAverage
    have hmean := (w n).meanZeroOn_subAverage hUPos hU.volume_lt_top
    have hcenter := meanZeroPoincare_on_boundedConvexDomain_unnormalized
      (by linarith : 1 ≤ p) hU hdiam hD hUPos hU.volume_lt_top v (by
        simpa only [v] using hmean)
    have hgradle : euclideanFieldELpNormOn U (ENNReal.ofReal p) v.grad ≤ G := by
      rw [show v.grad = (w n).grad by funext x; exact (w n).subAverage_grad x]
      exact higherIntegrabilityClamp_grad_eLpNorm_le hU p hp u hgrad _ (by positivity)
    have hcenter' : eLpNormOn U (ENNReal.ofReal p) v.toFun ≤
        ENNReal.ofReal ((2 : ℝ) ^ d * (Real.sqrt d * (2 * M))) * G :=
      hcenter.trans (mul_le_mul_of_nonneg_left hgradle zero_le)
    have htri := eLpNorm_add_le (f := v.toFun)
      (g := fun _ : Vec d => integralAverage U (w n).toFun) (μ := volumeOn U)
      (ENNReal.one_le_ofReal.mpr (by linarith : 1 ≤ p))
    have havg : ‖integralAverage U (w n).toFun‖ₑ ≤ A :=
      abs_integralAverage_higherIntegrabilityClamp_le hU hUPos p hp u hgrad _
        (by positivity)
    calc
      eLpNorm (w n).toFun (ENNReal.ofReal p) (volumeOn U) =
          eLpNorm (v.toFun + fun _ => integralAverage U (w n).toFun)
            (ENNReal.ofReal p) (volumeOn U) := by
              apply eLpNorm_congr_ae
              filter_upwards with x
              rw [Pi.add_apply, show v.toFun x =
                  (w n).toFun x - integralAverage U (w n).toFun by
                exact (w n).subAverage_apply x]
              ring
      _ ≤ eLpNorm v.toFun (ENNReal.ofReal p) (volumeOn U) +
          eLpNorm (fun _ : Vec d => integralAverage U (w n).toFun)
            (ENNReal.ofReal p) (volumeOn U) := htri
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ d * (Real.sqrt d * (2 * M))) * G +
          A * (volumeOn U Set.univ) ^ (1 / (ENNReal.ofReal p).toReal) := by
            gcongr
            · exact hcenter'
            · rw [eLpNorm_const' _ (by positivity) ENNReal.ofReal_ne_top]
              exact mul_le_mul_of_nonneg_right
                havg zero_le
      _ = C := rfl
  have hmeasure : TendstoInMeasure (volumeOn U) (fun n => (w n).toFun) atTop u.toFun := by
    apply tendstoInMeasure_of_tendsto_ae
    · exact fun n => (w n).memLp.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x =>
        tendsto_higherIntegrabilityClamp_toFun hU p hp u hgrad x
  have huNorm : eLpNorm u.toFun (ENNReal.ofReal p) (volumeOn U) ≤ C :=
    eLpNorm_le_of_tendstoInMeasure (Filter.Eventually.of_forall hboundLp)
      hmeasure (fun n => (w n).memLp.aestronglyMeasurable)
  refine huNorm.trans_lt ?_
  dsimp only [C, G, A]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    hgrad.memLp_vecEuclideanNorm.eLpNorm_lt_top,
    ENNReal.mul_lt_top (by
      exact (memLp_normalizedVolumeOn_of_memLpOn u.memL2 hUPos).eLpNorm_lt_top)
      (ENNReal.rpow_lt_top_of_nonneg (by positivity)
        (measure_lt_top (volumeOn U) Set.univ).ne)⟩

@[simp] theorem toW1pOfGradMemLp_toFun
    (hd : 0 < d) (hU : IsOpenBoundedConvexDomain U)
    (hUPos : 0 < volume U) (p : ℝ) (hp : 2 ≤ p)
    (u : H1Function U) (hgrad : GradMemLpOn U (ENNReal.ofReal p) u.grad) :
    (u.toW1pOfGradMemLp hd hU hUPos p hp hgrad).toFun = u.toFun := rfl

@[simp] theorem toW1pOfGradMemLp_grad
    (hd : 0 < d) (hU : IsOpenBoundedConvexDomain U)
    (hUPos : 0 < volume U) (p : ℝ) (hp : 2 ≤ p)
    (u : H1Function U) (hgrad : GradMemLpOn U (ENNReal.ofReal p) u.grad) :
    (u.toW1pOfGradMemLp hd hU hUPos p hp hgrad).grad = u.grad := rfl

end H1Function

end PDE
