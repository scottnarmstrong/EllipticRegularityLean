module

public import PDEFoundation.Measure.LpTendsto
public import PDEFoundation.Sobolev.Inequalities.SobolevWholeSpaceSmooth
public import PDEFoundation.Sobolev.W1p.ZeroBoundary
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Sobolev inequality for functions with supported smooth approximation

The smooth compact-support inequality of `SobolevWholeSpaceSmooth` is passed to
the limit along an explicit supported smooth approximation of a
representative-level `W^{1,p}(U)` function.  The argument uses convergence in
measure, an almost-everywhere convergent subsequence, and Fatou lower
semicontinuity.  The public gradient magnitude is the exact Euclidean norm.
-/

@[expose] public section

open scoped ENNReal NNReal Topology

namespace PDE

open Filter MeasureTheory

/-- The dimension-only constant of the public Sobolev proposition.  The factor
`d` converts the coordinate sum forced by the supremum-norm Fréchet derivative
into the Euclidean gradient magnitude. -/
noncomputable def sobolevWholeSpaceConstant (d : ℕ) : ℝ :=
  1 + (d : ℝ) * (sobolevOneConstant d : ℝ)

theorem sobolevWholeSpaceConstant_pos (d : ℕ) :
    0 < sobolevWholeSpaceConstant d := by
  unfold sobolevWholeSpaceConstant
  positivity

/-- The factor `p (d - 1) / (d - p)` is nonnegative for `p < d`, `d ≥ 1`. -/
theorem sobolevPowerFactor_nonneg {d : ℕ} (hd : 1 ≤ d) {p : ℝ} (hp : 0 ≤ p)
    (hpd : p < d) : 0 ≤ p * ((d : ℝ) - 1) / ((d : ℝ) - p) := by
  have h1 : (0 : ℝ) < (d : ℝ) - p := sub_pos.mpr hpd
  have h2 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  positivity

private theorem eLpNorm_coordinate_le_eLpNorm_vecEuclideanNorm
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞} (F : Vec d → Vec d) (i : Fin d)
    (hF : AEStronglyMeasurable (fun x => F x i) (volumeOn U)) :
    eLpNorm (fun x => F x i) p (volumeOn U) ≤
      eLpNorm (fun x => vecEuclideanNorm (F x)) p (volumeOn U) := by
  apply eLpNorm_mono_ae hF
  filter_upwards with x
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (vecEuclideanNorm_nonneg _)] using
    abs_apply_le_vecEuclideanNorm (F x) i

private theorem support_fderiv_apply_basisVec_subset
    {d : ℕ} {U : Set (Vec d)} {f : Vec d → ℝ}
    (i : Fin d) (hsub : tsupport f ⊆ U) :
    Function.support (fun x => (fderiv ℝ f x) (basisVec i)) ⊆ U := by
  intro x hx
  exact hsub <|
    (support_fderiv_subset (𝕜 := ℝ) (f := f)) <| by
      change fderiv ℝ f x ≠ 0
      intro hzero
      apply hx
      simp [hzero]

/-- The Sobolev inequality for a representative-level `W^{1,p}(U)` function
admitting a supported smooth approximation, `1 ≤ p < d`. -/
theorem eLpNorm_sobolevConjugate_le_of_supportedSmoothApproximation
    {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp : 1 ≤ p) (hpd : p < d)
    {U : Set (Vec d)} (u : W1pFunction U (ENNReal.ofReal p))
    (happrox : u.SupportedSmoothApproximation) :
    eLpNorm u.toFun (ENNReal.ofReal (sobolevConjugate d p)) (volumeOn U) ≤
      ENNReal.ofReal (sobolevWholeSpaceConstant d *
          (p * ((d : ℝ) - 1) / ((d : ℝ) - p))) *
        eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
          (volumeOn U) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hone : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  set μ : Measure (Vec d) := volumeOn U with hμ
  let P : ℝ≥0∞ := ENNReal.ofReal p
  let Q : ℝ≥0∞ := ENNReal.ofReal (sobolevConjugate d p)
  set γ : ℝ := p * ((d : ℝ) - 1) / ((d : ℝ) - p) with hγ
  have hγ0 : 0 ≤ γ := sobolevPowerFactor_nonneg (by omega) hp0.le hpd
  let Cg : ℝ≥0∞ := ENNReal.ofReal ((sobolevOneConstant d : ℝ) * γ)
  let ψ : ℕ → Vec d → ℝ := happrox.approx
  have hψC1 : ∀ n, ContDiff ℝ 1 (ψ n) := fun n =>
    (happrox.approx_smooth n).of_le (by simp)
  have hgradAe : ∀ n i, AEStronglyMeasurable
      (fun x => (fderiv ℝ (ψ n) x) (basisVec i)) μ := fun n i =>
    (((hψC1 n).continuous_fderiv (by simp)).clm_apply
      continuous_const).aestronglyMeasurable
  have hgradAe' : ∀ n i, AEStronglyMeasurable
      (fun x => (fderiv ℝ (ψ n) x) (basisVec i)) volume := fun n i =>
    (((hψC1 n).continuous_fderiv (by simp)).clm_apply
      continuous_const).aestronglyMeasurable
  let a : ℕ → ℝ≥0∞ := fun n => eLpNorm (ψ n) Q μ
  let b : ℕ → ℝ≥0∞ := fun n =>
    Cg * ∑ i : Fin d, eLpNorm (fun x => (fderiv ℝ (ψ n) x) (basisVec i)) P μ
  let binf : ℝ≥0∞ := Cg * ∑ i : Fin d, eLpNorm (fun x => u.grad x i) P μ
  have hCg_ne_top : Cg ≠ ∞ := ENNReal.ofReal_ne_top
  have hab : ∀ n, a n ≤ b n := by
    intro n
    have hvalue_support : Function.support (ψ n) ⊆ U :=
      (subset_tsupport _).trans (happrox.approx_tsupport_subset n)
    have hcoordinate_support : ∀ i : Fin d,
        Function.support (fun x => (fderiv ℝ (ψ n) x) (basisVec i)) ⊆ U :=
      fun i => support_fderiv_apply_basisVec_subset i
        (happrox.approx_tsupport_subset n)
    change eLpNorm (ψ n) Q μ ≤
      Cg * ∑ i : Fin d,
        eLpNorm (fun x => (fderiv ℝ (ψ n) x) (basisVec i)) P μ
    rw [hμ, volumeOn, eLpNorm_restrict_eq_of_support_subset
      (happrox.approx_smooth n).continuous.aestronglyMeasurable hvalue_support]
    refine (eLpNorm_sobolevConjugate_le_sum_eLpNorm_fderiv_apply_basisVec
      hd hp hpd (hψC1 n) (happrox.approx_hasCompactSupport n)).trans ?_
    refine mul_le_mul_right ?_ _
    refine Finset.sum_le_sum fun i _ => ?_
    rw [eLpNorm_restrict_eq_of_support_subset (hgradAe' n i) (hcoordinate_support i)]
  have hu_ae : AEStronglyMeasurable u.toFun μ := u.memLp.aestronglyMeasurable
  have hb_tend : Tendsto b atTop (𝓝 binf) := by
    refine ENNReal.Tendsto.const_mul (tendsto_finsetSum _ fun i _ => ?_)
      (Or.inr hCg_ne_top)
    refine tendsto_eLpNorm_of_tendsto_sub hone (hgradAe · i)
      (u.gradMemLp i).aestronglyMeasurable (u.gradMemLp i).eLpNorm_ne_top ?_
    exact happrox.tendsto_grad i
  have htim : TendstoInMeasure μ ψ atTop u.toFun :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := P) (by simp [P, hp0])
      happrox.tendsto_value
  obtain ⟨σ, hσ_mono, hσ_ae⟩ := htim.exists_seq_tendsto_ae
  have hfatou : eLpNorm u.toFun Q μ ≤ Filter.liminf (fun n => a (σ n)) atTop :=
    Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun n => (happrox.approx_smooth (σ n)).continuous.aestronglyMeasurable)
      u.toFun hu_ae hσ_ae
  have hbound_liminf : Filter.liminf (fun n => a (σ n)) atTop ≤ binf := by
    have hbσ : Tendsto (fun n => b (σ n)) atTop (𝓝 binf) :=
      hb_tend.comp hσ_mono.tendsto_atTop
    calc
      Filter.liminf (fun n => a (σ n)) atTop ≤
          Filter.liminf (fun n => b (σ n)) atTop :=
        Filter.liminf_le_liminf (Eventually.of_forall fun n => hab (σ n))
      _ = binf := hbσ.liminf_eq
  have hcoordinate_sum :
      (∑ i : Fin d, eLpNorm (fun x => u.grad x i) P μ) ≤
        (d : ℝ≥0∞) * eLpNorm (fun x => vecEuclideanNorm (u.grad x)) P μ := by
    calc
      (∑ i : Fin d, eLpNorm (fun x => u.grad x i) P μ) ≤
          ∑ _i : Fin d, eLpNorm (fun x => vecEuclideanNorm (u.grad x)) P μ :=
        Finset.sum_le_sum fun i _ =>
          eLpNorm_coordinate_le_eLpNorm_vecEuclideanNorm u.grad i
            (u.gradMemLp i).aestronglyMeasurable
      _ = (d : ℝ≥0∞) * eLpNorm (fun x => vecEuclideanNorm (u.grad x)) P μ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hconst : Cg * (d : ℝ≥0∞) ≤
      ENNReal.ofReal (sobolevWholeSpaceConstant d * γ) := by
    have : Cg * (d : ℝ≥0∞) =
        ENNReal.ofReal ((sobolevOneConstant d : ℝ) * γ * d) := by
      rw [show (d : ℝ≥0∞) = ENNReal.ofReal (d : ℝ) by simp,
        ← ENNReal.ofReal_mul (mul_nonneg (NNReal.coe_nonneg _) hγ0)]
    rw [this]
    apply ENNReal.ofReal_le_ofReal
    unfold sobolevWholeSpaceConstant
    have : (0 : ℝ) ≤ γ := hγ0
    nlinarith [NNReal.coe_nonneg (sobolevOneConstant d), (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  calc
    eLpNorm u.toFun Q μ ≤ binf := hfatou.trans hbound_liminf
    _ ≤ Cg * ((d : ℝ≥0∞) * eLpNorm (fun x => vecEuclideanNorm (u.grad x)) P μ) :=
      mul_le_mul_right hcoordinate_sum _
    _ = (Cg * (d : ℝ≥0∞)) * eLpNorm (fun x => vecEuclideanNorm (u.grad x)) P μ := by
      ring
    _ ≤ _ := mul_le_mul_left hconst _

end PDE
