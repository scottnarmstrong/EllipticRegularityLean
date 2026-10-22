module

public import PDEFoundation.Measure.LpTendsto
public import PDEFoundation.Sobolev.H1.ZeroBoundary
public import PDEFoundation.Sobolev.Inequalities.ZeroBoundarySobolevSmooth
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Critical Sobolev inequality for `H¹₀`

The whole-space smooth inequality from `ZeroBoundarySobolevSmooth` is passed
to the literal supported smooth approximants bundled by `H10Function`.  The
argument uses convergence in measure, an almost-everywhere convergent
subsequence, and Fatou lower semicontinuity.  The public conclusion retains
the exact Euclidean magnitude of the native weak gradient.
-/

@[expose] public section

open scoped ENNReal NNReal Topology

namespace PDE

open Filter MeasureTheory

/-- A positive dimension-only constant for the critical zero-boundary Sobolev
inequality.  The factor `d` converts the coordinate derivative sum forced by
the native supremum-norm Fréchet derivative into the explicit Euclidean
gradient norm. -/
noncomputable def zeroBoundarySobolevConstantTwo (d : ℕ) : ℝ≥0 :=
  1 + d * eLpNormLESNormFDerivOfEqInnerConst
    (volume : Measure (Vec d)) (2 : ℝ≥0)

theorem zeroBoundarySobolevConstantTwo_pos (d : ℕ) :
    0 < zeroBoundarySobolevConstantTwo d := by
  unfold zeroBoundarySobolevConstantTwo
  positivity

private theorem support_fderiv_apply_basisVec_subset_of_tsupport_subset
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

private theorem eLpNorm_coordinate_le_euclideanFieldELpNormOn
    {d : ℕ} {U : Set (Vec d)} (F : Vec d → Vec d) (i : Fin d)
    (hF : AEStronglyMeasurable (fun x => F x i) (volume.restrict U)) :
    eLpNorm (fun x => F x i) 2 (volume.restrict U) ≤
      euclideanFieldELpNormOn U 2 F := by
  apply eLpNorm_mono_ae hF
  filter_upwards with x
  simpa only [euclideanFieldELpNormOn, eLpNormOn, Real.norm_eq_abs,
    abs_of_nonneg (vecEuclideanNorm_nonneg _)] using
    abs_apply_le_vecEuclideanNorm (F x) i

/-- The raw critical Sobolev inequality for a representative-level
`H¹₀(U)` function.  It is scale invariant; no domain, radius, or side length
is hidden in the constant. -/
theorem eLpNormOn_sobolevTwoStar_le_euclideanFieldELpNormOn
    {d : ℕ} (hd : 3 ≤ d) {U : Set (Vec d)}
    (u : H10Function U) :
    eLpNormOn U (sobolevTwoStar d) u.toFun ≤
      (zeroBoundarySobolevConstantTwo d : ℝ≥0∞) *
        euclideanFieldELpNormOn U 2 u.toH1Function.grad := by
  let μ : Measure (Vec d) := volume.restrict U
  let Cgns : ℝ≥0∞ :=
    eLpNormLESNormFDerivOfEqInnerConst
      (volume : Measure (Vec d)) (2 : ℝ≥0)
  let ψ : ℕ → Vec d → ℝ := u.approx
  let a : ℕ → ℝ≥0∞ :=
    fun n => eLpNorm (ψ n) (sobolevTwoStar d) μ
  let b : ℕ → ℝ≥0∞ :=
    fun n => Cgns * ∑ i : Fin d,
      eLpNorm (fun x => (fderiv ℝ (ψ n) x) (basisVec i)) 2 μ
  let binf : ℝ≥0∞ :=
    Cgns * ∑ i : Fin d, eLpNorm (fun x => u.grad x i) 2 μ
  have hCgns_ne_top : Cgns ≠ ∞ := by
    simp [Cgns]
  have hab : ∀ n, a n ≤ b n := by
    intro n
    have hvalue_support : Function.support (ψ n) ⊆ U :=
      (subset_tsupport _).trans (u.approx_support_subset n)
    have hcoordinate_support :
        ∀ i : Fin d,
          Function.support
            (fun x => (fderiv ℝ (ψ n) x) (basisVec i)) ⊆ U := by
      intro i
      exact support_fderiv_apply_basisVec_subset_of_tsupport_subset i
        (u.approx_support_subset n)
    change eLpNorm (ψ n) (sobolevTwoStar d) μ ≤
      Cgns * ∑ i : Fin d,
        eLpNorm (fun x => (fderiv ℝ (ψ n) x) (basisVec i)) 2 μ
    rw [show μ = volume.restrict U from rfl,
      eLpNorm_restrict_eq_of_support_subset
        (u.approx_smooth n).continuous.aestronglyMeasurable hvalue_support]
    refine (eLpNorm_sobolevTwoStar_le_sum_eLpNorm_fderiv_apply_basisVec
      hd ((u.approx_smooth n).of_le (by simp))
      (u.approx_hasCompactSupport n)).trans ?_
    change Cgns * ∑ i : Fin d,
      eLpNorm (fun x => (fderiv ℝ (ψ n) x) (basisVec i)) 2 volume ≤
        Cgns * ∑ i : Fin d,
          eLpNorm (fun x => (fderiv ℝ (ψ n) x) (basisVec i)) 2
            (volume.restrict U)
    apply mul_le_mul_right
    refine Finset.sum_le_sum fun i _ => ?_
    rw [eLpNorm_restrict_eq_of_support_subset
      (((u.approx_smooth n).continuous_fderiv (by simp)).clm_apply
        continuous_const).aestronglyMeasurable (hcoordinate_support i)]
  have hb_tend : Tendsto b atTop (𝓝 binf) := by
    change Tendsto
      (fun n => Cgns * ∑ i : Fin d,
        eLpNorm (fun x => (fderiv ℝ (ψ n) x) (basisVec i)) 2 μ)
      atTop
      (𝓝 (Cgns * ∑ i : Fin d, eLpNorm (fun x => u.grad x i) 2 μ))
    refine ENNReal.Tendsto.const_mul (tendsto_finsetSum _ fun i _ => ?_)
      (Or.inr hCgns_ne_top)
    refine tendsto_eLpNorm_of_tendsto_sub (by norm_num)
      (fun n =>
        ((u.approx_smooth n).continuous_fderiv (by simp)).clm_apply
          continuous_const |>.aestronglyMeasurable)
      (u.gradMemL2 i).aestronglyMeasurable
      (u.gradMemL2 i).eLpNorm_ne_top ?_
    exact u.tendsto_approx_grad i
  have htim : TendstoInMeasure μ ψ atTop u.toFun := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := (2 : ℝ≥0∞))
      (by norm_num) ?_
    exact u.tendsto_approx
  obtain ⟨σ, hσ_mono, hσ_ae⟩ := htim.exists_seq_tendsto_ae
  have hfatou : eLpNorm u.toFun (sobolevTwoStar d) μ ≤
      Filter.liminf (fun n => a (σ n)) atTop := by
    exact Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun n => (u.approx_smooth (σ n)).continuous.aestronglyMeasurable)
      u.toFun u.memL2.aestronglyMeasurable hσ_ae
  have hbound_liminf : Filter.liminf (fun n => a (σ n)) atTop ≤ binf := by
    have hbσ : Tendsto (fun n => b (σ n)) atTop (𝓝 binf) :=
      hb_tend.comp hσ_mono.tendsto_atTop
    calc
      Filter.liminf (fun n => a (σ n)) atTop ≤
          Filter.liminf (fun n => b (σ n)) atTop :=
        Filter.liminf_le_liminf (Eventually.of_forall fun n => hab (σ n))
      _ = binf := hbσ.liminf_eq
  have hcoordinate_sum :
      (∑ i : Fin d, eLpNorm (fun x => u.grad x i) 2 μ) ≤
        (d : ℝ≥0∞) * euclideanFieldELpNormOn U 2 u.grad := by
    calc
      (∑ i : Fin d, eLpNorm (fun x => u.grad x i) 2 μ) ≤
          ∑ _i : Fin d, euclideanFieldELpNormOn U 2 u.grad :=
        Finset.sum_le_sum fun i _ =>
          eLpNorm_coordinate_le_euclideanFieldELpNormOn u.grad i
            (u.gradMemL2 i).aestronglyMeasurable
      _ = (d : ℝ≥0∞) * euclideanFieldELpNormOn U 2 u.grad := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
  change eLpNorm u.toFun (sobolevTwoStar d) μ ≤
    (zeroBoundarySobolevConstantTwo d : ℝ≥0∞) *
      euclideanFieldELpNormOn U 2 u.grad
  calc
    eLpNorm u.toFun (sobolevTwoStar d) μ ≤ binf :=
      hfatou.trans hbound_liminf
    _ ≤ Cgns * ((d : ℝ≥0∞) * euclideanFieldELpNormOn U 2 u.grad) := by
      change Cgns * ∑ i : Fin d, eLpNorm (fun x => u.grad x i) 2 μ ≤
        Cgns * ((d : ℝ≥0∞) * euclideanFieldELpNormOn U 2 u.grad)
      exact mul_le_mul_right hcoordinate_sum _
    _ = (Cgns * (d : ℝ≥0∞)) *
        euclideanFieldELpNormOn U 2 u.grad := by
      ring
    _ ≤ (zeroBoundarySobolevConstantTwo d : ℝ≥0∞) *
        euclideanFieldELpNormOn U 2 u.grad := by
      refine mul_le_mul_left ?_ _
      simp only [zeroBoundarySobolevConstantTwo, ENNReal.coe_add,
        ENNReal.coe_one, ENNReal.coe_mul, ENNReal.coe_natCast]
      rw [mul_comm]
      exact self_le_add_left _ _

/-- The raw critical Sobolev inequality in the public real-valued exponent
notation `sobolevConjugate d 2 = 2d / (d - 2)`. -/
theorem eLpNormOn_sobolevConjugate_two_le_euclideanFieldELpNormOn
    {d : ℕ} (hd : 3 ≤ d) {U : Set (Vec d)}
    (u : H10Function U) :
    eLpNormOn U (ENNReal.ofReal (sobolevConjugate d 2)) u.toFun ≤
      (zeroBoundarySobolevConstantTwo d : ℝ≥0∞) *
        euclideanFieldELpNormOn U 2 u.toH1Function.grad := by
  rw [← sobolevTwoStar_coe_eq_ofReal_sobolevConjugate_two hd]
  exact eLpNormOn_sobolevTwoStar_le_euclideanFieldELpNormOn hd u

/-- The normalized critical Sobolev inequality for a representative-level
`H¹₀(U)` function.  The explicit factor `|U|^(1 / d)` is exactly the scale
introduced when the raw critical inequality is expressed in normalized norms. -/
theorem eLpMeanNormOn_sobolevConjugate_two_le_volume_rpow_mul
    {d : ℕ} (hd : 3 ≤ d) {U : Set (Vec d)}
    (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    (u : H10Function U) :
    eLpMeanNormOn U (ENNReal.ofReal (sobolevConjugate d 2)) u.toFun ≤
      (zeroBoundarySobolevConstantTwo d : ℝ≥0∞) *
        volume U ^ ((d : ℝ)⁻¹) *
          euclideanFieldELpMeanNormOn U 2 u.toH1Function.grad := by
  have hdTwo : (2 : ℝ) < d := by
    exact_mod_cast hd
  have hExponent :
      -(1 / ENNReal.ofReal (sobolevConjugate d 2)).toReal +
          (1 / (2 : ℝ≥0∞)).toReal = (d : ℝ)⁻¹ := by
    rw [toReal_one_div_ofReal_sobolevConjugate (by norm_num) hdTwo]
    norm_num
  rw [eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn hUTop]
  calc
    (volume U)⁻¹ ^
          (1 / ENNReal.ofReal (sobolevConjugate d 2)).toReal *
        eLpNormOn U (ENNReal.ofReal (sobolevConjugate d 2)) u.toFun ≤
      (volume U)⁻¹ ^
          (1 / ENNReal.ofReal (sobolevConjugate d 2)).toReal *
        ((zeroBoundarySobolevConstantTwo d : ℝ≥0∞) *
          euclideanFieldELpNormOn U 2 u.toH1Function.grad) :=
      mul_le_mul_right
        (eLpNormOn_sobolevConjugate_two_le_euclideanFieldELpNormOn hd u) _
    _ = (zeroBoundarySobolevConstantTwo d : ℝ≥0∞) *
        volume U ^ ((d : ℝ)⁻¹) *
          euclideanFieldELpMeanNormOn U 2 u.toH1Function.grad := by
      rw [euclideanFieldELpNormOn_eq_volume_rpow_mul hUPos hUTop]
      rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg]
      calc
        volume U ^ (-(1 / ENNReal.ofReal (sobolevConjugate d 2)).toReal) *
            ((zeroBoundarySobolevConstantTwo d : ℝ≥0∞) *
              (volume U ^ (1 / (2 : ℝ≥0∞)).toReal *
                euclideanFieldELpMeanNormOn U 2 u.toH1Function.grad)) =
          (zeroBoundarySobolevConstantTwo d : ℝ≥0∞) *
            (volume U ^ (-(1 / ENNReal.ofReal (sobolevConjugate d 2)).toReal) *
              volume U ^ (1 / (2 : ℝ≥0∞)).toReal) *
                euclideanFieldELpMeanNormOn U 2 u.toH1Function.grad := by
          ac_rfl
        _ = (zeroBoundarySobolevConstantTwo d : ℝ≥0∞) *
            volume U ^ ((d : ℝ)⁻¹) *
              euclideanFieldELpMeanNormOn U 2 u.toH1Function.grad := by
          rw [← ENNReal.rpow_add _ _ hUPos.ne' hUTop.ne, hExponent]

end PDE
