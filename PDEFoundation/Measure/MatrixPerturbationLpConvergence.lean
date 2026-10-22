module

public import PDEFoundation.Measure.LpDominatedConvergence
public import PDEFoundation.Measure.LpPower
public import PDEFoundation.PDE.PerturbativeForcingLpBound

/-! # Strong convergence of coefficient perturbation fluxes -/

@[expose] public section

namespace PDE

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

/-- Pointwise convergence of uniformly identity-close coefficient fields gives
strong `L²` convergence after acting on one fixed native `L²` field. -/
theorem tendsto_eLpNorm_matrix_sub_mulVec_zero_of_ae
    {d : ℕ} {μ : Measure (Vec d)}
    {g : Vec d → Vec d} (hg : ∀ i, MemLp (fun x => g x i) 2 μ)
    {aSeq : ℕ → CoeffField d} {a : CoeffField d} {delta : ℝ}
    (hdelta : 0 ≤ delta)
    (haSeq : ∀ n i j, AEMeasurable (fun x => aSeq n x i j) μ)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) μ)
    (hcloseSeq : ∀ n, ∀ᵐ x ∂μ,
      IsMatrixPerturbationLE delta (aSeq n x) (1 : Mat d))
    (hclose : ∀ᵐ x ∂μ, IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (hconv : ∀ i j, ∀ᵐ x ∂μ,
      Tendsto (fun n => aSeq n x i j) atTop (𝓝 (a x i j))) :
    Tendsto (fun n => eLpNorm (fun x => vecEuclideanNorm
      (matVecMul (aSeq n x - a x) (g x))) 2 μ) atTop (𝓝 0) := by
  let q : ℕ → Vec d → ℝ := fun n x =>
    vecEuclideanNorm (matVecMul (aSeq n x - a x) (g x))
  let b : Vec d → ℝ := fun x => 2 * delta * vecEuclideanNorm (g x)
  have hgcoord : ∀ i, AEStronglyMeasurable (fun x => g x i) μ :=
    fun i => (hg i).aestronglyMeasurable
  have hqmeas (n : ℕ) : AEStronglyMeasurable (q n) μ := by
    let Pn : Vec d → Vec d := fun x => matVecMul (aSeq n x - 1) (g x)
    let P : Vec d → Vec d := fun x => matVecMul (a x - 1) (g x)
    have hncoord : ∀ i, AEStronglyMeasurable (fun x => Pn x i) μ :=
      fun i => aestronglyMeasurable_perturbationFlux_coord (haSeq n) hgcoord i
    have hcoord : ∀ i, AEStronglyMeasurable (fun x => P x i) μ :=
      fun i => aestronglyMeasurable_perturbationFlux_coord ha hgcoord i
    have hdiff : ∀ i, AEStronglyMeasurable (fun x => Pn x i - P x i) μ :=
      fun i => (hncoord i).sub (hcoord i)
    have hmag := aestronglyMeasurable_vecEuclideanNorm_of_coord hdiff
    apply hmag.congr
    filter_upwards with x
    dsimp only [q, Pn, P]
    congr 1
    classical
    change (aSeq n x - 1).mulVec (g x) - (a x - 1).mulVec (g x) =
      (aSeq n x - a x).mulVec (g x)
    rw [← Matrix.sub_mulVec]
    congr 1
    abel
  have hbound (n : ℕ) : ∀ᵐ x ∂μ, q n x ≤ b x := by
    filter_upwards [hcloseSeq n, hclose] with x hxn hx
    have hn := hxn (g x)
    have hh := hx (g x)
    have hsplit : matVecMul (aSeq n x - a x) (g x) =
        matVecMul (aSeq n x - 1) (g x) -
          matVecMul (a x - 1) (g x) := by
      classical
      change (aSeq n x - a x).mulVec (g x) =
        (aSeq n x - 1).mulVec (g x) - (a x - 1).mulVec (g x)
      rw [← Matrix.sub_mulVec]
      congr 1
      abel
    calc
      q n x = vecEuclideanNorm
          (matVecMul (aSeq n x - 1) (g x) -
            matVecMul (a x - 1) (g x)) := congrArg vecEuclideanNorm hsplit
      _ ≤ vecEuclideanNorm (matVecMul (aSeq n x - 1) (g x)) +
          vecEuclideanNorm (matVecMul (a x - 1) (g x)) := by
        let X := matVecMul (aSeq n x - 1) (g x)
        let Y := matVecMul (a x - 1) (g x)
        change vecEuclideanNorm (X - Y) ≤ vecEuclideanNorm X + vecEuclideanNorm Y
        simpa only [sub_eq_add_neg, vecEuclideanNorm_neg] using
          vecEuclideanNorm_add_le X (-Y)
      _ ≤ delta * vecEuclideanNorm (g x) +
          delta * vecEuclideanNorm (g x) := add_le_add hn hh
      _ = b x := by
        dsimp only [b]
        rw [← two_mul, mul_assoc]
  have hgHilbert : MemLp (toHilbertVecField g) 2 μ := by
    simpa only [toHilbertVecField, Vec.toHilbertVec_apply] using
      (memLp_piLp_iff (f := toHilbertVecField g) (p := 2) (μ := μ)).mpr hg
  have hgmag : MemLp (fun x => vecEuclideanNorm (g x)) 2 μ :=
    hgHilbert.norm.ae_eq (Filter.Eventually.of_forall
      (norm_toHilbertVecField_apply g))
  have hbmem : MemLp b 2 μ := by
    simpa only [b] using hgmag.const_mul (2 * delta)
  have hqmem (n : ℕ) : MemLp (q n) 2 μ := by
    apply hbmem.mono (hqmeas n)
    filter_upwards [hbound n] with x hx
    have hq0 : 0 ≤ q n x := vecEuclideanNorm_nonneg _
    have hb0 : 0 ≤ b x := by
      exact mul_nonneg (mul_nonneg (by norm_num) hdelta)
        (vecEuclideanNorm_nonneg _)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hq0, abs_of_nonneg hb0] using hx
  have hpoint : ∀ᵐ x ∂μ, Tendsto (fun n => q n x) atTop (𝓝 0) := by
    have hall : ∀ᵐ x ∂μ, ∀ i j,
        Tendsto (fun n => aSeq n x i j) atTop (𝓝 (a x i j)) :=
      ae_all_iff.mpr fun i => ae_all_iff.mpr (hconv i)
    filter_upwards [hall] with x hx
    have hvec : Tendsto
        (fun n => matVecMul (aSeq n x - a x) (g x)) atTop
          (𝓝 (0 : Vec d)) := by
      rw [tendsto_pi_nhds]
      intro i
      change Tendsto
        (fun n => ∑ j, (aSeq n x i j - a x i j) * g x j) atTop
          (𝓝 ((0 : Vec d) i))
      have hs := tendsto_finsetSum Finset.univ (fun j _ =>
        ((hx i j).sub_const (a x i j)).mul_const (g x j))
      convert hs using 1
      all_goals simp
    have ht := (continuous_vecEuclideanNorm.tendsto (0 : Vec d)).comp hvec
    have h0 : vecEuclideanNorm (0 : Vec d) = 0 := by
      simp [vecEuclideanNorm, vecNormSq, vecDot]
    rw [h0] at ht
    exact ht
  have hsqMeas (n : ℕ) : AEStronglyMeasurable (fun x => (q n x) ^ 2) μ :=
    (hqmeas n).pow 2
  have hbsq : Integrable (fun x => (b x) ^ 2) μ := by
    have hbpow := hbmem.integrable_norm_rpow (by norm_num) (by norm_num)
    apply hbpow.congr
    filter_upwards with x
    have hb0 : 0 ≤ b x := by
      exact mul_nonneg (mul_nonneg (by norm_num) hdelta)
        (vecEuclideanNorm_nonneg _)
    simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, abs_of_nonneg hb0,
      Real.rpow_two]
  have hsqBound (n : ℕ) : ∀ᵐ x ∂μ, ‖(q n x) ^ 2‖ ≤ (b x) ^ 2 := by
    filter_upwards [hbound n] with x hx
    have hqn := vecEuclideanNorm_nonneg
      (matVecMul (aSeq n x - a x) (g x))
    have hb0 : 0 ≤ b x := by
      exact mul_nonneg (mul_nonneg (by norm_num) hdelta)
        (vecEuclideanNorm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [q, pow_two] using mul_self_le_mul_self hqn hx
  have hsqPoint : ∀ᵐ x ∂μ,
      Tendsto (fun n => (q n x) ^ 2) atTop (𝓝 0) := by
    filter_upwards [hpoint] with x hx
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hx.pow 2
  have hint := tendsto_integral_of_dominated_convergence (fun x => (b x) ^ 2)
    hsqMeas hbsq hsqBound hsqPoint
  have hint0 : Tendsto (fun n => ∫ x, (q n x) ^ 2 ∂μ) atTop (𝓝 0) := by
    simpa only [integral_zero] using hint
  simpa only [q] using
    tendsto_eLpNorm_two_zero_of_tendsto_integral_sq hqmem hint0

end

end PDE
