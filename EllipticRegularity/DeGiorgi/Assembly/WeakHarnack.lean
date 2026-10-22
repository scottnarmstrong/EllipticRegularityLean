module

public import EllipticRegularity.DeGiorgi.Assembly.WeakHarnackChain
public import EllipticRegularity.DeGiorgi.Assembly.WeakHarnackReal

/-!
# The weak Harnack inequality (assembly)

Proposition 4.17, assembled from the weak Harnack estimates Proposition 4.14, the
crossover estimate Proposition 4.16 and the dilation of supersolutions.
-/

@[expose] public section

open scoped ENNReal Pointwise

namespace PDE.DGNMAssembly

open MeasureTheory Filter

variable {d : ℕ}

/-- The weak Harnack inequality for `q ∈ [1/2, 1)`. -/
theorem weakHarnack_step1 (d : ℕ) (hd : 3 ≤ d) (hWH0 : WeakHarnack0Concl d)
    (hCross : CrossoverConcl d) (hS : SuperAffineTransfer d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < u.toFun x) →
      IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) u →
      ∀ q : ℝ, 1 / 2 ≤ q → q < 1 →
        eLpNorm u.toFun (ENNReal.ofReal (q * d / (d - 2)))
            (volumeOn (euclideanBall (0 : Vec d) (1 / 4))) ≤
          ENNReal.ofReal ((C / (1 - q) ^ C) ^ Real.sqrt Λ) *
            essInf (fun x => ENNReal.ofReal (u.toFun x))
              (volumeOn (euclideanBall (0 : Vec d) (1 / 4))) := by
  obtain ⟨C0, hC0, hQ0⟩ := hWH0
  obtain ⟨C1, c, hC1, hc, hc2, hQ1⟩ := hCross
  have hCs : 0 < C0 * 2 ^ (((d : ℝ) + 2) / 2) * 2 ^ (d : ℝ) * 2 ^ ((d : ℝ) / 2) *
      2 ^ (d : ℝ) * C0 * C1 := by positivity
  refine ⟨max 1 (max ((C0 * 2 ^ (((d : ℝ) + 2) / 2) * 2 ^ (d : ℝ) * 2 ^ ((d : ℝ) / 2) *
      2 ^ (d : ℝ) * C0 * C1) ^ (1 / c)) (((d : ℝ) + 2) / c)), le_max_left _ _, ?_⟩
  intro Λ a hmeas hell u hpos hsuper q hq1 hq2
  have hΛ1 : 1 ≤ Λ := one_le_of_elliptic hell
  have hΛ0 : 0 < Λ := by linarith
  have hr : (0 : ℝ) < 1 / 2 := by norm_num
  have hg : 0 < c * Λ ^ (-(1 : ℝ) / 2) := mul_pos hc (Real.rpow_pos_of_pos hΛ0 _)
  have hg2 : Λ * (c * Λ ^ (-(1 : ℝ) / 2)) ^ 2 = c ^ 2 := mul_sq_rpow_neg_half hΛ0
  have hΛg : Λ * (c * Λ ^ (-(1 : ℝ) / 2)) ^ 2 ≤ 1 := by rw [hg2]; nlinarith
  have hgq : c * Λ ^ (-(1 : ℝ) / 2) ≤ q := by
    have : Λ ^ (-(1 : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hΛ1 (by norm_num)
    nlinarith
  have hsub12 : euclideanBall (0 : Vec d) (1 / 2) ⊆ euclideanBall (0 : Vec d) 1 :=
    euclideanBall_mono hr.le (by norm_num)
  obtain ⟨ub, hub, hsuper'⟩ := hS Λ a hmeas hell 0 (1 / 2) hr hsub12 u hsuper
  have hmeas' : ∀ i j : Fin d, AEMeasurable
      (fun y => (fun y => a (0 + (1 / 2 : ℝ) • y)) y i j)
      (volumeOn (euclideanBall (0 : Vec d) 1)) := fun i j =>
    aemeasurable_comp_aff 0 hr hsub12 (f := fun x => a x i j) (hmeas i j)
  have hell' : ∀ y ∈ euclideanBall (0 : Vec d) 1,
      IsEllipticMatrix 1 Λ ((fun y => a (0 + (1 / 2 : ℝ) • y)) y) := by
    intro y hy
    apply hell
    have : 0 + (1 / 2 : ℝ) • y ∈ euclideanBall (0 : Vec d) (1 / 2 * 1) :=
      (aff_mem_ball_iff 0 y hr one_pos).2 hy
    exact hsub12 (by simpa using this)
  have hpos' : ∀ᵐ y ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < ub.toFun y := by
    have h1 := ae_pos_ball (u := u) hpos (ρ := 1 / 2) (by norm_num) hr
    have h2 := (ae_ball_comp_aff_iff (0 : Vec d) hr (one_pos : (0 : ℝ) < 1)
      (fun x => 0 < u.toFun x)).2 (by simpa using h1)
    filter_upwards [h2] with y hy
    rw [hub]; exact hy
  obtain ⟨hE1all, hE2all⟩ := hQ0 Λ (fun y => a (0 + (1 / 2 : ℝ) • y)) hmeas' hell' ub hpos'
    hsuper'
  have E1 := hE1all _ hg
  have E2 := (hE2all _ q hg hgq hq2).1
  have E3 := hQ1 Λ a hmeas hell u hpos hsuper
  have hchain := weakHarnack_chain_instance hd u ub hub hpos C0 C1 Λ _ q hC0 hC1 hg hgq hq2 hΛg
    hΛ0 E1 E2 E3
  have hq0 : 0 < 1 - q := by linarith
  have hq1' : 1 - q ≤ 1 := by linarith
  set g := c * Λ ^ (-(1 : ℝ) / 2) with hgdef
  have hginv : 0 < 1 / g := one_div_pos.2 hg
  have h1 := ENNReal.rpow_le_rpow hchain hginv.le
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hg.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ hginv.le, ← ENNReal.rpow_mul, mul_one_div_cancel hg.ne',
    ENNReal.rpow_one, ENNReal.ofReal_rpow_of_nonneg (by positivity) hginv.le] at h1
  refine h1.trans ?_
  gcongr
  exact final_exponent_bound (e := (d : ℝ) + 2) hCs hc hΛ1 hq0 hq1'

theorem eLpNorm_ofReal_mono_exponent {μ : Measure (Vec d)} {f : Vec d → ℝ} {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hμ : μ Set.univ ≤ 1) (hf : AEStronglyMeasurable f μ) :
    eLpNorm f (ENNReal.ofReal x) μ ≤ eLpNorm f (ENNReal.ofReal y) μ := by
  refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (ENNReal.ofReal_le_ofReal hxy) hf).trans ?_
  have hexp : 0 ≤ 1 / (ENNReal.ofReal x).toReal - 1 / (ENNReal.ofReal y).toReal := by
    rw [ENNReal.toReal_ofReal hx.le, ENNReal.toReal_ofReal (hx.le.trans hxy)]
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le hx hxy
  calc eLpNorm f (ENNReal.ofReal y) μ *
        μ Set.univ ^ (1 / (ENNReal.ofReal x).toReal - 1 / (ENNReal.ofReal y).toReal)
      ≤ eLpNorm f (ENNReal.ofReal y) μ * 1 := by
        gcongr
        exact ENNReal.rpow_le_one hμ hexp
    _ = _ := mul_one _

/-- **Weak Harnack inequality** (Proposition 4.17), assembled from the weak Harnack
estimates, the crossover estimate and the dilation of supersolutions, which are taken as
explicit hypotheses. -/
theorem exists_weakHarnack_constant_full (d : ℕ) (hd : 3 ≤ d) (hWH0 : WeakHarnack0Concl d)
    (hCross : CrossoverConcl d) (hS : SuperAffineTransfer d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < u.toFun x) →
      IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) u →
      ∀ q : ℝ, 0 < q → q < 1 →
        eLpNorm u.toFun (ENNReal.ofReal (q * d / (d - 2))) (volumeOn (euclideanBall (0 : Vec d) (1 / 4))) ≤
          ENNReal.ofReal ((C / (1 - q) ^ C) ^ Real.sqrt Λ) *
            essInf (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall (0 : Vec d) (1 / 4))) := by
  obtain ⟨C1, hC1, hstep⟩ := weakHarnack_step1 d hd hWH0 hCross hS
  have hC1pos : 0 < C1 := lt_of_lt_of_le one_pos hC1
  have hCfin : 0 < C1 * 2 ^ C1 := by positivity
  refine ⟨C1 * 2 ^ C1, hCfin, ?_⟩
  intro Λ a hmeas hell u hpos hsuper q hq0 hq1
  have hΛ1 : 1 ≤ Λ := one_le_of_elliptic hell
  have ht0 : 0 < 1 - q := by linarith
  have ht1 : 1 - q ≤ 1 := by linarith
  have hs : 0 ≤ Real.sqrt Λ := Real.sqrt_nonneg _
  have hd2 : (0 : ℝ) < (d : ℝ) - 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  by_cases hq : 1 / 2 ≤ q
  · refine (hstep Λ a hmeas hell u hpos hsuper q hq hq1).trans ?_
    have hc1 : C1 ≤ C1 * 2 ^ C1 :=
      le_mul_of_one_le_right hC1pos.le (Real.one_le_rpow (by norm_num) hC1pos.le)
    have hpow : (1 - q) ^ (C1 * 2 ^ C1) ≤ (1 - q) ^ C1 :=
      Real.rpow_le_rpow_of_exponent_ge ht0 ht1 hc1
    have hbase : C1 / (1 - q) ^ C1 ≤ C1 * 2 ^ C1 / (1 - q) ^ (C1 * 2 ^ C1) :=
      div_le_div₀ hCfin.le hc1 (Real.rpow_pos_of_pos ht0 _) hpow
    have hreal := Real.rpow_le_rpow (by positivity) hbase hs
    gcongr
  · rw [not_le] at hq
    have h1 := hstep Λ a hmeas hell u hpos hsuper (1 / 2) le_rfl (by norm_num)
    have hmono : eLpNorm u.toFun (ENNReal.ofReal (q * d / (d - 2)))
          (volumeOn (euclideanBall (0 : Vec d) (1 / 4))) ≤
        eLpNorm u.toFun (ENNReal.ofReal (1 / 2 * d / (d - 2)))
          (volumeOn (euclideanBall (0 : Vec d) (1 / 4))) := by
      refine eLpNorm_ofReal_mono_exponent (by positivity) ?_ ?_
        (aestronglyMeasurable_ball u (by norm_num) (by norm_num))
      · gcongr
      · simpa [volumeOn] using volume_euclideanBall_le_one (d := d) (ρ := 1 / 4) (by norm_num)
          (by norm_num) 0
    refine hmono.trans (h1.trans ?_)
    have h2 : (1 - (1 / 2 : ℝ)) = 2⁻¹ := by norm_num
    have hpow : (1 - q) ^ (C1 * 2 ^ C1) ≤ 1 := Real.rpow_le_one ht0.le ht1 hCfin.le
    have hbase : C1 / (1 - (1 / 2 : ℝ)) ^ C1 ≤ C1 * 2 ^ C1 / (1 - q) ^ (C1 * 2 ^ C1) := by
      rw [h2, Real.inv_rpow (by norm_num), div_inv_eq_mul,
        le_div_iff₀ (Real.rpow_pos_of_pos ht0 _)]
      nlinarith
    have hreal := Real.rpow_le_rpow (by positivity) hbase hs
    gcongr

end PDE.DGNMAssembly
