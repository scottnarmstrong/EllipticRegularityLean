module

public import EllipticRegularity.Parabolic.Cauchy.Duality.MassWeightedFlux
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

@[expose] public section

namespace PDE.Parabolic.Duality

open MeasureTheory Set Filter Topology PDE PDE.Parabolic

/-- The weighted exponential profiles converge pointwise when the cap grows
and the mollifier scale shrinks along the same sequence. -/
theorem cauchyMassSmoothExponentialWeight_diagonal_tendsto {d : ℕ}
    {K : Set (Vec d)} (hK : K.Nonempty) (s Lam ε : ℝ) (z : Vec d × ℝ) :
    Tendsto
      (fun n : ℕ => cauchyMassSmoothExponentialWeight K s (n : ℝ) Lam ε n z)
      atTop
      (𝓝 (cauchyMassTimeDamping s Lam ε z.2 *
        Real.exp (ε * PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K z.1))) := by
  have hdist := cauchyMass_truncatedDistanceMollify_diagonal_tendsto hK z.1
  have hscaled : Tendsto
      (fun n : ℕ => ε * PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify
        K (n : ℝ) n z.1) atTop
      (𝓝 (ε * PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K z.1)) := by
    simpa using hdist.const_mul ε
  have hexp : Tendsto
      (fun n : ℕ => Real.exp (ε * PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify
        K (n : ℝ) n z.1)) atTop
      (𝓝 (Real.exp (ε * PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K z.1))) := by
    exact Real.continuous_exp.continuousAt.tendsto.comp hscaled
  simpa [cauchyMassSmoothExponentialWeight, cauchyMassSpatialExponential] using
    tendsto_const_nhds.mul hexp

/-- Compactly supported initial data give an exponentially weighted `L²`
coefficient flux. The proof passes the cap-uniform estimate to the limit in
`L²`, then compares distance from the support ball with distance from the
origin. -/
theorem cauchyMass_exponential_flux_of_ball_supported {d : ℕ}
    {lam Lam ε S : ℝ} {a : ParCoeffField d} {s T : ℝ}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hfS : ∀ x ∉ euclideanClosedBall (0 : Vec d) S, f x = 0) :
    MemLp
      (fun z : Vec d × ℝ => Real.exp (ε * vecEuclideanNorm z.1) *
        vecEuclideanNorm (matVecMul (a z) (u.grad z)))
      2 (volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s T)) := by
  classical
  let K : Set (Vec d) := euclideanClosedBall 0 S
  let Q : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s T
  let μ : Measure (Vec d × ℝ) := volume.restrict Q
  let N : Vec d × ℝ → ℝ := fun z =>
    vecEuclideanNorm (matVecMul (a z) (u.grad z))
  let ξ : ℕ → Vec d × ℝ → ℝ := fun n z =>
    cauchyMassSmoothExponentialWeight K s (n : ℝ) Lam ε n z
  let F : ℕ → Vec d × ℝ → ℝ := fun n z => ξ n z * N z
  let H : Vec d × ℝ → ℝ := fun z =>
    cauchyMassTimeDamping s Lam ε z.2 *
      Real.exp (ε * PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K z.1) * N z
  let C : ℝ := Lam * Real.exp (2 * ε * Real.sqrt d) * ∫ x : Vec d, f x ^ 2
  have hK : K.Nonempty := by
    refine ⟨0, ?_⟩
    change (0 : Vec d) ∈ euclideanClosedBall 0 S
    rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le hS]
    simpa [vecEuclideanNorm, vecNormSq, vecDot] using hS
  have hLam : 0 < Lam := cauchyMass_Lam_pos hsT ha
  have hLam0 : 0 ≤ Lam := hLam.le
  have hNmem : MemLp N 2 μ := by
    simpa [N, μ, Q] using cauchyMass_flux_magnitude_memLp ha u
  have hFmem : ∀ n : ℕ, MemLp (F n) 2 μ := by
    intro n
    let ξn : Vec d × ℝ → ℝ := ξ n
    have hξcd : ContDiff ℝ 1 ξn := by
      dsimp [ξn, ξ]
      exact cauchyMassSmoothExponentialWeight_contDiff hK (by positivity) n
    have hB : 0 ≤ Real.exp ((ε * (n : ℝ)) + 2 * Lam * ε ^ 2) := by positivity
    have hξbound (z : Vec d × ℝ) :
        |ξn z| ≤ Real.exp ((ε * (n : ℝ)) + 2 * Lam * ε ^ 2) := by
      exact cauchyMassSmoothExponentialWeight_bound hK (by positivity) hLam0 hε n z
    have hξmeas : AEStronglyMeasurable (fun z : Vec d × ℝ => ξn z ^ 2) μ :=
      (hξcd.continuous.pow 2).aestronglyMeasurable
    have hξsqBound : ∀ᵐ z ∂μ,
        ‖ξn z ^ 2‖ ≤ Real.exp ((ε * (n : ℝ)) + 2 * Lam * ε ^ 2) ^ 2 := by
      filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rcases abs_le.mp (hξbound z) with ⟨hlo, hhi⟩
      nlinarith [sq_nonneg
        (Real.exp ((ε * (n : ℝ)) + 2 * Lam * ε ^ 2) - ξn z),
        sq_nonneg (Real.exp ((ε * (n : ℝ)) + 2 * Lam * ε ^ 2) + ξn z)]
    have hFintSq : Integrable (fun z => (F n z) ^ 2) μ := by
      have hmul := hNmem.integrable_sq.bdd_mul hξmeas
        (c := Real.exp ((ε * (n : ℝ)) + 2 * Lam * ε ^ 2) ^ 2) hξsqBound
      exact hmul.congr (ae_of_all _ fun z => by dsimp [F, ξn, ξ]; ring)
    have hFmeas' : AEStronglyMeasurable (F n) μ := by
      exact hξcd.continuous.aestronglyMeasurable.mul hNmem.aestronglyMeasurable
    exact (memLp_two_iff_integrable_sq hFmeas').2 hFintSq
  have hFmeas : ∀ n : ℕ, AEStronglyMeasurable (F n) μ := fun n => (hFmem n).aestronglyMeasurable
  have hNnonneg (z : Vec d × ℝ) : 0 ≤ N z := vecEuclideanNorm_nonneg _
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    have hfSq := hf.integrable_sq
    exact mul_nonneg (mul_nonneg hLam0 (Real.exp_nonneg _))
      (integral_nonneg fun x : Vec d => sq_nonneg (f x))
  have hFintBound (n : ℕ) : ∫ z, (F n z) ^ 2 ∂μ ≤ C := by
    have hbound := cauchyMass_smooth_weighted_flux_bound hsT ha f hf u hu
      hK (by simpa [K] using hfS) (by positivity : 0 ≤ (n : ℝ)) hε n
    simpa [F, ξ, N, μ, Q, C] using hbound
  have hFnormBound (n : ℕ) : eLpNorm (F n) 2 μ ≤ ENNReal.ofReal (Real.sqrt C) := by
    have hsq := PDE.toReal_eLpNorm_two_sq_eq_integral_sq (hFmem n)
    have hreal : (eLpNorm (F n) 2 μ).toReal ≤ Real.sqrt C :=
      Real.le_sqrt_of_sq_le (by rw [hsq]; exact hFintBound n)
    rw [← ENNReal.ofReal_toReal (hFmem n).eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal hreal
  have hDlip : PDE.Ch4Infra.EucLip 1
      (PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K) :=
    PDE.Parabolic.Cauchy.Weights.euclideanSetDistance_eucLip hK
  have hDcont : Continuous (PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K) :=
    hDlip.continuous (by norm_num)
  have hHweight : Continuous (fun z : Vec d × ℝ =>
      cauchyMassTimeDamping s Lam ε z.2 *
        Real.exp (ε * PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K z.1)) := by
    have htime : Continuous (fun z : Vec d × ℝ => cauchyMassTimeDamping s Lam ε z.2) := by
      dsimp [cauchyMassTimeDamping, cauchyMassTimePrimitive]
      fun_prop
    have hspace : Continuous (fun z : Vec d × ℝ =>
        Real.exp (ε * PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K z.1)) := by
      exact Real.continuous_exp.comp
        (continuous_const.mul (hDcont.comp continuous_fst))
    exact htime.mul hspace
  have hHmeas : AEStronglyMeasurable H μ :=
    hHweight.aestronglyMeasurable.mul hNmem.aestronglyMeasurable
  have hHconv : ∀ᵐ z ∂μ, Tendsto (fun n => F n z) atTop (𝓝 (H z)) := by
    filter_upwards [] with z
    have hξ := cauchyMassSmoothExponentialWeight_diagonal_tendsto hK s Lam ε z
    have hprod := hξ.mul_const (N z)
    simpa [F, ξ, N, H] using hprod
  have hHnorm : eLpNorm H 2 μ ≤ Filter.liminf (fun n => eLpNorm (F n) 2 μ) atTop :=
    MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm hFmeas H hHmeas hHconv
  have hlimBound : Filter.liminf (fun n => eLpNorm (F n) 2 μ) atTop ≤
      ENNReal.ofReal (Real.sqrt C) :=
    liminf_le_of_frequently_le' (Frequently.of_forall hFnormBound)
  have hHtop : eLpNorm H 2 μ < ⊤ := by
    exact lt_of_le_of_lt hHnorm (lt_of_le_of_lt hlimBound (by simp))
  have hHmem : MemLp H 2 μ := by
    rw [memLp_iff]
    exact hHtop
  have hεS : 0 ≤ ε * S := mul_nonneg hε hS
  let c₀ : ℝ := Real.exp (-(2 * Lam * ε ^ 2) * (T - s) - ε * S)
  have hc₀ : 0 < c₀ := by positivity
  have htargetMeas : AEStronglyMeasurable
      (fun z : Vec d × ℝ => Real.exp (ε * vecEuclideanNorm z.1) * N z) μ := by
    have hweight : Continuous (fun z : Vec d × ℝ => Real.exp (ε * vecEuclideanNorm z.1)) :=
      Real.continuous_exp.comp
        (continuous_const.mul (continuous_vecEuclideanNorm.comp continuous_fst))
    exact hweight.aestronglyMeasurable.mul hNmem.aestronglyMeasurable
  have htargetBound : ∀ᵐ z ∂μ,
      ‖Real.exp (ε * vecEuclideanNorm z.1) * N z‖ ≤ c₀⁻¹ * ‖H z‖ := by
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ioc)] with z hz
    have ht : z.2 ∈ Ioc s T := hz.2
    have hdist := cauchyMass_distanceFromClosedBall_lower hS z.1
    have hκ : 0 ≤ 2 * Lam * ε ^ 2 := by positivity
    have htimeRange : z.2 - s ≤ T - s := by linarith [ht.2]
    have htimeExp : -(2 * Lam * ε ^ 2) * (T - s) ≤
        -(2 * Lam * ε ^ 2) * (z.2 - s) :=
      mul_le_mul_of_nonpos_left htimeRange (neg_nonpos.mpr hκ)
    have hspaceExp : ε * (vecEuclideanNorm z.1 - S) ≤
        ε * PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K z.1 := by
      exact mul_le_mul_of_nonneg_left (by simpa [K] using hdist) hε
    have hexp : -(2 * Lam * ε ^ 2) * (T - s) - ε * S +
          ε * vecEuclideanNorm z.1 ≤
        -(2 * Lam * ε ^ 2) * (z.2 - s) +
          ε * PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K z.1 := by
      nlinarith
    have htimeEq : cauchyMassTimeDamping s Lam ε z.2 =
        Real.exp (-(2 * Lam * ε ^ 2) * (z.2 - s)) := by
      change Real.exp (-(2 * Lam * ε ^ 2) * cauchyMassTimePrimitive s z.2) = _
      rw [cauchyMassTimePrimitive_eq_sub ht.1.le]
    have hcoef : c₀ * Real.exp (ε * vecEuclideanNorm z.1) ≤
        cauchyMassTimeDamping s Lam ε z.2 *
          Real.exp (ε * PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K z.1) := by
      have he := Real.exp_le_exp.mpr hexp
      calc
        _ = Real.exp (-(2 * Lam * ε ^ 2) * (T - s) - ε * S +
            ε * vecEuclideanNorm z.1) := by
          dsimp [c₀]
          rw [← Real.exp_add]
        _ ≤ Real.exp (-(2 * Lam * ε ^ 2) * (z.2 - s) +
            ε * PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K z.1) := he
        _ = cauchyMassTimeDamping s Lam ε z.2 *
            Real.exp (ε * PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K z.1) := by
          rw [htimeEq, Real.exp_add]
    have hprod : c₀ * (Real.exp (ε * vecEuclideanNorm z.1) * N z) ≤ H z := by
      calc
        _ = (c₀ * Real.exp (ε * vecEuclideanNorm z.1)) * N z := by ring
        _ ≤ (cauchyMassTimeDamping s Lam ε z.2 *
            Real.exp (ε * PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K z.1)) * N z :=
          mul_le_mul_of_nonneg_right hcoef (hNnonneg z)
        _ = H z := by ring
    have hTargetNN : 0 ≤ Real.exp (ε * vecEuclideanNorm z.1) * N z :=
      mul_nonneg (Real.exp_nonneg _) (hNnonneg z)
    have hHNN : 0 ≤ H z := by
      dsimp [H, cauchyMassTimeDamping]
      exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
        (hNnonneg z)
    have hdiv : Real.exp (ε * vecEuclideanNorm z.1) * N z ≤ c₀⁻¹ * H z := by
      calc
        _ = c₀⁻¹ * (c₀ * (Real.exp (ε * vecEuclideanNorm z.1) * N z)) := by
          field_simp [hc₀.ne']
        _ ≤ c₀⁻¹ * H z := mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr hc₀.le)
    simpa [Real.norm_eq_abs, abs_of_nonneg (hNnonneg z),
      abs_of_nonneg hTargetNN, abs_of_nonneg hHNN] using hdiv
  exact hHmem.of_le_mul (c := c₀⁻¹) htargetMeas htargetBound

end PDE.Parabolic.Duality
