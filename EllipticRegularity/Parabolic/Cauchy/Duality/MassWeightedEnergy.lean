module

public import EllipticRegularity.Parabolic.Cauchy.Duality.MassWeight
public import EllipticRegularity.Parabolic.Cauchy.Energy.Density

/-! # Weighted energy for the Cauchy mass argument -/

@[expose] public section

namespace PDE.Parabolic.Duality

open MeasureTheory Set PDE PDE.Parabolic

theorem cauchyMass_Lam_pos {d : ℕ} {lam Lam s T : ℝ}
    {a : ParCoeffField d} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) : 0 < Lam := by
  let S : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Icc s T
  let B : Set (Vec d) := euclideanBall 0 1
  have hB : 0 < volume B := volume_euclideanBall_pos 0 (by norm_num)
  have hI : 0 < volume (Ioo s T) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hsT)
  have hrect : 0 < volume (B ×ˢ Ioo s T) := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_pos hB.ne' hI.ne'
  have hsub : B ×ˢ Ioo s T ⊆ S := by
    intro z hz
    exact ⟨Set.mem_univ _, ⟨hz.2.1.le, hz.2.2.le⟩⟩
  have hS : 0 < volume S := lt_of_lt_of_le hrect (measure_mono hsub)
  have hμ : (volume.restrict S : Measure (Vec d × ℝ)) ≠ 0 := by
    intro hzero
    have hval := congrArg (fun μ : Measure (Vec d × ℝ) => μ univ) hzero
    rw [Measure.restrict_apply_univ] at hval
    have hS0 : volume S = 0 := by simpa using hval
    exact (ne_of_gt hS) hS0
  let : NeZero (volume.restrict S : Measure (Vec d × ℝ)) := ⟨hμ⟩
  obtain ⟨z, hz⟩ := ha.elliptic.exists
  exact hz.Lam_pos

/-- The smooth exponential weight satisfies the density inequality required by
the weighted energy identity. -/
theorem cauchyMassSmoothWeighted_density {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    {K : Set (Vec d)} (hK : K.Nonempty) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 ≤ ε) (n : ℕ) :
    let ξ := cauchyMassSmoothExponentialWeight K s R Lam ε n
    let loss := fun z : Vec d × ℝ =>
      (1 / 2 : ℝ) * ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z
    ∀ᵐ z ∂(volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s T)),
      u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z ≤
        ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
          2 * ξ z * u.toFun z *
            vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z) - loss z := by
  classical
  let ξ := cauchyMassSmoothExponentialWeight K s R Lam ε n
  let loss := fun z : Vec d × ℝ =>
    (1 / 2 : ℝ) * ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z
  change ∀ᵐ z ∂(volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s T)), _
  have hQsub : (univ : Set (Vec d)) ×ˢ Ioc s T ⊆
      (univ : Set (Vec d)) ×ˢ Icc s T :=
    prod_mono subset_rfl Ioc_subset_Icc_self
  have hEll : ∀ᵐ z ∂(volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s T)),
      IsEllipticMatrix lam Lam (a z) :=
    ha.elliptic.filter_mono (ae_mono (Measure.restrict_mono hQsub le_rfl))
  have hmem : ∀ᵐ z ∂(volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s T)),
      z.2 ∈ Ioc s T := by
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ioc)] with z hz
    exact hz.2
  filter_upwards [hEll, hmem] with z hzEll hz
  have hξpos (y : Vec d × ℝ) : 0 < ξ y := by
    dsimp [ξ, cauchyMassSmoothExponentialWeight,
      cauchyMassTimeDamping, cauchyMassSpatialExponential]
    exact mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have hξtime := cauchyMassSmoothExponentialWeight_timeDeriv
    (s := s) (Lam := Lam) (ε := ε) hK hR n hz.1
  have hξgrad := cauchyMassSmoothExponentialWeight_gradient_bound
    (s := s) (Lam := Lam) (ε := ε) hK hR hε n z
  let p : Vec d := (ξ z)⁻¹ • parSpaceGrad ξ z
  have hpBound : vecNormSq p ≤ ε ^ 2 := by
    have hnorm : vecEuclideanNorm p ≤ ε := by
      dsimp [p]
      rw [vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr (hξpos z))]
      calc
        (ξ z)⁻¹ * vecEuclideanNorm (parSpaceGrad ξ z) ≤
            (ξ z)⁻¹ * (ε * ξ z) :=
          mul_le_mul_of_nonneg_left hξgrad (inv_nonneg.mpr (hξpos z).le)
        _ = ε := by field_simp [ne_of_gt (hξpos z)]
    rw [← vecEuclideanNorm_sq]
    nlinarith [vecEuclideanNorm_nonneg p]
  have hhalf := cauchyMass_half_cross_term_bound hzEll (u.toFun z)
    (u.grad z) p
  have hhalf' :
      -(1 / 2 : ℝ) * vecDot (u.grad z) (matVecMul (a z) (u.grad z)) -
        2 * u.toFun z * vecDot (matVecMul (a z) (u.grad z)) p ≤
      2 * Lam * ε ^ 2 * u.toFun z ^ 2 := by
    calc
      _ ≤ 2 * Lam * vecNormSq p * u.toFun z ^ 2 := hhalf
      _ ≤ 2 * Lam * ε ^ 2 * u.toFun z ^ 2 := by
        have hLam : 0 ≤ Lam := le_of_lt hzEll.Lam_pos
        have hu2 : 0 ≤ u.toFun z ^ 2 := sq_nonneg _
        have hmul := mul_le_mul_of_nonneg_left hpBound
          (mul_nonneg (by positivity : 0 ≤ 2 * Lam) hu2)
        nlinarith
  have hgradRel : parSpaceGrad ξ z = ξ z • p := by
    dsimp [p]
    rw [smul_smul, mul_inv_cancel₀ (hξpos z).ne', one_smul]
  have hfluxRel :
      vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z) =
        ξ z * vecDot (matVecMul (a z) (u.grad z)) p := by
    rw [hgradRel, PDE.Parabolic.WeakSlice.vecDot_smul_right']
  have hscaled := mul_le_mul_of_nonneg_left hhalf' (sq_nonneg (ξ z))
  rw [hξtime, hfluxRel]
  dsimp [loss, PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity]
  nlinarith [hscaled]

/-- Weighted energy estimate for a smoothed, capped exponential distance. -/
theorem cauchyMassSmoothWeighted_energy_dissipation {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u)
    {K : Set (Vec d)} (hK : K.Nonempty) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 ≤ ε) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc s T) (hst : s < t) :
    let ξ := cauchyMassSmoothExponentialWeight K s R Lam ε n
    (∫ x : Vec d, ξ (x, t) ^ 2 * u.toFun (x, t) ^ 2) +
        2 * ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
          (1 / 2 : ℝ) * ξ z ^ 2 *
            PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z ≤
      ∫ x : Vec d, ξ (x, s) ^ 2 * f x ^ 2 := by
  let ξ := cauchyMassSmoothExponentialWeight K s R Lam ε n
  let B : ℝ := Real.exp (ε * R + 2 * Lam * ε ^ 2)
  let Bt : ℝ := 9 * (2 * Lam * ε ^ 2) * B
  let Bg : ℝ := ε * B
  have hLam : 0 ≤ Lam := (cauchyMass_Lam_pos hsT ha).le
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hBt : 0 ≤ Bt := by dsimp [Bt]; positivity
  have hBg : 0 ≤ Bg := by dsimp [Bg]; positivity
  have hξcd : ContDiff ℝ 1 ξ := by
    dsimp [ξ]
    exact cauchyMassSmoothExponentialWeight_contDiff hK hR n
  have hξbound : ∀ z, |ξ z| ≤ B := by
    intro z
    exact cauchyMassSmoothExponentialWeight_bound
      (s := s) (Lam := Lam) (ε := ε) hK hR hLam hε n z
  have hξtbound : ∀ z, |parTimeDeriv ξ z| ≤ Bt := by
    intro z
    rw [cauchyMassSmoothExponentialWeight_timeDeriv_eq
      (s := s) (Lam := Lam) (ε := ε) hK hR n z]
    have hc : 0 ≤ 2 * Lam * ε ^ 2 := by positivity
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hc]
    have hp := deriv_cauchyMassTimePrimitive_abs_le_nine s z.2
    have hξ := hξbound z
    calc
      2 * Lam * ε ^ 2 * |deriv (cauchyMassTimePrimitive s) z.2| * |ξ z| ≤
          2 * Lam * ε ^ 2 * (9 * B) := by
            calc
              _ = 2 * Lam * ε ^ 2 *
                  (|deriv (cauchyMassTimePrimitive s) z.2| * |ξ z|) := by ring
              _ ≤ 2 * Lam * ε ^ 2 * (9 * B) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul hp hξ (abs_nonneg _) (by norm_num)) hc
      _ = Bt := by dsimp [Bt, B]; ring
  have hξgradbound : ∀ z, vecEuclideanNorm (parSpaceGrad ξ z) ≤ Bg := by
    intro z
    have hgrad := cauchyMassSmoothExponentialWeight_gradient_bound
      (s := s) (Lam := Lam) (ε := ε) hK hR hε n z
    have hξle : ξ z ≤ B := (le_abs_self _).trans (hξbound z)
    calc
      vecEuclideanNorm (parSpaceGrad ξ z) ≤ ε * ξ z := hgrad
      _ ≤ ε * B := mul_le_mul_of_nonneg_left hξle hε
      _ = Bg := rfl
  let loss : Vec d × ℝ → ℝ := fun z =>
    (1 / 2 : ℝ) * ξ z ^ 2 *
      PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z
  have hQint : IntegrableOn (PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u)
      ((univ : Set (Vec d)) ×ˢ Ioc s t) :=
    PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity_integrable_Ioc ha u ht
  have hcoefMeas : AEStronglyMeasurable (fun z : Vec d × ℝ => (1 / 2 : ℝ) * ξ z ^ 2)
      (volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s t)) := by
    exact (continuous_const.mul (hξcd.continuous.pow 2)).aestronglyMeasurable
  have hcoefBound : ∀ᵐ z ∂(volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s t)),
      ‖(1 / 2 : ℝ) * ξ z ^ 2‖ ≤ (1 / 2 : ℝ) * B ^ 2 := by
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_of_nonneg (sq_nonneg _)]
    have hsq : ξ z ^ 2 ≤ B ^ 2 := by
      rcases abs_le.mp (hξbound z) with ⟨hlo, hhi⟩
      nlinarith [sq_nonneg (B - ξ z), sq_nonneg (B + ξ z)]
    exact mul_le_mul_of_nonneg_left hsq (by norm_num)
  have hlossInt : IntegrableOn loss ((univ : Set (Vec d)) ×ˢ Ioc s t) := by
    change Integrable (fun z => (1 / 2 : ℝ) * ξ z ^ 2 *
      PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z)
      (volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s t))
    have hmul := hQint.bdd_mul hcoefMeas (c := (1 / 2 : ℝ) * B ^ 2) hcoefBound
    exact hmul.congr (ae_of_all _ fun z => by ring)
  have hdensity := cauchyMassSmoothWeighted_density ha u hK hR hε n
  have hsub : (univ : Set (Vec d)) ×ˢ Ioc s t ⊆
      (univ : Set (Vec d)) ×ˢ Ioc s T :=
    prod_mono subset_rfl (fun r hr => ⟨hr.1, hr.2.trans ht.2⟩)
  have hdensity' : ∀ᵐ z ∂(volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s t)),
      u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z ≤
        ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
          2 * ξ z * u.toFun z *
            vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z) - loss z := by
    exact hdensity.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  simpa only [ξ] using
    PDE.Parabolic.Cauchy.Weights.cauchySmoothWeighted_energy_dissipation
      hsT ha f hf u hu ξ hξcd B Bt Bg hB hBt hBg hξbound hξtbound hξgradbound
      ht hst loss hlossInt hdensity'

end PDE.Parabolic.Duality
