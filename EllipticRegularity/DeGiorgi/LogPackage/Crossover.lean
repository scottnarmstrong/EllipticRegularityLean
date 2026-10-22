module

public import EllipticRegularity.DeGiorgi.LogPackage.CrossoverCore
public import EllipticRegularity.DeGiorgi.LogPackage.CrossoverLimit
public import EllipticRegularity.DeGiorgi.LogPackage.Shift
public import Ch1Statements.JohnNirenberg

/-!
# The crossover estimate from the logarithmic energy estimate

Manuscript: Proposition 4.16. The PDE input is the explicit hypothesis `LogEnergyHyp d`; everything else
(BMO from Poincare, John-Nirenberg, exponential integrability, the limit `δ → 0`) is proved here.
-/

@[expose] public section

namespace PDE.DGNMLog

open MeasureTheory

/-- The crossover estimate (Proposition 4.16), with the logarithmic energy estimate
taken as the explicit hypothesis `hLogEnergy`. -/
theorem exists_crossover_constants_full (d : ℕ) (hd : 1 ≤ d) (hLogEnergy : LogEnergyHyp d) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 / 2 ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < u.toFun x) →
      IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) u →
        eLpMeanNormOn (euclideanBall (0 : Vec d) (1 / 2)) 1
            (fun x => u.toFun x ^ (c * Λ ^ (-(1 : ℝ) / 2))) *
          eLpMeanNormOn (euclideanBall (0 : Vec d) (1 / 2)) 1
            (fun x => u.toFun x ^ (-(c * Λ ^ (-(1 : ℝ) / 2)))) ≤ ENNReal.ofReal C := by
  obtain ⟨CJ, hCJ, hJN⟩ := PDE.exists_johnNirenberg_constant d hd
  have hKpos := bmoConst_pos d
  set s : ℝ := Real.sqrt (bmoConst d) with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr hKpos
  set c : ℝ := min (1 / 2) (1 / (2 * CJ * s)) with hc
  have hcpos : 0 < c := lt_min (by norm_num) (by positivity)
  refine ⟨(1 + CJ) ^ 2, c, by positivity, hcpos, min_le_left _ _, ?_⟩
  intro Λ a hmeas hell u hupos hsuper
  have hΛ1 : 1 ≤ Λ := (hell 0 (center_mem_euclideanBall 0 one_pos)).2.1
  have hΛpos : 0 < Λ := by linarith
  have hBsub : (euclideanBall (0 : Vec d) (1 / 2)) ⊆ (euclideanBall (0 : Vec d) 1) := euclideanBall_mono (by norm_num) (by norm_num)
  have hBfin : volume (euclideanBall (0 : Vec d) (1 / 2)) < ⊤ := (volume_euclideanBall_ne_top _ (by norm_num)).lt_top
  have hBpos : 0 < volume (euclideanBall (0 : Vec d) (1 / 2)) := volume_euclideanBall_pos _ (by norm_num)
  have hB1fin : IsFiniteMeasure (volumeOn (euclideanBall (0 : Vec d) 1)) := isFiniteMeasure_volumeOn_euclideanBall _ zero_le_one
  set γ : ℝ := c * Λ ^ (-(1 : ℝ) / 2) with hγ
  have hγpos : 0 < γ := by positivity
  have hshift : ∀ n : ℕ,
      (∫⁻ x in (euclideanBall (0 : Vec d) (1 / 2)), ENNReal.ofReal ((u.toFun x + 1 / ((n : ℝ) + 1)) ^ γ)) *
        (∫⁻ x in (euclideanBall (0 : Vec d) (1 / 2)), ENNReal.ofReal ((u.toFun x + 1 / ((n : ℝ) + 1)) ^ (-γ))) ≤
      ENNReal.ofReal ((1 + CJ) ^ 2) * volume (euclideanBall (0 : Vec d) (1 / 2)) ^ 2 := by
    intro n
    set δ : ℝ := 1 / ((n : ℝ) + 1) with hδ
    have hδpos : 0 < δ := by positivity
    set un := u.addConst δ with hun
    have hunlow : ∃ δ' : ℝ, 0 < δ' ∧ ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), δ' ≤ un.toFun x := by
      refine ⟨δ, hδpos, ?_⟩
      filter_upwards [hupos] with x hx
      simp only [hun, H1Function.addConst_apply]
      linarith [hx]
    obtain ⟨v, hvlog, hvE⟩ :=
      hLogEnergy Λ a hmeas hell un hunlow (superharmonic_addConst hsuper δ)
    set M : ℝ := Real.sqrt (bmoConst d * Λ) with hM
    have hMpos : 0 < M := Real.sqrt_pos.mpr (by positivity)
    have hvint : IntegrableOn v.toFun (euclideanBall (0 : Vec d) (1 / 2)) volume :=
      (v.integrableOn (U := (euclideanBall (0 : Vec d) 1))).mono_set hBsub
    have hBMO : ∀ (y : Vec d) (r : ℝ), 0 < r → closure (euclideanBall y r) ⊆ (euclideanBall (0 : Vec d) (1 / 2)) →
        integralAverage (euclideanBall y r)
          (fun z => |v.toFun z - integralAverage (euclideanBall y r) v.toFun|) ≤ M :=
      fun y r hr hcl => avg_abs_sub_avg_le_of_energy ⟨0, hd⟩ hΛpos v hvE y hr
        (subset_closure.trans hcl)
    obtain ⟨-, htail⟩ := hJN 0 (1 / 2) (by norm_num) v.toFun M hMpos
      hvint.locallyIntegrableOn hBMO
    have hγM : γ ≤ 1 / (2 * CJ * M) := by
      have hsM : M = s * Real.sqrt Λ := by rw [hM, hs, ← Real.sqrt_mul hKpos.le]
      have hΛexp : Λ ^ (-(1 : ℝ) / 2) = (Real.sqrt Λ)⁻¹ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hΛpos.le]; congr 1; ring
      have hsqpos : 0 < Real.sqrt Λ := Real.sqrt_pos.mpr hΛpos
      rw [hγ, hΛexp, hsM]
      have : c ≤ 1 / (2 * CJ * s) := min_le_right _ _
      calc c * (Real.sqrt Λ)⁻¹ ≤ 1 / (2 * CJ * s) * (Real.sqrt Λ)⁻¹ := by gcongr
        _ = 1 / (2 * CJ * (s * Real.sqrt Λ)) := by field_simp
    have hcore := exp_moment_product_le hBfin
      ((v.memL2.aestronglyMeasurable.mono_measure
        (Measure.restrict_mono hBsub le_rfl)).aemeasurable) hCJ hMpos hγpos hγM htail
    have hae : ∀ᵐ x ∂(volume.restrict (euclideanBall (0 : Vec d) (1 / 2))), v.toFun x = Real.log (un.toFun x) ∧ 0 < u.toFun x := by
      have h1 := ae_restrict_of_ae_restrict_of_subset hBsub hvlog
      have h2 := ae_restrict_of_ae_restrict_of_subset hBsub hupos
      filter_upwards [h1, h2] with x hx1 hx2 using ⟨hx1, hx2⟩
    have e1 : ∫⁻ x in (euclideanBall (0 : Vec d) (1 / 2)), ENNReal.ofReal (Real.exp (γ * v.toFun x)) =
        ∫⁻ x in (euclideanBall (0 : Vec d) (1 / 2)), ENNReal.ofReal ((u.toFun x + δ) ^ γ) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with x ⟨hx1, hx2⟩
      have hpos : 0 < u.toFun x + δ := by linarith
      simp only [hun, H1Function.addConst_apply] at hx1
      rw [hx1, Real.rpow_def_of_pos hpos, mul_comm]
    have e2 : ∫⁻ x in (euclideanBall (0 : Vec d) (1 / 2)), ENNReal.ofReal (Real.exp (-γ * v.toFun x)) =
        ∫⁻ x in (euclideanBall (0 : Vec d) (1 / 2)), ENNReal.ofReal ((u.toFun x + δ) ^ (-γ)) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with x ⟨hx1, hx2⟩
      have hpos : 0 < u.toFun x + δ := by linarith
      simp only [hun, H1Function.addConst_apply] at hx1
      rw [hx1, Real.rpow_def_of_pos hpos, mul_comm]
    rw [e1, e2] at hcore
    exact hcore
  have hu' : AEMeasurable u.toFun (volume.restrict (euclideanBall (0 : Vec d) (1 / 2))) :=
    (u.memL2.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono hBsub le_rfl)).aemeasurable
  have hposB : ∀ᵐ x ∂(volume.restrict (euclideanBall (0 : Vec d) (1 / 2))), 0 < u.toFun x :=
    ae_restrict_of_ae_restrict_of_subset hBsub hupos
  have hlim := crossover_product_limit hu' hposB hγpos hshift
  have hnn : ∀ (e : ℝ), ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) (1 / 2))), 0 ≤ u.toFun x ^ e := by
    intro e
    filter_upwards [hposB] with x hx using Real.rpow_nonneg hx.le _
  rw [eLpMeanNormOn_one_eq hBfin (hu'.pow_const _).aestronglyMeasurable (hnn _),
    eLpMeanNormOn_one_eq hBfin (hu'.pow_const _).aestronglyMeasurable (hnn _)]
  have hV : (volume (euclideanBall (0 : Vec d) (1 / 2)))⁻¹ * volume (euclideanBall (0 : Vec d) (1 / 2)) = 1 := ENNReal.inv_mul_cancel hBpos.ne' hBfin.ne
  calc _ = (volume (euclideanBall (0 : Vec d) (1 / 2)))⁻¹ * (volume (euclideanBall (0 : Vec d) (1 / 2)))⁻¹ *
          ((∫⁻ x in (euclideanBall (0 : Vec d) (1 / 2)), ENNReal.ofReal (u.toFun x ^ γ)) *
            ∫⁻ x in (euclideanBall (0 : Vec d) (1 / 2)), ENNReal.ofReal (u.toFun x ^ (-γ))) := by ring
    _ ≤ (volume (euclideanBall (0 : Vec d) (1 / 2)))⁻¹ * (volume (euclideanBall (0 : Vec d) (1 / 2)))⁻¹ * (ENNReal.ofReal ((1 + CJ) ^ 2) * volume (euclideanBall (0 : Vec d) (1 / 2)) ^ 2) := by
        gcongr
    _ = ENNReal.ofReal ((1 + CJ) ^ 2) * ((volume (euclideanBall (0 : Vec d) (1 / 2)))⁻¹ * volume (euclideanBall (0 : Vec d) (1 / 2))) ^ 2 := by ring
    _ = ENNReal.ofReal ((1 + CJ) ^ 2) := by rw [hV]; simp

end PDE.DGNMLog
