module

public import EllipticRegularity.DeGiorgi.LogPackage.SmallSupportL2
public import EllipticRegularity.DeGiorgi.LogPackage.ZeroSet
public import EllipticRegularity.DeGiorgi.LogPackage.BallCover
public import EllipticRegularity.DeGiorgi.LogPackage.ExpansionGeom
public import EllipticRegularity.DeGiorgi.LogPackage.Shift
public import EllipticRegularity.DeGiorgi.LogPackage.Defs

/-!
# Expansion of positivity from the logarithmic energy estimate and the local maximum principle

Manuscript: Proposition 4.11.  The PDE inputs are the explicit hypotheses `PosPartLogEnergyHyp d`
and `LocMaxBallHyp d`; the remainder (Poincare on the set of positive density, Sobolev-Poincare,
Holder, covering, the limit `δ → 0`) is proved here.
-/

@[expose] public section

namespace PDE.DGNMLog

open MeasureTheory

/-- Expansion of positivity (Proposition 4.11), with the two PDE inputs taken as
explicit hypotheses. -/
theorem exists_expansionOfPositivity_constant_full (d : ℕ) (hd : 3 ≤ d)
    (hPosPart : PosPartLogEnergyHyp d) (hLocMax : LocMaxBallHyp d) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 → ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) u →
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 ≤ u.toFun x) →
      ENNReal.ofReal (1 - θ) * volume (euclideanBall (0 : Vec d) 1) ≤
        volume {x ∈ euclideanBall (0 : Vec d) 1 | 1 ≤ u.toFun x} →
        ENNReal.ofReal (Real.exp (-(C * θ ^ ((1 : ℝ) / d) * Λ ^ (((d : ℝ) + 2) / 4)))) ≤
          essInf (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) := by
  obtain ⟨CL, hCL, hLoc⟩ := hLocMax
  obtain ⟨K, hK, hSS⟩ := smallSupport_sq_le hd
  have hd1 : 1 ≤ d := by omega
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set ρ := expRho d with hρdef
  have hρpos : 0 < ρ := expRho_pos d
  have hρ1 : ρ < 1 := expRho_lt_one hd1
  have hρ34 : 3 / 4 ≤ ρ := three_quarters_le_expRho hd1
  have hB1fin : volume (euclideanBall (0 : Vec d) 1) < ⊤ :=
    (volume_euclideanBall_ne_top _ zero_le_one).lt_top
  have hB1pos : 0 < (volume (euclideanBall (0 : Vec d) 1)).toReal :=
    volume_euclideanBall_toReal_pos _ one_pos
  set E₀ : ℝ := 16 * (volume (euclideanBall (0 : Vec d) 1)).toReal / (1 - ρ) ^ 2 with hE₀
  have hE₀pos : 0 < E₀ := by
    have : 0 < 1 - ρ := by linarith
    positivity
  set K₃ : ℝ := K * (4 / 3 : ℝ) ^ ((1 : ℝ) / d) * Real.sqrt E₀ with hK₃
  have hK₃pos : 0 < K₃ := by positivity
  refine ⟨CL * K₃, by positivity, ?_⟩
  intro θ hθ hθ2 Λ a hmeas hell u hsuper hnonneg hdens
  have hΛ1 : 1 ≤ Λ := (hell 0 (center_mem_euclideanBall 0 one_pos)).2.1
  have hΛpos : 0 < Λ := by linarith
  set S : ℝ := CL * K₃ * θ ^ ((1 : ℝ) / d) * Λ ^ (((d : ℝ) + 2) / 4) with hS
  have hS0 : 0 ≤ S := by positivity
  have hB1meas : MeasurableSet (euclideanBall (0 : Vec d) 1) := measurableSet_euclideanBall _ _
  have hfin : IsFiniteMeasure (volumeOn (euclideanBall (0 : Vec d) 1)) :=
    isFiniteMeasure_volumeOn_euclideanBall _ zero_le_one
  set V := euclideanBall (0 : Vec d) ρ with hV
  have hVsub : V ⊆ euclideanBall (0 : Vec d) 1 := euclideanBall_mono hρpos.le hρ1.le
  have hVmeas : MeasurableSet V := measurableSet_euclideanBall _ _
  have hSpos : (0 : ℝ) ≤ K₃ * θ ^ ((1 : ℝ) / d) * Real.sqrt Λ := by positivity
  have hshift : ∀ n : ℕ, ∀ᵐ z ∂(volumeOn (euclideanBall (0 : Vec d) (1 / 2))),
      Real.exp (-S) ≤ u.toFun z + 1 / ((n : ℝ) + 1) := by
    intro n
    set δ : ℝ := 1 / ((n : ℝ) + 1) with hδdef
    have hδ : 0 < δ := by positivity
    set un := u.addConst δ with hun
    have hunlow : ∃ δ' : ℝ, 0 < δ' ∧
        ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), δ' ≤ un.toFun x := by
      refine ⟨δ, hδ, ?_⟩
      filter_upwards [hnonneg] with x hx
      simp only [hun, H1Function.addConst_apply]
      linarith [hx]
    obtain ⟨w, hwlog, hwsub, hwE⟩ :=
      hPosPart Λ a hmeas hell un hunlow (superharmonic_addConst hsuper δ)
    have hw' : ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)),
        w.toFun x = max (-Real.log (u.toFun x + δ)) 0 := by
      filter_upwards [hwlog] with x hx
      simpa only [hun, H1Function.addConst_apply] using hx
    obtain ⟨t, htmeas, htzero, htmeasure⟩ := exists_measurable_zero_set hB1meas hB1fin
      u.memL2.aestronglyMeasurable hθ.le (by linarith) hδ hdens hw'
    have htV : volume (t ∩ V) ≤ ENNReal.ofReal ((4 / 3) * θ) * volume V := by
      calc volume (t ∩ V) ≤ volume (t ∩ euclideanBall (0 : Vec d) 1) :=
            measure_mono (Set.inter_subset_inter_right _ hVsub)
        _ ≤ ENNReal.ofReal θ * volume (euclideanBall (0 : Vec d) 1) := htmeasure
        _ = ENNReal.ofReal ((4 / 3) * θ) * volume V := by
            rw [hV, hρdef, volume_expRho_ball hd1, ← mul_assoc,
              ← ENNReal.ofReal_mul (by positivity)]
            congr 2; ring
    have hI := hSS hρpos hρ1.le (a := (4 / 3) * θ) (by positivity) (by linarith) w t htmeas
      (fun x hx hxt => htzero x (hVsub hx) hxt) htV
    -- energy bound
    have hs1 : ρ < (1 + ρ) / 2 := by linarith
    have hEn := hwE 0 ρ ((1 + ρ) / 2) hρpos hs1 (by
      have : vecEuclideanNorm (0 : Vec d) = 0 := by
        unfold vecEuclideanNorm; simp [vecNormSq, vecDot]
      rw [this]; linarith)
    have hEn' : ∫ x in V, vecNormSq (w.grad x) ≤ E₀ * Λ := by
      refine hEn.trans ?_
      have hvol : (volume (euclideanBall (0 : Vec d) ((1 + ρ) / 2))).toReal ≤
          (volume (euclideanBall (0 : Vec d) 1)).toReal :=
        ENNReal.toReal_mono hB1fin.ne
          (measure_mono (euclideanBall_mono (by linarith) (by linarith)))
      have hden : ((1 + ρ) / 2 - ρ) ^ 2 = (1 - ρ) ^ 2 / 4 := by ring
      rw [hden, hE₀]
      have h1ρ : 0 < 1 - ρ := by linarith
      rw [show 4 * Λ * (volume (euclideanBall (0 : Vec d) ((1 + ρ) / 2))).toReal /
          ((1 - ρ) ^ 2 / 4) = 16 * Λ * (volume (euclideanBall (0 : Vec d) ((1 + ρ) / 2))).toReal /
          (1 - ρ) ^ 2 by field_simp; ring]
      rw [show 16 * (volume (euclideanBall (0 : Vec d) 1)).toReal / (1 - ρ) ^ 2 * Λ =
          16 * Λ * (volume (euclideanBall (0 : Vec d) 1)).toReal / (1 - ρ) ^ 2 by ring]
      gcongr
    -- the L² bound on B_ρ
    have hνmono : volumeOn V ≤ volumeOn (euclideanBall (0 : Vec d) 1) :=
      Measure.restrict_mono hVsub le_rfl
    have hwL2 : MemLp w.toFun 2 (volumeOn V) := w.memL2.mono_measure hνmono
    have hIsq : (eLpNorm w.toFun 2 (volumeOn V)).toReal ^ 2 = ∫ x in V, w.toFun x ^ 2 := by
      simpa only [volumeOn] using toReal_eLpNorm_two_sq_eq_integral_sq hwL2
    have hXsq : ∫ x in V, w.toFun x ^ 2 ≤
        (K₃ * θ ^ ((1 : ℝ) / d) * Real.sqrt Λ) ^ 2 := by
      have hpow : ((4 / 3 : ℝ) * θ) ^ (2 / (d : ℝ)) =
          ((4 / 3 : ℝ) ^ ((1 : ℝ) / d) * θ ^ ((1 : ℝ) / d)) ^ 2 := by
        rw [Real.mul_rpow (by norm_num) hθ.le, mul_pow, ← Real.rpow_natCast,
          ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul hθ.le]
        congr 2 <;> · push_cast; ring
      calc ∫ x in V, w.toFun x ^ 2
          ≤ K ^ 2 * ((4 / 3) * θ) ^ (2 / (d : ℝ)) * ∫ x in V, vecNormSq (w.grad x) := hI
        _ ≤ K ^ 2 * ((4 / 3) * θ) ^ (2 / (d : ℝ)) * (E₀ * Λ) := by gcongr
        _ = (K₃ * θ ^ ((1 : ℝ) / d) * Real.sqrt Λ) ^ 2 := by
            rw [hpow, hK₃, mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hE₀pos.le,
              Real.sq_sqrt hΛpos.le]
            ring
    have hNorm : eLpNorm w.toFun 2 (volumeOn V) ≤
        ENNReal.ofReal (K₃ * θ ^ ((1 : ℝ) / d) * Real.sqrt Λ) := by
      rw [ENNReal.le_ofReal_iff_toReal_le hwL2.eLpNorm_ne_top hSpos]
      refine le_of_sq_le_sq ?_ hSpos
      rw [hIsq]; exact hXsq
    -- local maximum principle
    have hloc : ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2),
        ∀ᵐ z ∂(volumeOn (euclideanBall x (1 / 8))), w.toFun z ≤ S := by
      intro x hx
      have hxn : vecEuclideanNorm x < 1 / 2 := by
        have := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hx
        simpa using this
      have h := hLoc Λ a hmeas hell w hwsub x (by linarith)
      have hsub2 : euclideanBall x (1 / 4) ⊆ V :=
        euclideanBall_subset_of_center_norm_add_le (c := (0 : Vec d)) (by norm_num) hρpos
          (by simpa using (by linarith : vecEuclideanNorm x + 1 / 4 ≤ ρ))
      have hL2 : eLpNorm w.toFun 2 (volumeOn (euclideanBall x (1 / 4))) ≤
          ENNReal.ofReal (K₃ * θ ^ ((1 : ℝ) / d) * Real.sqrt Λ) :=
        (eLpNorm_mono_measure _ (Measure.restrict_mono hsub2 le_rfl)).trans hNorm
      have hess : essSup (fun z => ENNReal.ofReal (w.toFun z))
          (volumeOn (euclideanBall x (1 / 8))) ≤ ENNReal.ofReal S := by
        refine h.trans ?_
        calc ENNReal.ofReal (CL * Λ ^ ((d : ℝ) / 4)) *
              eLpNorm w.toFun 2 (volumeOn (euclideanBall x (1 / 4)))
            ≤ ENNReal.ofReal (CL * Λ ^ ((d : ℝ) / 4)) *
                ENNReal.ofReal (K₃ * θ ^ ((1 : ℝ) / d) * Real.sqrt Λ) := by gcongr
          _ = ENNReal.ofReal S := by
              rw [← ENNReal.ofReal_mul (by positivity)]
              congr 1
              have hexp : ((d : ℝ) + 2) / 4 = (d : ℝ) / 4 + 1 / 2 := by ring
              rw [hS, hexp, Real.rpow_add hΛpos, Real.sqrt_eq_rpow]
              ring
      filter_upwards [ENNReal.ae_le_essSup (fun z => ENNReal.ofReal (w.toFun z))
        (μ := volumeOn (euclideanBall x (1 / 8)))] with z hz
      exact (ENNReal.ofReal_le_ofReal_iff hS0).mp (hz.trans hess)
    have hwS := ae_le_of_local_ball_bound hloc
    have hBsub : euclideanBall (0 : Vec d) (1 / 2) ⊆ euclideanBall (0 : Vec d) 1 :=
      euclideanBall_mono (by norm_num) (by norm_num)
    have h1 := ae_restrict_of_ae_restrict_of_subset hBsub hw'
    have h2 := ae_restrict_of_ae_restrict_of_subset hBsub hnonneg
    filter_upwards [hwS, h1, h2] with z hz1 hz2 hz3
    have hpos : 0 < u.toFun z + δ := by linarith
    rw [hz2] at hz1
    have : -Real.log (u.toFun z + δ) ≤ S := (le_max_left _ _).trans hz1
    exact (Real.le_log_iff_exp_le hpos).mp (by linarith)
  have hall : ∀ᵐ z ∂(volumeOn (euclideanBall (0 : Vec d) (1 / 2))),
      ∀ n : ℕ, Real.exp (-S) ≤ u.toFun z + 1 / ((n : ℝ) + 1) := ae_all_iff.mpr hshift
  refine le_essInf_of_ae_le _ ?_
  filter_upwards [hall] with z hz
  refine ENNReal.ofReal_le_ofReal ?_
  have h0 : Filter.Tendsto (fun n : ℕ => u.toFun z + 1 / ((n : ℝ) + 1)) Filter.atTop
      (nhds (u.toFun z + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
  rw [add_zero] at h0
  exact ge_of_tendsto' h0 hz

end PDE.DGNMLog
