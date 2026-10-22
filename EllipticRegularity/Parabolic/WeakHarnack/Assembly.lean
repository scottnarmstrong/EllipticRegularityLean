module

public import EllipticRegularity.Parabolic.WeakHarnack.AssemblyNeg
public import EllipticRegularity.Parabolic.WeakHarnack.AssemblyMeasurable
public import EllipticRegularity.Parabolic.WeakHarnack.MeasuresConvert

/-!
# Final assembly of the parabolic weak Harnack inequality (conditional on the analytic steps)

Manuscript Proposition 5.13: "Apply the Bombieri-Giusti
lemma to `e^{-k} v` ... multiplication proves ... let `ε ↓ 0`".

`weakHarnack_of_steps` has exactly the type of the statement `PDE.parabWeakHarnack`, with the
three analytic ingredients of the proof as hypotheses (each a theorem-type with its constants
quantified before `∀ a u ε`; `χ = 1 + 2/d`, `v = u + ε`):

* `H1step`, `H1fin` (manuscript (5.20), positive powers `0 < p ≤ q`): reverse Hölder step
  for `v` on `posCyl d σ` with respect to `cylMeasure (posCyl d 1)`, and finiteness of the
  `L^{qχ}` norm on `posCyl d 1`;
* `H2neg`, `H2inner` (negative powers `p > 0`): the step for `1/v` on `negCyl d σ`
  (resp. `negCylInner d σ`) with respect to `cylMeasure (negCyl d 1)` (resp. `cylMeasure
  (negCylInner d 1)`);
* `H3` (manuscript (5.21)): the hypotheses of `posNegCyl_log_tail` for `g = log v`.

Measurability of `u` is not assumed: a nonnegative measurable representative on `B₁ × (-1,0]` is
built from `ParH1Function.memL2` (`AssemblyMeasurable`) and all hypotheses are transferred to it.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.WeakHarnack

theorem weakHarnack_of_steps (d : ℕ) (hd : 0 < d) (Lam : ℝ) (_hLam : 1 ≤ Lam) (q : ℝ)
    (hq0 : 0 < q) (_hq1 : q < 1)
    (H1step : ∃ A m : ℝ, 1 ≤ A ∧ 0 < m ∧ ∀ (a : ParCoeffField d),
      IsParabolicCoeff 1 Lam a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
      ∀ u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
      IsParabolicWeakSupersolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u →
      (∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
        0 ≤ u.toFun z) →
      ∀ ε : ℝ, 0 < ε → ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p → p ≤ q →
        eLpNorm (fun z => u.toFun z + ε) (ENNReal.ofReal ((1 + 2 / (d : ℝ)) * p))
            ((cylMeasure (posCyl d 1)).restrict (posCyl d σ')) ≤
          ENNReal.ofReal ((A * (σ - σ') ^ (-m)) ^ (1 / p)) *
            eLpNorm (fun z => u.toFun z + ε) (ENNReal.ofReal p)
              ((cylMeasure (posCyl d 1)).restrict (posCyl d σ)))
    (H1fin : ∀ (a : ParCoeffField d),
      IsParabolicCoeff 1 Lam a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
      ∀ u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
      IsParabolicWeakSupersolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u →
      (∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
        0 ≤ u.toFun z) →
      ∀ ε : ℝ, 0 < ε →
        eLpNorm (fun z => u.toFun z + ε) (ENNReal.ofReal (q * (1 + 2 / (d : ℝ))))
          ((cylMeasure (posCyl d 1)).restrict (posCyl d 1)) < ⊤)
    (H2neg : ∃ A β m : ℝ, 1 ≤ A ∧ 0 ≤ β ∧ 0 < m ∧ ∀ (a : ParCoeffField d),
      IsParabolicCoeff 1 Lam a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
      ∀ u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
      IsParabolicWeakSupersolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u →
      (∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
        0 ≤ u.toFun z) →
      ∀ ε : ℝ, 0 < ε → ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
        eLpNorm (fun z => 1 / (u.toFun z + ε)) (ENNReal.ofReal ((1 + 2 / (d : ℝ)) * p))
            ((cylMeasure (negCyl d 1)).restrict (negCyl d σ')) ≤
          ENNReal.ofReal ((A * (1 + p) ^ β * (σ - σ') ^ (-m)) ^ (1 / p)) *
            eLpNorm (fun z => 1 / (u.toFun z + ε)) (ENNReal.ofReal p)
              ((cylMeasure (negCyl d 1)).restrict (negCyl d σ)))
    (H2inner : ∃ A β m : ℝ, 1 ≤ A ∧ 0 ≤ β ∧ 0 < m ∧ ∀ (a : ParCoeffField d),
      IsParabolicCoeff 1 Lam a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
      ∀ u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
      IsParabolicWeakSupersolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u →
      (∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
        0 ≤ u.toFun z) →
      ∀ ε : ℝ, 0 < ε → ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
        eLpNorm (fun z => 1 / (u.toFun z + ε)) (ENNReal.ofReal ((1 + 2 / (d : ℝ)) * p))
            ((cylMeasure (negCylInner d 1)).restrict (negCylInner d σ')) ≤
          ENNReal.ofReal ((A * (1 + p) ^ β * (σ - σ') ^ (-m)) ^ (1 / p)) *
            eLpNorm (fun z => 1 / (u.toFun z + ε)) (ENNReal.ofReal p)
              ((cylMeasure (negCylInner d 1)).restrict (negCylInner d σ)))
    (H3 : ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧ ∀ (a : ParCoeffField d),
      IsParabolicCoeff 1 Lam a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
      ∀ u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
      IsParabolicWeakSupersolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u →
      (∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
        0 ≤ u.toFun z) →
      ∀ ε : ℝ, 0 < ε → ∃ N : Set ℝ, volume N = 0 ∧
        (∀ t ∈ Icc (-7 / 8 : ℝ) 0, t ∉ N →
          MemLp (fun x => Real.log (u.toFun (x, t) + ε)) 2 (cutoffMeasure d)) ∧
        IntervalIntegrable
          (fun t => ∫ x, (Real.log (u.toFun (x, t) + ε) -
              ∫ y, Real.log (u.toFun (y, t) + ε) ∂(cutoffMeasure d)) ^ 2 ∂(cutoffMeasure d))
          volume (-7 / 8) 0 ∧
        (∀ t₁ ∈ Icc (-7 / 8 : ℝ) 0, ∀ t₂ ∈ Icc (-7 / 8 : ℝ) 0, t₁ ∉ N → t₂ ∉ N → t₁ < t₂ →
          ∫ τ in t₁..t₂, (c * ∫ x, (Real.log (u.toFun (x, τ) + ε) -
              ∫ y, Real.log (u.toFun (y, τ) + ε) ∂(cutoffMeasure d)) ^ 2
              ∂(cutoffMeasure d) - K) ≤
            (∫ x, Real.log (u.toFun (x, t₂) + ε) ∂(cutoffMeasure d)) -
              ∫ x, Real.log (u.toFun (x, t₁) + ε) ∂(cutoffMeasure d))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ParCoeffField d),
      IsParabolicCoeff 1 Lam a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
      ∀ u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
      IsParabolicWeakSupersolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u →
      (∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
        0 ≤ u.toFun z) →
        ((volume (euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioo (-3 / 4 : ℝ) (-1 / 2)))⁻¹ *
            ∫⁻ z in euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioo (-3 / 4 : ℝ) (-1 / 2),
              ENNReal.ofReal (u.toFun z) ^ (q * ((d : ℝ) + 2) / d)) ^ (1 / (q * ((d : ℝ) + 2) / d))
          ≤ ENNReal.ofReal C *
            essInf (fun z => ENNReal.ofReal (u.toFun z))
              (volume.restrict (euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioc (-1 / 4 : ℝ) 0)) := by
  obtain ⟨A₁, m₁, hA₁, hm₁, h1⟩ := H1step
  obtain ⟨A₂, β₂, m₂, hA₂, hβ₂, hm₂, h2⟩ := H2neg
  obtain ⟨A₃, β₃, m₃, hA₃, hβ₃, hm₃, h3⟩ := H2inner
  obtain ⟨c, K, hc, hK, hlogH⟩ := H3
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set χ : ℝ := 1 + 2 / (d : ℝ) with hχdef
  have hχ : 1 < χ := by rw [hχdef]; have : 0 < 2 / (d : ℝ) := by positivity
                        linarith
  have hr : q * ((d : ℝ) + 2) / d = q * χ := by rw [hχdef]; field_simp
  rw [hr]
  set D : ℝ := (cutoffMass d).toReal * (4 / c + 4 * K * (0 - (-7 / 8 : ℝ)) ^ 2) with hD
  set c₀ : ℝ := max (D / (volume (posCyl d 1)).toReal) (D / (volume (negCyl d 1)).toReal)
    with hc₀
  set C₁ : ℝ := PDE.Bombieri.giustiConst (1 / 2) (q * χ)
    (max c₀ (PDE.ParabIter.posC χ A₁ m₁ q)) (PDE.ParabIter.posM χ m₁ q) with hC₁
  set C₂ : ℝ := negTopConst d χ A₂ β₂ m₂ A₃ β₃ m₃ c₀ with hC₂
  have hC₁pos : 0 < C₁ := PDE.Bombieri.giustiConst_pos _ _ _ _
  have hC₂pos : 0 < C₂ := negTopConst_pos d hχ hA₃ hβ₃ hm₃
  have hqχ : 0 < q * χ := by positivity
  refine ⟨(posVolRatio d) ^ (1 / (q * χ)) * C₁ * C₂, by
    have := Real.rpow_pos_of_pos (posVolRatio_pos d) (1 / (q * χ))
    positivity, ?_⟩
  intro a ha u hu hu0
  obtain ⟨g, hgm, hg0, hae⟩ := exists_measurable_nonneg_rep
    (μ := volume.restrict (weakDomain d)) u.memL2.aestronglyMeasurable hu0
  have hsubPos : posCyl d 1 ⊆ weakDomain d := posCyl_subset (by norm_num) le_rfl
  have hsubNeg : negCyl d 1 ⊆ weakDomain d := negCyl_subset (by norm_num) le_rfl
  have hsubInn : negCylInner d 1 ⊆ weakDomain d := negCylInner_subset (by norm_num) le_rfl
  have hcore : ∀ ε : ℝ, 0 < ε → ∃ k : ℝ,
      eLpNorm (fun z => g z + ε) (ENNReal.ofReal (q * χ))
          ((cylMeasure (posCyl d 1)).restrict (posCyl d (1 / 2))) ≤
        ENNReal.ofReal (C₁ * Real.exp k) ∧
      eLpNorm (fun z => 1 / (g z + ε)) ⊤
          ((cylMeasure (negCyl d 1)).restrict (negCylInner d (1 / 2))) ≤
        ENNReal.ofReal (C₂ * Real.exp (-k)) := by
    intro ε hε
    have hvm : Measurable (fun z => g z + ε) := hgm.add_const ε
    have hvε : ∀ z, ε ≤ g z + ε := fun z => by linarith [hg0 z]
    have hvpos : ∀ z, 0 < g z + ε := fun z => hε.trans_le (hvε z)
    have hae' : (fun z => u.toFun z + ε) =ᵐ[volume.restrict (weakDomain d)] (fun z => g z + ε) :=
      hae.mono fun z hz => by simp only [hz]
    have hae'' : (fun z => 1 / (u.toFun z + ε)) =ᵐ[volume.restrict (weakDomain d)]
        (fun z => 1 / (g z + ε)) := hae.mono fun z hz => by simp only [hz]
    have hae3 : (fun z => Real.log (u.toFun z + ε)) =ᵐ[volume.restrict (weakDomain d)]
        (fun z => Real.log (g z + ε)) := hae.mono fun z hz => by simp only [hz]
    -- the logarithmic tail
    obtain ⟨N, hN, hL2, hV, hdiff⟩ := hlogH a ha u hu hu0 ε hε
    obtain ⟨N', hN', hL2', hV', hdiff'⟩ := transfer_logHyps hae3 hN hL2 hV hdiff
    obtain ⟨k, htail⟩ := posNegCyl_log_tail (g := fun z => Real.log (g z + ε))
      (Real.measurable_log.comp hvm) N' hc hK hN' hL2' hV' hdiff'
    obtain ⟨hlogp, hlogn⟩ := bombieri_hlog_of_log_tail (v := fun z => g z + ε) hvpos
      (D := D) htail (c₁ := c₀) (c₂ := c₀) (le_max_left _ _) (le_max_right _ _)
    refine ⟨k, ?_, ?_⟩
    · refine pos_side hχ hA₁ hm₁ hq0 hvm hvpos ?_ ?_ hlogp
      · rw [← eLpNorm_congr_ae (ae_cylMeasure_restrict hsubPos hae')]
        exact H1fin a ha u hu hu0 ε hε
      · intro σ' σ h1' h2' h3' p hp hpq
        have := h1 a ha u hu hu0 ε hε σ' σ h1' h2' h3' p hp hpq
        rwa [eLpNorm_congr_ae (ae_cylMeasure_restrict hsubPos hae'),
          eLpNorm_congr_ae (ae_cylMeasure_restrict hsubPos hae')] at this
    · refine neg_side hχ hA₂ hβ₂ hm₂ hA₃ hβ₃ hm₃ hε hvm hvε ?_ ?_ hlogn
      · intro σ' σ h1' h2' h3' p hp
        have := h2 a ha u hu hu0 ε hε σ' σ h1' h2' h3' p hp
        rwa [eLpNorm_congr_ae (ae_cylMeasure_restrict hsubNeg hae''),
          eLpNorm_congr_ae (ae_cylMeasure_restrict hsubNeg hae'')] at this
      · intro σ' σ h1' h2' h3' p hp
        have := h3 a ha u hu hu0 ε hε σ' σ h1' h2' h3' p hp
        rwa [eLpNorm_congr_ae (ae_cylMeasure_restrict hsubInn hae''),
          eLpNorm_congr_ae (ae_cylMeasure_restrict hsubInn hae'')] at this
  have key := weakHarnackAvg_le_essInf_of_eps hqχ hgm
    (Filter.Eventually.of_forall hg0) hC₁pos hC₂pos hcore
  -- transfer back to `u`
  have hQm : posCyl d (1 / 2) ⊆ weakDomain d :=
    (posCyl_mono (by norm_num) (by norm_num)).trans hsubPos
  have hQp : negCylInner d (1 / 2) ⊆ weakDomain d :=
    (negCylInner_mono (by norm_num) (by norm_num)).trans hsubInn
  have haeQm := ae_restrict_of_ae_restrict_of_subset hQm hae
  have haeQp := ae_restrict_of_ae_restrict_of_subset hQp hae
  rw [← negCylInner_half]
  have hcongr : weakHarnackAvg d (q * χ) u.toFun = weakHarnackAvg d (q * χ) g := by
    unfold weakHarnackAvg
    rw [← posCyl_half]
    congr 2
    refine lintegral_congr_ae ?_
    filter_upwards [haeQm] with z hz
    rw [hz]
  have hess : essInf (fun z => ENNReal.ofReal (u.toFun z))
      (volume.restrict (negCylInner d (1 / 2))) =
      essInf (fun z => ENNReal.ofReal (g z)) (volume.restrict (negCylInner d (1 / 2))) := by
    refine essInf_congr_ae ?_
    filter_upwards [haeQp] with z hz
    rw [hz]
  rw [hess]
  rw [← hcongr] at key
  exact key

end PDE.Parabolic.WeakHarnack
