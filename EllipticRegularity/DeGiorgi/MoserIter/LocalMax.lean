module

public import EllipticRegularity.DeGiorgi.MoserIter.Iterate
public import EllipticRegularity.DeGiorgi.MoserIter.AddConst
public import EllipticRegularity.DeGiorgi.MoserIter.DeltaLimit

/-!
# Moser's `L^∞` estimate for subsolutions from the one-step estimate

The `δ`-regularisation `(u₊ + δ)` of Step 0 of Proposition 4.13, the Moser
iteration, and the limit `δ → 0`, given the one-step estimate (H1), local boundedness (H0a)
and the subsolution property of the positive part (H0b).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE.DGNMMoser

/-- The value of the constant of the Moser iteration, raised to the power `p`. -/
theorem moser_constant_pow {d : ℕ} {c Λ q p : ℝ} (hc : 0 < c) (hΛ : 0 < Λ) (hq : 0 < q)
    (hp : 0 < p) :
    ((128 * c * Λ * q ^ 2) ^ ((d : ℝ) / 2 / p) * (4 : ℝ) ^ (((d : ℝ) * (d - 2) / 4) / p)) ^ p =
      (128 * c) ^ ((d : ℝ) / 2) * (4 : ℝ) ^ ((d : ℝ) * (d - 2) / 4) *
        Λ ^ ((d : ℝ) / 2) * q ^ (d : ℝ) := by
  have h1 : (0 : ℝ) ≤ 128 * c * Λ * q ^ 2 := by positivity
  rw [Real.mul_rpow (Real.rpow_nonneg h1 _) (Real.rpow_nonneg (by norm_num) _),
    ← Real.rpow_mul h1, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4),
    div_mul_cancel₀ _ hp.ne', div_mul_cancel₀ _ hp.ne']
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity)
    (by positivity), ← Real.rpow_natCast q 2, ← Real.rpow_mul hq.le]
  have h2 : ((2 : ℕ) : ℝ) * ((d : ℝ) / 2) = (d : ℝ) := by push_cast; ring
  rw [h2]
  ring

theorem exists_moserLocalMax_constant_full (d : ℕ) (hd : 3 ≤ d)
    (hOne : MoserOneStepHyp d) (hBdd : SubsolutionBoundedHyp d)
    (hPos : PositivePartSubsolutionHyp d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSubharmonicOn a (euclideanBall (0 : Vec d) 1) u →
      ∀ p : ℝ, 1 < p →
        (essSup (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ p ≤
          ENNReal.ofReal (C * Λ ^ ((d : ℝ) / 2) * (p / (p - 1)) ^ (d : ℝ)) *
            (eLpNorm u.toFun (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1))) ^ p := by
  obtain ⟨C₁, hC₁, hstep⟩ := hOne
  set c₁ : ℝ := max C₁ 1 with hc₁def
  have hc₁ : 1 ≤ c₁ := le_max_right _ _
  have hc₀ : 0 < c₁ := by linarith
  refine ⟨(128 * c₁) ^ ((d : ℝ) / 2) * (4 : ℝ) ^ ((d : ℝ) * (d - 2) / 4), by positivity, ?_⟩
  intro Λ a hm hell u hsub p hp
  have hΛ : 1 ≤ Λ := (hell 0 (center_mem_euclideanBall 0 one_pos)).lam_le_Lam
  have hΛ0 : 0 < Λ := by linarith
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hq0 : 0 < p / (p - 1) := by positivity
  have hB := isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) (R := 1) one_pos
  have hfin := isFiniteMeasure_volumeOn_ball d (r := 1) one_pos
  set μ : Measure (Vec d) := volumeOn (euclideanBall (0 : Vec d) 1) with hμ
  set E : ℝ≥0∞ := eLpNorm u.toFun (ENNReal.ofReal p) μ with hE
  set Kp : ℝ := (128 * c₁ * Λ * (p / (p - 1)) ^ 2) ^ ((d : ℝ) / 2 / p) *
    (4 : ℝ) ^ (((d : ℝ) * (d - 2) / 4) / p) with hKp
  set W : ℝ≥0∞ := μ Set.univ ^ (1 / p) with hW
  have hWtop : W ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top _ _)
  have key : ∀ δ : ℝ, 0 < δ → essSup (fun x => ENNReal.ofReal (u.toFun x))
      (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
        ENNReal.ofReal Kp * (E + ENNReal.ofReal δ * W) := by
    intro δ hδ
    set pp := u.positivePartSubConst hB 0 with hpp
    set v : H1Function (euclideanBall (0 : Vec d) 1) := pp.addConst δ with hvdef
    have hv : ∀ x, v.toFun x = max (u.toFun x - 0) 0 + δ := fun x => rfl
    have hvsub : IsWeakDivergenceFormSubharmonicOn a (euclideanBall (0 : Vec d) 1) v :=
      subharmonic_addConst (hPos Λ a hm hell u hsub) δ
    obtain ⟨M, hM⟩ := hBdd Λ a hm hell v hvsub
    have hδv : ∀ᵐ x ∂μ, δ ≤ v.toFun x :=
      Filter.Eventually.of_forall fun x => by
        rw [hv]; have := le_max_right (u.toFun x - 0) 0; linarith
    have hstep' : ∀ p' : ℝ, 1 < p' → ∀ r s : ℝ, 1 / 2 ≤ r → r < s → s ≤ 3 / 4 →
        eLpNorm v.toFun (ENNReal.ofReal (p' * ((d : ℝ) / (d - 2))))
            (volumeOn (euclideanBall (0 : Vec d) r)) ≤
          ENNReal.ofReal ((c₁ / (s - r) ^ 2 * (Λ * p' ^ 2 / (p' - 1) ^ 2 + 1)) ^ (1 / p')) *
            eLpNorm v.toFun (ENNReal.ofReal p') (volumeOn (euclideanBall (0 : Vec d) s)) := by
      intro p' hp' r s h1 h2 h3
      refine (hstep Λ a hm hell v hvsub δ M hδ hδv hM p' hp' r s h1 h2 h3).trans ?_
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by
        have : 0 < p' - 1 := by linarith
        positivity) ?_ (by have : 0 < p' := by linarith
                           positivity))) le_rfl
      have : 0 < p' - 1 := by linarith
      have hsr : 0 < s - r := by linarith
      have hX : 0 ≤ Λ * p' ^ 2 / (p' - 1) ^ 2 + 1 := by positivity
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_max_left _ _)
        (by positivity)) hX
    have hmeas : AEMeasurable v.toFun (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) :=
      v.memL2.aestronglyMeasurable.aemeasurable.mono_measure
        (Measure.restrict_mono (euclideanBall_mono (by norm_num) (by norm_num)) le_rfl)
    have hit := moser_iteration hd v.toFun hmeas hc₁ hΛ hstep' hp
    have hess : essSup (fun x => ENNReal.ofReal (u.toFun x))
        (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
        essSup (fun x => ENNReal.ofReal (v.toFun x))
        (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) :=
      essSup_mono_ae (Filter.Eventually.of_forall fun x => by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hv]; have := le_max_left (u.toFun x - 0) 0; linarith)
    have hnorm : eLpNorm v.toFun (ENNReal.ofReal p)
        (volumeOn (euclideanBall (0 : Vec d) (3 / 4))) ≤ E + ENNReal.ofReal δ * W := by
      refine (eLpNorm_ball_mono v.toFun _ (by norm_num) (by norm_num : (3 / 4 : ℝ) ≤ 1)).trans ?_
      have hsplit : v.toFun = (fun x => max (u.toFun x - 0) 0) + fun _ => δ := rfl
      have hp1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
      rw [hsplit]
      refine (eLpNorm_add_le hp1').trans (add_le_add ?_ ?_)
      · refine eLpNorm_mono pp.memL2.aestronglyMeasurable fun x => ?_
        simp only [Real.norm_eq_abs, sub_zero]
        rcases le_total (u.toFun x) 0 with h | h
        · simp [max_eq_right h]
        · simp [max_eq_left h]
      · have hne : (volumeOn (euclideanBall (0 : Vec d) 1)) ≠ 0 := by
          intro h0
          have := (isOpen_euclideanBall (0 : Vec d) 1).measure_pos volume
            ⟨0, center_mem_euclideanBall 0 one_pos⟩
          have h00 := congrArg (fun m : Measure (Vec d) => m Set.univ) h0
          simp only [volumeOn, Measure.restrict_apply_univ, Measure.coe_zero,
            Pi.zero_apply] at h00
          exact this.ne' h00
        rw [eLpNorm_const _ (by simpa using hp0) hne, ENNReal.toReal_ofReal hp0.le,
          Real.enorm_eq_ofReal hδ.le]
    exact hess.trans (hit.trans (mul_le_mul' le_rfl hnorm))
  have hmain := le_mul_of_forall_delta hWtop key
  have hKp0 : 0 ≤ Kp := by positivity
  calc (essSup (fun x => ENNReal.ofReal (u.toFun x))
        (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ p
      ≤ (ENNReal.ofReal Kp * E) ^ p := ENNReal.rpow_le_rpow hmain hp0.le
    _ = ENNReal.ofReal (Kp ^ p) * E ^ p := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.ofReal_rpow_of_nonneg hKp0 hp0.le]
    _ = _ := by
        rw [hKp, moser_constant_pow hc₀ hΛ0 hq0 hp0]

end PDE.DGNMMoser
