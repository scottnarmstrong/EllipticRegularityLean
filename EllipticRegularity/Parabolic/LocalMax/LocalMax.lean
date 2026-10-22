module

public import EllipticRegularity.Parabolic.LocalMax.Iteration
public import EllipticRegularity.Parabolic.ParabolicDef
public import PDEFoundation.Measure.BallVolume

/-!
# Parabolic local maximum principle from the power step

Given the reverse-Hölder power step (`PowerStepProp`), Moser iteration bounds the essential
supremum on `B_{3/8} × (-11/16, -1/2)` by the `L^{(d+1)/d}` norm on `B_{1/2} × (-3/4, -1/2)`;
a Minkowski/`ε → 0` argument removes the shift and a volume normalisation gives the form of the
weak Harnack statement with `q = (d+1)/(d+2)`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.LocalMax

/-- The power-step property (the statement proved separately as `power_step`). -/
def PowerStepProp (d : ℕ) (C₀ : ℝ) : Prop :=
  ∀ (Lam : ℝ), 1 ≤ Lam → ∀ (a : ParCoeffField d),
    IsParabolicCoeff 1 Lam a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
    ∀ u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
    IsParabolicWeakSolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u →
    (∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)), 0 ≤ u.toFun z) →
    ∀ ε : ℝ, 0 < ε → ∀ p : ℝ, 1 < p → ∀ r ρ T T' tTop : ℝ, 0 < r → r < ρ → ρ ≤ 1 →
    -1 < T → T < T' → T' < tTop → tTop ≤ 0 →
    ∫⁻ z in euclideanBall (0 : Vec d) r ×ˢ Ioo T' tTop,
        ENNReal.ofReal (u.toFun z + ε) ^ (p * (((d : ℝ) + 2) / d)) ≤
      ENNReal.ofReal (C₀ * Lam * (2 + p / (p - 1)) ^ 2 * (1 / (ρ - r) ^ 2 + 1 / (T' - T))) ^
          (((d : ℝ) + 2) / d) *
        (∫⁻ z in euclideanBall (0 : Vec d) ρ ×ˢ Ioo T tTop,
          ENNReal.ofReal (u.toFun z + ε) ^ p) ^ (((d : ℝ) + 2) / d)

/-- Removing a small error term in `ℝ≥0∞`. -/
theorem le_of_forall_pos_le_add_mul {a b K : ℝ≥0∞} (hK : K ≠ ⊤)
    (h : ∀ ε : ℝ, 0 < ε → a ≤ b + ENNReal.ofReal ε * K) : a ≤ b := by
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  have hk : 0 ≤ K.toReal := ENNReal.toReal_nonneg
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  have h1 := h ((δ : ℝ) / (K.toReal + 1)) (by positivity)
  refine h1.trans (add_le_add le_rfl ?_)
  have : (δ : ℝ) / (K.toReal + 1) * K.toReal ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  calc ENNReal.ofReal ((δ : ℝ) / (K.toReal + 1)) * K
      = ENNReal.ofReal ((δ : ℝ) / (K.toReal + 1) * K.toReal) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hK]
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal this
    _ = δ := ENNReal.ofReal_coe_nnreal

/-- Scalar bound on the step constant. -/
theorem step_const_bound {d : ℕ} (hd : 0 < d) {C₀ Lam p : ℝ} (hC₀ : 0 < C₀) (hLam : 1 ≤ Lam)
    (hp : ((d : ℝ) + 1) / d ≤ p) :
    C₀ * Lam * (2 + p / (p - 1)) ^ 2 ≤ C₀ * Lam * ((d : ℝ) + 3) ^ 2 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hp1 : 1 < p := lt_of_lt_of_le (by rw [lt_div_iff₀ hd0]; linarith) hp
  have hpm : 0 < p - 1 := by linarith
  have h1 : p / (p - 1) ≤ (d : ℝ) + 1 := by
    rw [div_le_iff₀ hpm]
    have : ((d : ℝ) + 1) ≤ p * d := by rwa [div_le_iff₀ hd0] at hp
    nlinarith
  have h2 : 0 ≤ p / (p - 1) := by positivity
  have h3 : (2 + p / (p - 1)) ^ 2 ≤ ((d : ℝ) + 3) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have : 0 ≤ C₀ * Lam := by positivity
  exact mul_le_mul_of_nonneg_left h3 this

/-- Local maximum principle in `L^{(d+1)/d}` form. -/
theorem local_max_Lp (d : ℕ) (hd : 0 < d) {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hstep : PowerStepProp d C₀) (Lam : ℝ) (hLam : 1 ≤ Lam) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (a : ParCoeffField d),
      IsParabolicCoeff 1 Lam a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
      ∀ u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
      IsParabolicWeakSolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u →
      (∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
        0 ≤ u.toFun z) →
      essSup (fun z => ENNReal.ofReal (u.toFun z))
          (volume.restrict (moserCyl d (3 / 8) (-11 / 16))) ≤
        ENNReal.ofReal C₁ *
          (∫⁻ z in moserCyl d (1 / 2) (-3 / 4),
            ENNReal.ofReal (u.toFun z) ^ (((d : ℝ) + 1) / d)) ^ ((d : ℝ) / ((d : ℝ) + 1)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set A : ℝ := max 1 (C₀ * Lam * ((d : ℝ) + 3) ^ 2) with hA
  have hA1 : 1 ≤ A := le_max_left _ _
  obtain ⟨C₁, hC₁, hmoser⟩ := moser_iteration_essSup d hd A hA1
  refine ⟨C₁, hC₁, fun a ha u hu hu0 => ?_⟩
  set Q := moserCyl d (1 / 2) (-3 / 4) with hQ
  set p₀ : ℝ := ((d : ℝ) + 1) / d with hp₀
  have hp₀1 : 1 ≤ p₀ := by rw [hp₀, le_div_iff₀ hd0]; linarith
  have hexp : (d : ℝ) / ((d : ℝ) + 1) = 1 / p₀ := by rw [hp₀, one_div_div]
  rw [hexp]
  have hsub : Q ⊆ euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 := by
    intro z hz
    refine ⟨euclideanBall_mono (by norm_num) (by norm_num) hz.1, ?_⟩
    exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hmeas_u : AEMeasurable u.toFun (volume.restrict Q) :=
    (u.memL2.aestronglyMeasurable.mono_measure (Measure.restrict_mono hsub le_rfl)).aemeasurable
  have hVfin : volume Q ≠ ⊤ := volume_moserCyl_ne_top d (by norm_num) _
  have hChi : (0 : ℝ) < ((d : ℝ) + 2) / d := by positivity
  have hnn : ∀ᵐ z ∂(volume.restrict Q), 0 ≤ u.toFun z :=
    ae_restrict_of_ae_restrict_of_subset hsub hu0
  -- the bound for the shifted function
  have hshift : ∀ ε : ℝ, 0 < ε →
      essSup (fun z => ENNReal.ofReal (u.toFun z)) (volume.restrict (moserCyl d (3 / 8) (-11 / 16)))
        ≤ ENNReal.ofReal C₁ * (∫⁻ z in Q, ENNReal.ofReal (u.toFun z + ε) ^ p₀) ^ (1 / p₀) := by
    intro ε hε
    have hfm : AEMeasurable (fun z => u.toFun z + ε) (volume.restrict Q) := hmeas_u.add_const ε
    have hε' := hmoser (fun z => u.toFun z + ε) hfm (by
      intro p hp r ρ T T' hr hrρ hρ hT hTT' hT'
      have hp1 : 1 < p := lt_of_lt_of_le (by rw [hp₀]; rw [lt_div_iff₀ hd0]; linarith) hp
      have key := hstep Lam hLam a ha u hu hu0 ε hε p hp1 r ρ T T' (-1 / 2) (by linarith)
        hrρ (by linarith) (by linarith) hTT' (by linarith) (by norm_num)
      refine key.trans ?_
      have hS : 0 ≤ 1 / (ρ - r) ^ 2 + 1 / (T' - T) := by
        have : 0 < ρ - r := by linarith
        have : 0 < T' - T := by linarith
        positivity
      have hc : C₀ * Lam * (2 + p / (p - 1)) ^ 2 ≤ A :=
        (step_const_bound hd hC₀ hLam hp).trans (le_max_right _ _)
      exact mul_le_mul' (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hc hS)) hChi.le) le_rfl)
    rw [hexp] at hε'
    refine le_trans (essSup_mono_ae (f := fun z => ENNReal.ofReal (u.toFun z))
      (g := fun z => ENNReal.ofReal (u.toFun z + ε))
      (Filter.Eventually.of_forall fun z => ?_)) hε'
    exact ENNReal.ofReal_le_ofReal (by linarith)
  -- Minkowski
  have hmink : ∀ ε : ℝ, 0 < ε →
      (∫⁻ z in Q, ENNReal.ofReal (u.toFun z + ε) ^ p₀) ^ (1 / p₀) ≤
        (∫⁻ z in Q, ENNReal.ofReal (u.toFun z) ^ p₀) ^ (1 / p₀) +
          ENNReal.ofReal ε * volume Q ^ (1 / p₀) := by
    intro ε hε
    have hp0pos : 0 < p₀ := by linarith
    have hm := ENNReal.lintegral_Lp_add_le (μ := volume.restrict Q)
      (f := fun z => ENNReal.ofReal (u.toFun z)) (g := fun _ => ENNReal.ofReal ε)
      hmeas_u.ennreal_ofReal aemeasurable_const hp₀1
    have hconst : (∫⁻ _ in Q, ENNReal.ofReal ε ^ p₀) ^ (1 / p₀) =
        ENNReal.ofReal ε * volume Q ^ (1 / p₀) := by
      rw [lintegral_const, Measure.restrict_apply_univ,
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
      congr 2
      field_simp
      simp
    refine le_trans (ENNReal.rpow_le_rpow ?_ (by positivity)) (hm.trans (le_of_eq ?_))
    · refine lintegral_mono fun z => ENNReal.rpow_le_rpow ?_ hp0pos.le
      simpa using ENNReal.ofReal_add_le (p := u.toFun z) (q := ε)
    · rw [← hconst]
  have hK : ENNReal.ofReal C₁ * volume Q ^ (1 / p₀) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hVfin)
  refine le_of_forall_pos_le_add_mul hK fun ε hε => ?_
  refine (hshift ε hε).trans ?_
  calc ENNReal.ofReal C₁ * (∫⁻ z in Q, ENNReal.ofReal (u.toFun z + ε) ^ p₀) ^ (1 / p₀)
      ≤ ENNReal.ofReal C₁ * ((∫⁻ z in Q, ENNReal.ofReal (u.toFun z) ^ p₀) ^ (1 / p₀) +
          ENNReal.ofReal ε * volume Q ^ (1 / p₀)) := by gcongr; exact hmink ε hε
    _ = _ := by ring

/-- The parabolic local maximum principle, assuming the power step. -/
theorem parabolic_local_max_of_powerStep (d : ℕ) (hd : 0 < d) {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hstep : PowerStepProp d C₀) (Lam : ℝ) (hLam : 1 ≤ Lam) (q : ℝ)
    (hq : q = ((d : ℝ) + 1) / ((d : ℝ) + 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ParCoeffField d),
      IsParabolicCoeff 1 Lam a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
      ∀ u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
      IsParabolicWeakSolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u →
      (∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)), 0 ≤ u.toFun z) →
      essSup (fun z => ENNReal.ofReal (u.toFun z))
          (volume.restrict (euclideanBall (0 : Vec d) (3 / 8) ×ˢ Ioo (-11 / 16 : ℝ) (-1 / 2))) ≤
        ENNReal.ofReal C *
          ((volume (euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioo (-3 / 4 : ℝ) (-1 / 2)))⁻¹ *
            ∫⁻ z in euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioo (-3 / 4 : ℝ) (-1 / 2),
              ENNReal.ofReal (u.toFun z) ^ (q * ((d : ℝ) + 2) / d)) ^
            (1 / (q * ((d : ℝ) + 2) / d)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨C₁, hC₁, hmain⟩ := local_max_Lp d hd hC₀ hstep Lam hLam
  have hexp : q * ((d : ℝ) + 2) / d = ((d : ℝ) + 1) / d := by
    rw [hq]; field_simp
  have hp₀ : (0 : ℝ) < ((d : ℝ) + 1) / d := by positivity
  have hQpos : 0 < volume (moserCyl d (1 / 2) (-3 / 4)) := by
    unfold moserCyl
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    refine ENNReal.mul_pos (volume_euclideanBall_pos _ (by norm_num)).ne' ?_
    simp; norm_num
  have hQfin := volume_moserCyl_ne_top d (r := 1 / 2) (by norm_num) (-3 / 4)
  set V := volume (moserCyl d (1 / 2) (-3 / 4)) with hV
  have hVr : 0 < V.toReal := ENNReal.toReal_pos hQpos.ne' hQfin
  refine ⟨C₁ * V.toReal ^ (((d : ℝ) + 1) / d)⁻¹, mul_pos hC₁ (Real.rpow_pos_of_pos hVr _), ?_⟩
  intro a ha u hu hu0
  rw [hexp, one_div_div]
  refine (hmain a ha u hu hu0).trans (le_of_eq ?_)
  show _ = _
  have hI : ∀ I : ℝ≥0∞, I ^ (d / ((d : ℝ) + 1)) =
      V ^ (d / ((d : ℝ) + 1)) * (V⁻¹ * I) ^ (d / ((d : ℝ) + 1)) := by
    intro I
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← mul_assoc,
      ENNReal.mul_inv_cancel hQpos.ne' hQfin, one_mul]
  have hVc : V ^ ((d : ℝ) / ((d : ℝ) + 1)) = ENNReal.ofReal (V.toReal ^ (((d : ℝ) + 1) / d)⁻¹) := by
    calc V ^ ((d : ℝ) / ((d : ℝ) + 1)) = (ENNReal.ofReal V.toReal) ^ ((d : ℝ) / ((d : ℝ) + 1)) := by
          rw [ENNReal.ofReal_toReal hQfin]
      _ = _ := by rw [ENNReal.ofReal_rpow_of_pos hVr, inv_div]
  rw [hI, hVc, ENNReal.ofReal_mul hC₁.le, mul_assoc]
  rfl

end PDE.Parabolic.LocalMax
