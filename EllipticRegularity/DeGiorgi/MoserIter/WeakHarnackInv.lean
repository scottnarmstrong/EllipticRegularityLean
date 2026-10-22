module

public import EllipticRegularity.DeGiorgi.MoserIter.InvIterate
public import EllipticRegularity.DeGiorgi.MoserIter.AddConst
public import EllipticRegularity.DeGiorgi.MoserIter.DeltaLimit
public import EllipticRegularity.DeGiorgi.MoserIter.EssInf

/-!
# The first weak Harnack estimate (4.67)

Step 2 of the proof of Proposition 4.14: the `δ`-reduction `u ↦ u + δ`, the Moser iteration
for `u⁻¹` and the passage `p → ∞` giving `inf`, from the one-step estimate (H2a).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE.DGNMMoser

/-- The constant of the iteration, raised to the power `p`. -/
theorem inv_constant_pow {d : ℕ} {c Z γ p : ℝ} (hc : 0 < c) (hZ : 0 < Z) (hγ : 0 < γ)
    (hp : 0 < p) :
    ((16 * c * Z) ^ ((d : ℝ) / 2 / p) * (4 * γ ^ 2) ^ (((d : ℝ) * (d - 2) / 4) / p)) ^ p =
      (16 * c) ^ ((d : ℝ) / 2) * (4 * γ ^ 2) ^ ((d : ℝ) * (d - 2) / 4) * Z ^ ((d : ℝ) / 2) := by
  have h1 : (0 : ℝ) ≤ 16 * c * Z := by positivity
  have h2 : (0 : ℝ) ≤ 4 * γ ^ 2 := by positivity
  rw [Real.mul_rpow (Real.rpow_nonneg h1 _) (Real.rpow_nonneg h2 _),
    ← Real.rpow_mul h1, ← Real.rpow_mul h2, div_mul_cancel₀ _ hp.ne',
    div_mul_cancel₀ _ hp.ne', Real.mul_rpow (by positivity) hZ.le]
  ring

/-- Conversion between the `L^p` seminorm of `u⁻¹` and the lower integral. -/
theorem eLpNorm_inv_rpow {d : ℕ} {U : Set (Vec d)} {u : Vec d → ℝ}
    (hu : AEMeasurable u (volumeOn U)) (hpos : ∀ᵐ x ∂(volumeOn U), 0 < u x) {p : ℝ}
    (hp : 0 < p) :
    eLpNorm (fun x => (u x)⁻¹) (ENNReal.ofReal p) (volumeOn U) ^ p =
      ∫⁻ x in U, ENNReal.ofReal ((u x)⁻¹ ^ p) ∂volume := by
  have hne0 : ENNReal.ofReal p ≠ 0 := by simpa using hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hne0 ENNReal.ofReal_ne_top
    (f := fun x => (u x)⁻¹) hu.inv.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul,
    one_div_mul_cancel hp.ne', ENNReal.rpow_one]
  refine lintegral_congr_ae ?_
  filter_upwards [hpos] with x hx
  rw [Real.enorm_eq_ofReal (inv_nonneg.2 hx.le),
    ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 hx.le) hp.le]

theorem exists_weakHarnack0_inv_constant (d : ℕ) (hd : 3 ≤ d) (hInv : WeakHarnackInvOneStepHyp d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < u.toFun x) →
      IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) u →
      ∀ p : ℝ, 0 < p →
        ENNReal.ofReal ((Λ * p ^ 2 + 1) ^ (-((d : ℝ) / 2))) *
            (∫⁻ x in euclideanBall (0 : Vec d) 1, ENNReal.ofReal ((u.toFun x)⁻¹ ^ p) ∂volume)⁻¹ ≤
          ENNReal.ofReal C *
            (essInf (fun x => ENNReal.ofReal (u.toFun x))
              (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ p := by
  obtain ⟨C₁, hC₁, hstep⟩ := hInv
  set c₁ : ℝ := max C₁ 1 with hc₁def
  have hc₁ : 1 ≤ c₁ := le_max_right _ _
  have hc₀ : 0 < c₁ := by linarith
  have hγ : 1 < (d : ℝ) / (d - 2) := one_lt_gamma hd
  refine ⟨(16 * c₁) ^ ((d : ℝ) / 2) * (4 * ((d : ℝ) / (d - 2)) ^ 2) ^ ((d : ℝ) * (d - 2) / 4),
    by positivity, ?_⟩
  intro Λ a hm hell u hpos hsuper p hp
  have hΛ : 1 ≤ Λ := (hell 0 (center_mem_euclideanBall 0 one_pos)).lam_le_Lam
  have hΛ0 : 0 < Λ := by linarith
  have hZ0 : 0 < Λ * p ^ 2 + 1 := by positivity
  have hfin := isFiniteMeasure_volumeOn_ball d (r := 1) one_pos
  have hfin2 := isFiniteMeasure_volumeOn_ball d (r := 1 / 2) (by norm_num)
  set μ : Measure (Vec d) := volumeOn (euclideanBall (0 : Vec d) 1) with hμ
  set μh : Measure (Vec d) := volumeOn (euclideanBall (0 : Vec d) (1 / 2)) with hμh
  have hle : μh ≤ μ := Measure.restrict_mono (euclideanBall_mono (by norm_num) (by norm_num)) le_rfl
  set Z : ℝ := Λ * p ^ 2 + 1 with hZdef
  set Kv : ℝ := (16 * c₁ * Z) ^ ((d : ℝ) / 2 / p) *
    (4 * ((d : ℝ) / (d - 2)) ^ 2) ^ (((d : ℝ) * (d - 2) / 4) / p) with hKv
  have hKv0 : 0 < Kv := by positivity
  set L : ℝ≥0∞ := eLpNorm (fun x => (u.toFun x)⁻¹) (ENNReal.ofReal p) μ with hL
  set m : ℝ≥0∞ := essInf (fun x => ENNReal.ofReal (u.toFun x)) μh with hm_def
  have hu_meas : AEMeasurable u.toFun μ := u.memL2.aestronglyMeasurable.aemeasurable
  have key : ∀ δ : ℝ, 0 < δ → (ENNReal.ofReal Kv * L)⁻¹ ≤ m + ENNReal.ofReal δ := by
    intro δ hδ
    set v : H1Function (euclideanBall (0 : Vec d) 1) := u.addConst δ with hvdef
    have hv : ∀ x, v.toFun x = u.toFun x + δ := fun x => rfl
    have hvsuper : IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) v :=
      superharmonic_addConst hsuper δ
    have hδv : ∀ᵐ x ∂μ, δ ≤ v.toFun x := by
      filter_upwards [hpos] with x hx
      rw [hv]; linarith
    have hstep' : ∀ p' : ℝ, 0 < p' → ∀ r s : ℝ, 1 / 2 ≤ r → r < s → s ≤ 1 →
        eLpNorm (fun x => (v.toFun x)⁻¹) (ENNReal.ofReal (p' * ((d : ℝ) / (d - 2))))
            (volumeOn (euclideanBall (0 : Vec d) r)) ≤
          ENNReal.ofReal ((c₁ / (s - r) ^ 2 * (Λ * p' ^ 2 / (1 + p') ^ 2 + 1)) ^ (1 / p')) *
            eLpNorm (fun x => (v.toFun x)⁻¹) (ENNReal.ofReal p')
              (volumeOn (euclideanBall (0 : Vec d) s)) := by
      intro p' hp' r s h1 h2 h3
      refine (hstep Λ a hm hell v hvsuper δ hδ hδv p' hp' r s h1 h2 h3).trans ?_
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) ?_
        (by positivity))) le_rfl
      have hsr : 0 < s - r := by linarith
      have hX : 0 ≤ Λ * p' ^ 2 / (1 + p') ^ 2 + 1 := by positivity
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_max_left _ _)
        (by positivity)) hX
    have hv_meas : AEMeasurable v.toFun μ := v.memL2.aestronglyMeasurable.aemeasurable
    have hg_meas : AEMeasurable (fun x => (v.toFun x)⁻¹) μh :=
      hv_meas.inv.mono_measure hle
    have hit := inv_moser_iteration hd (fun x => (v.toFun x)⁻¹) hg_meas hc₁ hΛ0.le hstep'
      hp
    have hposh : ∀ᵐ x ∂μh, 0 < v.toFun x := by
      have : ∀ᵐ x ∂μ, 0 < v.toFun x := hδv.mono fun x hx => lt_of_lt_of_le hδ hx
      exact ae_mono hle this
    have h1 : (essInf (fun x => ENNReal.ofReal (v.toFun x)) μh)⁻¹ ≤
        essSup (fun x => ENNReal.ofReal ((v.toFun x)⁻¹)) μh := by
      refine (inv_essInf_le_essSup_inv _).trans (le_of_eq (essSup_congr_ae ?_))
      filter_upwards [hposh] with x hx
      rw [ENNReal.ofReal_inv_of_pos hx]
    have h2 : eLpNorm (fun x => (v.toFun x)⁻¹) (ENNReal.ofReal p) μ ≤ L := by
      refine eLpNorm_mono_ae hv_meas.inv.aestronglyMeasurable ?_
      filter_upwards [hpos] with x hx
      have hvx : 0 < v.toFun x := by rw [hv]; linarith
      rw [Real.norm_of_nonneg (inv_nonneg.2 hvx.le), Real.norm_of_nonneg (inv_nonneg.2 hx.le)]
      exact inv_anti₀ hx (by rw [hv]; linarith)
    have h3 : essInf (fun x => ENNReal.ofReal (v.toFun x)) μh ≤ m + ENNReal.ofReal δ := by
      refine (essInf_mono_ae (μ := μh) ?_).trans (essInf_add_const_le _ _)
      exact Filter.Eventually.of_forall fun x => by
        show ENNReal.ofReal (v.toFun x) ≤ ENNReal.ofReal (u.toFun x) + ENNReal.ofReal δ
        rw [hv]; exact ENNReal.ofReal_add_le
    have h4 : (m + ENNReal.ofReal δ)⁻¹ ≤ ENNReal.ofReal Kv * L :=
      (ENNReal.inv_le_inv.2 h3).trans (h1.trans (hit.trans (mul_le_mul' le_rfl h2)))
    exact ENNReal.inv_le_iff_inv_le.1 h4
  have hmain : (ENNReal.ofReal Kv * L)⁻¹ ≤ m := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε hb => ?_
    have := key (ε : ℝ) (by exact_mod_cast hε)
    simpa using this
  have hm' := ENNReal.rpow_le_rpow hmain hp.le
  have hLp : L ^ p = ∫⁻ x in euclideanBall (0 : Vec d) 1, ENNReal.ofReal ((u.toFun x)⁻¹ ^ p)
      ∂volume := eLpNorm_inv_rpow hu_meas hpos hp
  rw [ENNReal.inv_rpow, ENNReal.mul_rpow_of_nonneg _ _ hp.le,
    ENNReal.ofReal_rpow_of_nonneg hKv0.le hp.le, hLp] at hm'
  set J := ∫⁻ x in euclideanBall (0 : Vec d) 1, ENNReal.ofReal ((u.toFun x)⁻¹ ^ p) ∂volume
  refine le_trans ?_ (mul_le_mul' le_rfl hm')
  have hKp : Kv ^ p = (16 * c₁) ^ ((d : ℝ) / 2) *
      (4 * ((d : ℝ) / (d - 2)) ^ 2) ^ ((d : ℝ) * (d - 2) / 4) * Z ^ ((d : ℝ) / 2) :=
    inv_constant_pow hc₀ hZ0 (by linarith) hp
  have hKpos : 0 < Kv ^ p := Real.rpow_pos_of_pos hKv0 p
  rw [ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.2 hKpos).ne')
    (Or.inl ENNReal.ofReal_ne_top), ← mul_assoc, ← ENNReal.ofReal_inv_of_pos hKpos,
    ← ENNReal.ofReal_mul (by positivity)]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  rw [Real.rpow_neg hZ0.le, hKp]
  have hZp : 0 < Z ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos hZ0 _
  have hC : 0 < (16 * c₁) ^ ((d : ℝ) / 2) *
      (4 * ((d : ℝ) / (d - 2)) ^ 2) ^ ((d : ℝ) * (d - 2) / 4) := by positivity
  have hBp : (4 * ((d : ℝ) / (d - 2)) ^ 2) ^ ((d : ℝ) * (d - 2) / 4) ≠ 0 :=
    (Real.rpow_pos_of_pos (mul_pos (by norm_num) (pow_pos (by linarith) 2)) _).ne'
  have hAp : (16 * c₁) ^ ((d : ℝ) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos (by positivity) _).ne'
  apply le_of_eq
  generalize (16 * c₁) ^ ((d : ℝ) / 2) = A at *
  generalize (4 * ((d : ℝ) / (d - 2)) ^ 2) ^ ((d : ℝ) * (d - 2) / 4) = B at *
  generalize Z ^ ((d : ℝ) / 2) = z at *
  field_simp

end PDE.DGNMMoser
