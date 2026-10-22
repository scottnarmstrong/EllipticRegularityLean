module

public import PDEFoundation.Analysis.Gehring.LocalTruncYoung

/-!
# One step of the localization iteration (Lemma 4.6)

With `I_L(D) = ∫_D g min(g, L)^ε` (`truncMomentOn`), for `0 < ρ < R ≤ 1`:
`I_L(B_ρ) ≤ T_{ρ,R}^ε ∫ g + (1/4) I_L(B_R) + 8^ε (2 B N_σ)^{1+ε} ∫ h^{1+ε}`,
for `g, h` not necessarily supported in `B_R` (the zero extension is taken inside the proof).
-/

@[expose] public section

namespace PDE.Gehring

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

/-- The truncated moment `I_L(D) = ∫_D g min(g, L)^ε` over a domain `D`. -/
noncomputable def truncMomentOn (g : Vec d → ℝ) (L ε : ℝ) (D : Set (Vec d)) : ℝ≥0∞ :=
  ∫⁻ x in D, ENNReal.ofReal (g x) * (min (ENNReal.ofReal (g x)) (ENNReal.ofReal L)) ^ ε

theorem truncMoment_indicator {D : Set (Vec d)} (hD : MeasurableSet D) {g : Vec d → ℝ}
    {L ε : ℝ} (hε : 0 < ε) :
    truncMoment (D.indicator g) L ε = truncMomentOn g L ε D := by
  unfold truncMoment truncMomentOn
  rw [← lintegral_indicator hD]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ D <;> simp [hx, ENNReal.zero_rpow_of_pos hε]

theorem truncMomentOn_le_truncMoment (g : Vec d → ℝ) (L ε : ℝ) (D : Set (Vec d)) :
    truncMomentOn g L ε D ≤ truncMoment g L ε :=
  setLIntegral_le_lintegral _ _

theorem centeredAxisCube_mono {z : Vec d} {r r' : ℝ} (h : r ≤ r') :
    centeredAxisCube z r ⊆ centeredAxisCube z r' := by
  intro x hx i hi
  have := hx i hi
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- The reverse Hölder predicate only depends on `g`, `h` on the dilated cube `σ Q`. -/
theorem GehringRH.congr_eqOn {σ A B : ℝ} {g g' h h' : Vec d → ℝ} {z : Vec d} {r : ℝ}
    (hσ : 1 ≤ σ) (hr : 0 < r)
    (hg : ∀ᵐ x ∂(volume.restrict (centeredAxisCube z (σ * r))), g x = g' x)
    (hh : ∀ x ∈ centeredAxisCube z (σ * r), h x = h' x)
    (hrh : GehringRH d σ A B g h z r) : GehringRH d σ A B g' h' z r := by
  unfold GehringRH at hrh ⊢
  have hQ : centeredAxisCube z r ⊆ centeredAxisCube z (σ * r) :=
    centeredAxisCube_mono (by nlinarith)
  have hmeas : MeasurableSet (centeredAxisCube z (σ * r)) := (isOpen_centeredAxisCube _ _).measurableSet
  have hgQ : ∀ᵐ x ∂(volume.restrict (centeredAxisCube z r)), g x = g' x :=
    ae_restrict_of_ae_restrict_of_subset hQ hg
  have h1 : ∫ x in centeredAxisCube z r, g' x = ∫ x in centeredAxisCube z r, g x :=
    integral_congr_ae (by filter_upwards [hgQ] with x hx using hx.symm)
  have h2 : integralAverage (centeredAxisCube z (σ * r))
      (fun x => g' x ^ ((d : ℝ) / ((d : ℝ) + 1))) =
      integralAverage (centeredAxisCube z (σ * r)) (fun x => g x ^ ((d : ℝ) / ((d : ℝ) + 1))) := by
    unfold integralAverage
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hg] with x hx
    rw [hx]
  have h3 : ∫ x in centeredAxisCube z (σ * r), h' x = ∫ x in centeredAxisCube z (σ * r), h x :=
    setIntegral_congr_fun hmeas fun x hx => (hh x hx).symm
  rw [h1, h2, h3]
  exact hrh

/-- **One localization step**, with the zero extension to `B_R` taken internally. -/
theorem local_step (hd : 2 ≤ d) {g h : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hh0 : ∀ x, 0 ≤ h x) (hgm : Measurable g) (hg : Integrable g volume)
    (hc : HasCompactSupport g) {σ A B ρ R m ε L : ℝ}
    (hh : MemLp h (ENNReal.ofReal (1 + ε)) volume) (hσ : σ = 2 ∨ σ = 4) (hA : 1 ≤ A)
    (hB : 0 ≤ B) (hε : 0 < ε) (hεA : ε ≤ 1 / (8 * gehringG d * A)) (hL : 0 < L)
    (hρ : 0 < ρ) (hρR : ρ < R) (hR : R ≤ 1)
    (hm : 0 < m) (hmg : integralAverage (euclideanBall (0 : Vec d) 1) g ≤ m)
    (hrh : ∀ (z : Vec d) (r : ℝ), 0 < r → centeredAxisCube z (σ * r) ⊆ euclideanBall (0 : Vec d) 1 →
      GehringRH d σ A B g h z r) :
    truncMomentOn g L ε (euclideanBall (0 : Vec d) ρ) ≤
      ENNReal.ofReal (((3 * Real.sqrt d / (R - ρ)) ^ (d + 1) * m) ^ ε) *
          (∫⁻ x, ENNReal.ofReal (g x)) +
        ENNReal.ofReal (1 / 4) * truncMomentOn g L ε (euclideanBall (0 : Vec d) R) +
        ENNReal.ofReal (8 ^ ε * (2 * B * gehringN σ d) ^ (1 + ε)) *
          ∫⁻ x, ENNReal.ofReal (h x) ^ (1 + ε) := by
  set BR := euclideanBall (0 : Vec d) R with hBR
  have hRm : MeasurableSet BR := (isOpen_euclideanBall _ _).measurableSet
  have hσ1 : 1 ≤ σ := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hR0 : 0 ≤ R := by linarith
  have hBRsub : BR ⊆ euclideanBall (0 : Vec d) 1 := Loc.euclideanBall_zero_mono hR hR0
  set g' := BR.indicator g with hg'
  set h' := BR.indicator h with hh'
  have hg'0 : ∀ x, 0 ≤ g' x := fun x => Set.indicator_nonneg (fun x _ => hg0 x) x
  have hh'0 : ∀ x, 0 ≤ h' x := fun x => Set.indicator_nonneg (fun x _ => hh0 x) x
  have hg'c : HasCompactSupport g' := by
    refine HasCompactSupport.intro hc.isCompact fun x hx => ?_
    by_cases hxB : x ∈ BR
    · rw [hg', Set.indicator_of_mem hxB]; exact image_eq_zero_of_notMem_tsupport hx
    · rw [hg', Set.indicator_of_notMem hxB]
  have hg'i : Integrable g' volume := hg.indicator hRm
  have hmg' : integralAverage (euclideanBall (0 : Vec d) 1) g' ≤ m := by
    refine le_trans ?_ hmg
    unfold integralAverage
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine setIntegral_mono hg'i.integrableOn hg.integrableOn fun x => ?_
    by_cases hxB : x ∈ BR
    · rw [hg', Set.indicator_of_mem hxB]
    · rw [hg', Set.indicator_of_notMem hxB]; exact hg0 x
  have key := local_truncated_young hd hg'0 hh'0 (hgm.indicator hRm) hg'i hg'c
    (hh.indicator hRm) hσ hA hB hε hεA hL hρ hρR hR
    (fun x hx => by rw [hg', Set.indicator_of_notMem hx]) hm hmg'
    (by
      intro z r hr hsub
      refine GehringRH.congr_eqOn hσ1 hr ?_ ?_ (hrh z r hr (hsub.trans hBRsub))
      · exact ae_restrict_of_forall_mem (isOpen_centeredAxisCube _ _).measurableSet fun x hx => by
          rw [hg', Set.indicator_of_mem (hsub hx)]
      · intro x hx
        rw [hh', Set.indicator_of_mem (hsub hx)])
  have hρsub : euclideanBall (0 : Vec d) ρ ⊆ BR := Loc.euclideanBall_zero_mono hρR.le hρ.le
  have e1 : truncMomentOn g L ε (euclideanBall (0 : Vec d) ρ) =
      ∫⁻ x in euclideanBall (0 : Vec d) ρ,
        ENNReal.ofReal (g' x) * (min (ENNReal.ofReal (g' x)) (ENNReal.ofReal L)) ^ ε := by
    unfold truncMomentOn
    refine setLIntegral_congr_fun (isOpen_euclideanBall _ _).measurableSet fun x hx => ?_
    rw [hg', Set.indicator_of_mem (hρsub hx)]
  have e2 : truncMoment g' L ε = truncMomentOn g L ε BR := truncMoment_indicator hRm hε
  have i1 : ∫⁻ x, ENNReal.ofReal (g' x) ≤ ∫⁻ x, ENNReal.ofReal (g x) := by
    refine lintegral_mono fun x => ?_
    by_cases hxB : x ∈ BR
    · rw [hg', Set.indicator_of_mem hxB]
    · rw [hg', Set.indicator_of_notMem hxB]; simp
  have i2 : ∫⁻ x, ENNReal.ofReal (h' x) ^ (1 + ε) ≤ ∫⁻ x, ENNReal.ofReal (h x) ^ (1 + ε) := by
    refine lintegral_mono fun x => ?_
    by_cases hxB : x ∈ BR
    · rw [hh', Set.indicator_of_mem hxB]
    · rw [hh', Set.indicator_of_notMem hxB]
      simp [ENNReal.zero_rpow_of_pos (by linarith : (0 : ℝ) < 1 + ε)]
  rw [e1]
  refine key.trans ?_
  rw [e2]
  gcongr

end PDE.Gehring
