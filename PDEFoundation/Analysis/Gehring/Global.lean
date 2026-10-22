module

public import PDEFoundation.Analysis.Gehring.GlobalMeasurable

/-!
# The global Gehring estimate (Lemma 4.6, part (a))

`gehring_global`: part (a) of the quantitative Gehring lemma in exactly the shape of the first
conjunct of `exists_gehring_constant`, with the explicit constant `gehringGlobalC d`.
-/

@[expose] public section

namespace PDE.Gehring

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

/-- The reverse Hölder predicate only depends on the a.e.-class of `g`. -/
theorem GehringRH.congr_ae {σ A B : ℝ} {g g' h : Vec d → ℝ} (hae : g =ᵐ[volume] g')
    {z : Vec d} {r : ℝ} (hrh : GehringRH d σ A B g h z r) : GehringRH d σ A B g' h z r := by
  unfold GehringRH at hrh ⊢
  have h1 : ∫ x in centeredAxisCube z r, g' x = ∫ x in centeredAxisCube z r, g x :=
    integral_congr_ae (ae_restrict_of_ae hae.symm)
  have h2 : integralAverage (centeredAxisCube z (σ * r)) (fun x => g' x ^ ((d : ℝ) / ((d : ℝ) + 1))) =
      integralAverage (centeredAxisCube z (σ * r)) (fun x => g x ^ ((d : ℝ) / ((d : ℝ) + 1))) := by
    unfold integralAverage
    congr 1
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hae] with x hx
    rw [hx]
  rw [h1, h2]
  exact hrh

/-- **Quantitative Gehring lemma, part (a)** (4.28), with the explicit constant
`gehringGlobalC d`. -/
theorem gehring_global (hd : 2 ≤ d) {σ : ℝ} (hσ : σ = 2 ∨ σ = 4) {A B ε : ℝ} (hA : 1 ≤ A)
    (hB : 0 ≤ B) (hε : 0 < ε) (hεA : ε ≤ 1 / (gehringGlobalC d * A))
    {g h : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hh0 : ∀ x, 0 ≤ h x)
    (hg : Integrable g volume) (hc : HasCompactSupport g)
    (hh : MemLp h (ENNReal.ofReal (1 + ε)) volume)
    (hrh : ∀ (z : Vec d) (r : ℝ), 0 < r → GehringRH d σ A B g h z r) :
    eLpNorm g (ENNReal.ofReal (1 + ε)) volume ≤
      ENNReal.ofReal (gehringGlobalC d * B) * eLpNorm h (ENNReal.ofReal (1 + ε)) volume := by
  classical
  set gm := hg.aemeasurable.mk g with hgmdef
  have hgm : Measurable gm := hg.aemeasurable.measurable_mk
  set g' : Vec d → ℝ := (tsupport g).indicator (fun x => max (gm x) 0) with hg'
  have hg'm : Measurable g' :=
    (hgm.max measurable_const).indicator (isClosed_tsupport g).measurableSet
  have hg'0 : ∀ x, 0 ≤ g' x := fun x => by
    by_cases hx : x ∈ tsupport g
    · rw [hg', Set.indicator_of_mem hx]; exact le_max_right _ _
    · rw [hg', Set.indicator_of_notMem hx]
  have hae : g =ᵐ[volume] g' := by
    filter_upwards [hg.aemeasurable.ae_eq_mk] with x hx
    by_cases hxs : x ∈ tsupport g
    · have hx' : gm x = g x := hx.symm
      rw [hg', Set.indicator_of_mem hxs]
      show g x = max (gm x) 0
      rw [hx', max_eq_left (hg0 x)]
    · rw [hg', Set.indicator_of_notMem hxs, image_eq_zero_of_notMem_tsupport hxs]
  have hg'i : Integrable g' volume := hg.congr hae
  have hg'c : HasCompactSupport g' :=
    HasCompactSupport.intro hc.isCompact fun x hx => by
      rw [hg', Set.indicator_of_notMem hx]
  have := global_measurable hd hσ hA hB hε hεA hg'0 hh0 hg'm hg'i hg'c hh
    (fun z r hr => (hrh z r hr).congr_ae hae)
  rw [eLpNorm_congr_ae hae]
  exact this

/-- **Part (a) of the quantitative Gehring lemma**, in exactly the shape of the first conjunct
of `exists_gehring_constant` (with `C = gehringGlobalC d`, independent of
`σ, A, B, ε, g, h`). -/
theorem exists_gehring_global_constant (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (σ : ℝ), (σ = 2 ∨ σ = 4) →
      ∀ (A B ε : ℝ), 1 ≤ A → 0 ≤ B → 0 < ε → ε ≤ 1 / (C * A) →
      ∀ g h : Vec d → ℝ, (∀ x, 0 ≤ g x) → (∀ x, 0 ≤ h x) →
        ((Integrable g volume ∧ HasCompactSupport g ∧
            MemLp h (ENNReal.ofReal (1 + ε)) volume ∧
            ∀ (z : Vec d) (r : ℝ), 0 < r →
              ∫ x in centeredAxisCube z r, g x ≤
                A * (volume (centeredAxisCube z r)).toReal *
                    (integralAverage (centeredAxisCube z (σ * r))
                      (fun x => g x ^ ((d : ℝ) / ((d : ℝ) + 1)))) ^
                        (((d : ℝ) + 1) / (d : ℝ)) +
                  B * ∫ x in centeredAxisCube z (σ * r), h x) →
          eLpNorm g (ENNReal.ofReal (1 + ε)) volume ≤
            ENNReal.ofReal (C * B) *
              eLpNorm h (ENNReal.ofReal (1 + ε)) volume) :=
  ⟨gehringGlobalC d, one_le_gehringGlobalC d, fun _σ hσ _A _B _ε hA hB hε hεA _g _h hg0 hh0
    ⟨hg, hc, hh, hrh⟩ => gehring_global hd hσ hA hB hε hεA hg0 hh0 hg hc hh hrh⟩

end PDE.Gehring
