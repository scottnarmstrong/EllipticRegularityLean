module

public import PDEFoundation.Analysis.Gehring.LocalGeom
public import PDEFoundation.Analysis.Gehring.TailGlobal

/-!
# The localized tail estimate (Lemma 4.6)

For `g` vanishing outside `B_R` and levels `t ≥ T_{ρ,R}`, applying the family-general tail
estimate to the selected Whitney cubes meeting `B_ρ` (for which `σ Q ⊆ B_R ⊆ B_1`, so that the
local reverse Hölder hypothesis applies) gives the tail estimate with left side restricted
to `B_ρ`.
-/

@[expose] public section

namespace PDE.Gehring

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

/-- **Localized tail estimate** (4.32 on `B_ρ`, `t ≥ T_{ρ,R}`). The reverse Hölder
inequality is only required for cubes `Q` with `σ Q ⊆ B_R`. -/
theorem local_tail (hd : 0 < d) {g h : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hh0 : ∀ x, 0 ≤ h x)
    (hg : Integrable g volume) (hc : HasCompactSupport g) (hh : LocallyIntegrable h volume)
    {σ A B ρ R m t : ℝ} (hσ : σ = 2 ∨ σ = 4) (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ : 0 < ρ)
    (hρR : ρ < R) (hR : R ≤ 1)
    (hsupp : ∀ x, x ∉ euclideanBall (0 : Vec d) R → g x = 0)
    (hm : 0 < m) (hmg : integralAverage (euclideanBall (0 : Vec d) 1) g ≤ m)
    (ht : (3 * Real.sqrt d / (R - ρ)) ^ (d + 1) * m ≤ t)
    (hrh : ∀ (z : Vec d) (r : ℝ), 0 < r → centeredAxisCube z (σ * r) ⊆ euclideanBall (0 : Vec d) R →
      GehringRH d σ A B g h z r) :
    ∫⁻ x in {x | t < g x} ∩ euclideanBall (0 : Vec d) ρ, ENNReal.ofReal (g x) ≤
      ENNReal.ofReal (gehringD d * A * t ^ (1 - gehringTheta d)) *
          (∫⁻ y in {y | gehringC d * t < g y}, ENNReal.ofReal (g y ^ gehringTheta d)) +
        ENNReal.ofReal (B * gehringN σ d) * ∫⁻ x in gehringE g t, ENNReal.ofReal (h x) := by
  have hδ : 0 < R - ρ := by linarith
  have hdR : (0 : ℝ) < d := Nat.cast_pos.2 hd
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 hdR
  have hTpos : 0 < (3 * Real.sqrt d / (R - ρ)) ^ (d + 1) * m := by positivity
  have htpos : 0 < t := lt_of_lt_of_le hTpos ht
  obtain ⟨F⟩ := exists_whitneyFamily hd hg0 hg hc htpos hσ
  set T : Set F.ι := {i | (dyadicCube (F.scale i) (F.index i) ∩ euclideanBall (0 : Vec d) ρ).Nonempty}
    with hT
  have h1 := lintegral_gt_le_family hd hg0 hh0 hg hh hσ hA hB htpos.le F T
    (euclideanBall (0 : Vec d) ρ)
    (by
      intro i hi
      obtain ⟨_, hsub⟩ := Loc.local_conclusions hd hg0 hg hc hρR hR hρ hsupp hm hmg ht hσ F i hi
      have e : σ * (F.toWhitneyCover.side i / 2) = σ * 2 ^ (F.scale i) / 2 := by
        simp only [WhitneyCover.side]; ring
      refine hrh _ _ (by have := F.toWhitneyCover.side_pos i; positivity) ?_
      rw [e]
      exact hsub)
    (by
      have hnull := F.toWhitneyCover.volume_diff_iUnion_cube_eq_zero
      filter_upwards [ae_lt_mem_gehringE hd hg0 hg hc htpos,
        measure_eq_zero_iff_ae_notMem.1 hnull] with x hx1 hx2 hx3
      have hxE := hx1 hx3.1
      have : x ∈ ⋃ i, F.toWhitneyCover.cube i := by
        by_contra hcon
        exact hx2 ⟨hxE, hcon⟩
      obtain ⟨i, hi⟩ := mem_iUnion.1 this
      refine mem_biUnion (x := i) ?_ hi
      exact ⟨x, centeredAxisCube_subset_dyadicCube _ _ hi, hx3.2⟩)
  refine h1.trans (add_le_add ?_ le_rfl)
  have h2 := volume_gehringE_le hd hg0 hg htpos
  have hH := gehringH_pos d
  calc ENNReal.ofReal (A * gehringH d * t) * volume (gehringE g t)
      ≤ ENNReal.ofReal (A * gehringH d * t) * (ENNReal.ofReal (2 * 3 ^ d / t ^ gehringTheta d) *
          ∫⁻ y in {y | gehringC d * t < g y}, ENNReal.ofReal (g y ^ gehringTheta d)) := by
        gcongr
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [Real.rpow_sub htpos, Real.rpow_one, gehringD]
        field_simp

end PDE.Gehring
