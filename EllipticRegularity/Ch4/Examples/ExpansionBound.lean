module

public import EllipticRegularity.Ch4.Examples.Basic

/-!
# Expansion of positivity for small `θ`: the integral bound

For `u ≥ 0` with `|{u ≥ 1} ∩ B₁| ≥ (1-θ)|B₁|`,
`∫_{B₁} (u+ε)^{-p} ≤ |B₁| + ε^{-p} θ |B₁|`.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE.Ch4Examples

open MeasureTheory Filter

theorem inv_power_lintegral_bound {d : ℕ} {B : Set (Vec d)} (hB : MeasurableSet B)
    (hBtop : volume B ≠ ⊤) (u : H1Function B)
    (hnn : ∀ᵐ x ∂(volumeOn (B)), 0 ≤ u.toFun x)
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hdens : ENNReal.ofReal (1 - θ) * volume (B) ≤
      volume {x ∈ B | 1 ≤ u.toFun x})
    (ε p : ℝ) (hε : 0 < ε) (hp : 0 < p) :
    ∫⁻ x in B, ENNReal.ofReal ((u.toFun x + ε)⁻¹ ^ p) ≤
      volume (B) +
        ENNReal.ofReal (ε⁻¹ ^ p) * (ENNReal.ofReal θ * volume (B)) := by
  have hmeas : AEStronglyMeasurable u.toFun (volumeOn B) := u.memL2.aestronglyMeasurable
  set u' := hmeas.mk u.toFun with hu'def
  have hu' : StronglyMeasurable u' := hmeas.stronglyMeasurable_mk
  have hae : u.toFun =ᵐ[volumeOn B] u' := hmeas.ae_eq_mk
  set A : Set (Vec d) := {x | 1 ≤ u' x} with hAdef
  have hA : MeasurableSet A := measurableSet_le measurable_const hu'.measurable
  have hboth : ∀ᵐ x ∂(volumeOn B), 0 ≤ u.toFun x ∧ u.toFun x = u' x := hnn.and hae
  -- density for `B ∩ A`
  have hdens' : ENNReal.ofReal (1 - θ) * volume B ≤ volume (B ∩ A) := by
    refine hdens.trans ?_
    have hN : volume {x | ¬ (x ∈ B → u.toFun x = u' x)} = 0 := by
      have := (ae_restrict_iff' hB).1 hae
      exact ae_iff.1 this
    calc volume {x ∈ B | 1 ≤ u.toFun x}
        ≤ volume ((B ∩ A) ∪ {x | ¬ (x ∈ B → u.toFun x = u' x)}) := by
          refine measure_mono ?_
          intro x ⟨hxB, hx1⟩
          by_cases h : u.toFun x = u' x
          · exact Or.inl ⟨hxB, by simpa [hAdef, ← h] using hx1⟩
          · exact Or.inr (fun h' => h (h' hxB))
      _ ≤ volume (B ∩ A) + volume {x | ¬ (x ∈ B → u.toFun x = u' x)} := measure_union_le _ _
      _ = volume (B ∩ A) := by rw [hN, add_zero]
  have hsplit := lintegral_inter_add_sdiff
    (fun x => ENNReal.ofReal ((u.toFun x + ε)⁻¹ ^ p)) B hA (μ := volume)
  rw [← hsplit]
  -- the two pieces
  have h1 : ∫⁻ x in B ∩ A, ENNReal.ofReal ((u.toFun x + ε)⁻¹ ^ p) ≤ volume (B ∩ A) := by
    calc ∫⁻ x in B ∩ A, ENNReal.ofReal ((u.toFun x + ε)⁻¹ ^ p)
        ≤ ∫⁻ x in B ∩ A, 1 := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left hboth,
            ae_restrict_mem (hB.inter hA)] with x hx hxm
          obtain ⟨_, hxe⟩ := hx
          have h1x : 1 ≤ u.toFun x := by rw [hxe]; exact hxm.2
          have : (u.toFun x + ε)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
          exact ENNReal.ofReal_le_one.2 (Real.rpow_le_one (by positivity) this hp.le)
      _ = volume (B ∩ A) := by simp
  have h2 : ∫⁻ x in B \ A, ENNReal.ofReal ((u.toFun x + ε)⁻¹ ^ p) ≤
      ENNReal.ofReal (ε⁻¹ ^ p) * volume (B \ A) := by
    calc ∫⁻ x in B \ A, ENNReal.ofReal ((u.toFun x + ε)⁻¹ ^ p)
        ≤ ∫⁻ x in B \ A, ENNReal.ofReal (ε⁻¹ ^ p) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_of_ae_restrict_of_subset Set.sdiff_subset hboth] with x hx
          have hx0 := hx.1
          have : (u.toFun x + ε)⁻¹ ≤ ε⁻¹ := inv_anti₀ hε (by linarith)
          exact ENNReal.ofReal_le_ofReal
            (Real.rpow_le_rpow (by positivity) this hp.le)
      _ = ENNReal.ofReal (ε⁻¹ ^ p) * volume (B \ A) := by simp
  have hcompl : volume (B \ A) ≤ ENNReal.ofReal θ * volume B := by
    have hsum := measure_inter_add_sdiff B hA (μ := volume)
    have hsum2 : volume B = ENNReal.ofReal (1 - θ) * volume B + ENNReal.ofReal θ * volume B := by
      rw [← add_mul, ← ENNReal.ofReal_add (by linarith) hθ.le]
      simp
    have hfin : volume (B ∩ A) ≠ ⊤ := ne_top_of_le_ne_top hBtop (measure_mono Set.inter_subset_left)
    have : volume (B ∩ A) + volume (B \ A) ≤ volume (B ∩ A) + ENNReal.ofReal θ * volume B := by
      rw [hsum]
      calc volume B = ENNReal.ofReal (1 - θ) * volume B + ENNReal.ofReal θ * volume B := hsum2
        _ ≤ volume (B ∩ A) + ENNReal.ofReal θ * volume B := by gcongr
    exact (ENNReal.add_le_add_iff_left hfin).1 this
  calc _ ≤ volume (B ∩ A) + ENNReal.ofReal (ε⁻¹ ^ p) * volume (B \ A) := add_le_add h1 h2
    _ ≤ volume B + ENNReal.ofReal (ε⁻¹ ^ p) * (ENNReal.ofReal θ * volume B) := by
        have := measure_mono (μ := volume) (Set.inter_subset_left : B ∩ A ⊆ B)
        gcongr

end PDE.Ch4Examples
