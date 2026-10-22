module

public import PDEFoundation.Ambient.Basic
public import PDEFoundation.FunctionalInequalities.PrekopaLeindler.OneDim

/-!
# Prékopa--Leindler in `Vec d` for `[0,∞]`-valued measurable functions

Induction on the dimension via the splitting `Vec (d + 1) ≃ ℝ × Vec d` and Tonelli.
-/

@[expose] public section

namespace PDE.PrekopaLeindlerProof

open MeasureTheory Set
open scoped ENNReal Pointwise

/-- The splitting `Vec (d+1) ≃ ℝ × Vec d` commutes with convex combinations. -/
theorem splitting_symm_combo (d : ℕ) (l : ℝ) (p q : ℝ × Vec d) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm
        (l • p + (1 - l) • q) =
      l • (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm p +
        (1 - l) • (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm q := by
  ext j
  refine Fin.cases ?_ (fun i => ?_) j <;>
    simp [MeasurableEquiv.piFinSuccAbove]

/-- Prékopa--Leindler in `Vec d` for measurable `[0,∞]`-valued functions. -/
theorem ennreal_vec (d : ℕ) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {f g k : Vec d → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hk : Measurable k)
    (hyp : ∀ x y, f x ^ l * g y ^ (1 - l) ≤ k (l • x + (1 - l) • y)) :
    (∫⁻ x, f x) ^ l * (∫⁻ x, g x) ^ (1 - l) ≤ ∫⁻ x, k x := by
  induction d with
  | zero =>
    have h := hyp default default
    have hv : (volume : Measure (Vec 0)) univ = 1 := by
      rw [volume_pi, Measure.pi_univ]; simp
    have e : ∀ u : Vec 0 → ℝ≥0∞, ∫⁻ x, u x = u default := fun u => by
      rw [lintegral_unique, hv, mul_one]; exact congrArg u (Subsingleton.elim _ _)
    rw [e, e, e]
    have hd : (l • (default : Vec 0) + (1 - l) • default) = default := Subsingleton.elim _ _
    rwa [hd] at h
  | succ d ih =>
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0 with he
    have hmp : MeasurePreserving e.symm (volume : Measure (ℝ × Vec d)) volume :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm
    have hint : ∀ u : Vec (d + 1) → ℝ≥0∞, Measurable u →
        ∫⁻ x, u x = ∫⁻ x1 : ℝ, ∫⁻ x' : Vec d, u (e.symm (x1, x')) := by
      intro u hu
      rw [← hmp.lintegral_comp_emb e.symm.measurableEmbedding u, Measure.volume_eq_prod]
      exact lintegral_prod _ (hu.comp e.symm.measurable).aemeasurable
    have hm : ∀ u : Vec (d + 1) → ℝ≥0∞, Measurable u →
        Measurable fun x1 : ℝ => ∫⁻ x' : Vec d, u (e.symm (x1, x')) := fun u hu =>
      (hu.comp e.symm.measurable).lintegral_prod_right'
    have hfib : ∀ x1 y1 : ℝ, (∫⁻ x' : Vec d, f (e.symm (x1, x'))) ^ l *
        (∫⁻ y' : Vec d, g (e.symm (y1, y'))) ^ (1 - l) ≤
        ∫⁻ z : Vec d, k (e.symm (l • x1 + (1 - l) • y1, z)) := fun x1 y1 => by
      refine ih (f := fun x' => f (e.symm (x1, x'))) (g := fun y' => g (e.symm (y1, y')))
        (k := fun z => k (e.symm (l • x1 + (1 - l) • y1, z)))
        (hf.comp (e.symm.measurable.comp measurable_prodMk_left))
        (hg.comp (e.symm.measurable.comp measurable_prodMk_left))
        (hk.comp (e.symm.measurable.comp measurable_prodMk_left)) fun x' y' => ?_
      have h := hyp (e.symm (x1, x')) (e.symm (y1, y'))
      rw [← splitting_symm_combo] at h
      exact h
    rw [hint f hf, hint g hg, hint k hk]
    exact oneDim hl0 hl1 (hm f hf) (hm g hg) (hm k hk) hfib

end PDE.PrekopaLeindlerProof
