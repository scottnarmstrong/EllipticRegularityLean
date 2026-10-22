module

public import EllipticRegularity.Ch4.Examples.Basic

/-!
# Measure of a slab of the unit ball
-/

@[expose] public section

namespace PDE.Ch4Examples

open MeasureTheory

/-- The slab `{|x₀| < l}` of the unit ball of `ℝ^{n+1}` has measure at most `2 l |B^n_1|`. -/
theorem slab_measure_le (n : ℕ) (l : ℝ) :
    volume {x ∈ euclideanBall (0 : Vec (n + 1)) 1 | |x 0| < l} ≤
      ENNReal.ofReal (2 * l) * volume (euclideanBall (0 : Vec n) 1) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  let P : Set (ℝ × (Fin n → ℝ)) := Set.Ioo (-l) l ×ˢ euclideanBall (0 : Vec n) 1
  have hsub : {x ∈ euclideanBall (0 : Vec (n + 1)) 1 | |x 0| < l} ⊆ e ⁻¹' P := by
    intro x ⟨hx, hl⟩
    refine ⟨abs_lt.1 hl |> fun h => ⟨h.1, h.2⟩, ?_⟩
    rw [mem_euclideanBall_zero_iff] at hx ⊢
    rw [vecNormSq_eq_sum_sq, Fin.sum_univ_succ] at hx
    rw [vecNormSq_eq_sum_sq]
    have h0 : 0 ≤ x 0 ^ 2 := sq_nonneg _
    have h2 : (e x).2 = fun j => x j.succ := by
      ext j
      simp [e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.tail]
    change ∑ i, (e x).2 i ^ 2 < 1 ^ 2
    rw [h2]
    linarith
  calc volume {x ∈ euclideanBall (0 : Vec (n + 1)) 1 | |x 0| < l}
      ≤ volume (e ⁻¹' P) := measure_mono hsub
    _ = volume P := hmp.measure_preimage_equiv P
    _ = ENNReal.ofReal (2 * l) * volume (euclideanBall (0 : Vec n) 1) := by
        rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo]
        congr 2
        ring

end PDE.Ch4Examples
