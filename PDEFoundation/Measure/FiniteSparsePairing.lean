module

public import PDEFoundation.Measure.SingleSparsePairing
public import PDEFoundation.Measure.DisjointIntegralPacking

/-! # The finite sparse pairing bound with exact factor four thirds -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory
open scoped ENNReal

/-- Sum the actual single-box estimates over disjoint sparse remainders.
This is the finite bilinear estimate before Hölder and the sharp dyadic
maximal bound. Every integral is extended nonnegative. -/
theorem finite_sparse_pairing_le
    {d : ℕ} (I : Box (Fin d)) (S : Finset (List (Set (Fin d))))
    (b φ : Vec d → ℝ) (a : List (Set (Fin d)) → ℝ)
    (E : List (Set (Fin d)) → Set (Vec d))
    (hE : ∀ p ∈ S, MeasurableSet (E p))
    (hsub : ∀ p ∈ S, E p ⊆ (dyadicDescendant I p : Set (Vec d)))
    (hdisj : (S : Set (List (Set (Fin d)))).PairwiseDisjoint E)
    (hpacking : ∀ p ∈ S, ENNReal.ofReal (3 / 4 : ℝ) *
      volume (dyadicDescendant I p : Set (Vec d)) ≤ volume (E p))
    (hminor : ∀ p ∈ S, ∀ᵐ x ∂volume.restrict (dyadicDescendant I p : Set (Vec d)),
      a p ≤ |b x|) :
    (∑ p ∈ S, ENNReal.ofReal (a p) *
      ∫⁻ x in (dyadicDescendant I p : Set (Vec d)), ENNReal.ofReal |φ x|) ≤
      ENNReal.ofReal (4 / 3 : ℝ) *
        ∫⁻ x in (I : Set (Vec d)), ENNReal.ofReal |b x| * dyadicBoxMaximal I φ x := by
  have hsum := sum_setLIntegral_le_of_pairwiseDisjoint volume S E (I : Set (Vec d))
    (fun x => ENNReal.ofReal |b x| * dyadicBoxMaximal I φ x) hE hdisj
    (fun p hp => (hsub p hp).trans (dyadicDescendant_le I p))
  calc
    (∑ p ∈ S, ENNReal.ofReal (a p) *
        ∫⁻ x in (dyadicDescendant I p : Set (Vec d)), ENNReal.ofReal |φ x|) ≤
      ∑ p ∈ S, ENNReal.ofReal (4 / 3 : ℝ) *
        ∫⁻ x in E p, ENNReal.ofReal |b x| * dyadicBoxMaximal I φ x := by
      apply Finset.sum_le_sum
      intro p hp
      exact single_sparse_pairing_le I p b φ (a p) (E p)
        (hE p hp) (hsub p hp) (hpacking p hp) (hminor p hp)
    _ = ENNReal.ofReal (4 / 3 : ℝ) *
        ∑ p ∈ S, ∫⁻ x in E p, ENNReal.ofReal |b x| * dyadicBoxMaximal I φ x := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_right hsum _

end PDE
