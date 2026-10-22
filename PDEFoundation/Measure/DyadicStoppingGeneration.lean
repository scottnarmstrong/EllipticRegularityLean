module

public import PDEFoundation.Measure.DyadicOscillationStopPacking

/-! # Recursive generations of dyadic oscillation stopping paths -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory Set

/-- The literal quadratic oscillation stopping predicate relative to a root
box and its coordinatewise mean. -/
def dyadicOscillationBad {d m : ℕ} (I : Box (Fin d))
    (g : Vec d → Vec m) (q : List (Set (Fin d))) : Prop :=
  integralAverage (dyadicDescendant I q : Set (Vec d))
      (fun x => vecNormSq (g x - coordinateVectorAverage (I : Set (Vec d)) g)) >
    4 * integralAverage (I : Set (Vec d))
      (fun x => vecNormSq (g x - coordinateVectorAverage (I : Set (Vec d)) g))

/-- Literal recursive generations: generation zero is the root path, and the
next generation appends every first stopping path relative to each current
root. -/
def dyadicStoppingGeneration {d m : ℕ} (I : Box (Fin d))
    (g : Vec d → Vec m) : ℕ → Set (List (Set (Fin d)))
  | 0 => {[]}
  | n + 1 => {r | ∃ p ∈ dyadicStoppingGeneration I g n,
      ∃ q, IsFirstPrefixStop (dyadicOscillationBad (dyadicDescendant I p) g) q ∧
        r = p ++ q}

@[simp]
theorem mem_dyadicStoppingGeneration_zero {d m : ℕ} (I : Box (Fin d))
    (g : Vec d → Vec m) (p : List (Set (Fin d))) :
    p ∈ dyadicStoppingGeneration I g 0 ↔ p = [] := by
  rfl

theorem mem_dyadicStoppingGeneration_succ {d m : ℕ} (I : Box (Fin d))
    (g : Vec d → Vec m) (n : ℕ) (r : List (Set (Fin d))) :
    r ∈ dyadicStoppingGeneration I g (n + 1) ↔
      ∃ p ∈ dyadicStoppingGeneration I g n,
        ∃ q, IsFirstPrefixStop (dyadicOscillationBad (dyadicDescendant I p) g) q ∧
          r = p ++ q := by
  rfl

theorem not_dyadicOscillationBad_nil {d m : ℕ} (I : Box (Fin d))
    (g : Vec d → Vec m) : ¬dyadicOscillationBad I g [] := by
  unfold dyadicOscillationBad
  rw [dyadicDescendant_nil]
  have hnonneg : 0 ≤ integralAverage (I : Set (Vec d))
      (fun x => vecNormSq (g x - coordinateVectorAverage (I : Set (Vec d)) g)) :=
    integralAverage_nonneg I.measurableSet_coe (fun x _ => vecNormSq_nonneg _)
  linarith

theorem firstPrefixStop_dyadicOscillationBad_ne_nil {d m : ℕ}
    (I : Box (Fin d)) (g : Vec d → Vec m) {q : List (Set (Fin d))}
    (hq : IsFirstPrefixStop (dyadicOscillationBad I g) q) : q ≠ [] :=
  firstPrefixStop_ne_nil (not_dyadicOscillationBad_nil I g) hq

/-- The literal descendant carriers at every recursively defined generation
are pairwise disjoint. -/
theorem pairwiseDisjoint_dyadicStoppingGeneration {d m : ℕ}
    (I : Box (Fin d)) (g : Vec d → Vec m) (n : ℕ) :
    (dyadicStoppingGeneration I g n).Pairwise
      (fun p q => Disjoint (dyadicDescendant I p : Set (Vec d))
        (dyadicDescendant I q : Set (Vec d))) := by
  induction n with
  | zero =>
      intro p hp q hq hpq
      simp only [mem_dyadicStoppingGeneration_zero] at hp hq
      exact (hpq (hp.trans hq.symm)).elim
  | succ n ih =>
      intro r₁ hr₁ r₂ hr₂ hrne
      rw [mem_dyadicStoppingGeneration_succ] at hr₁ hr₂
      obtain ⟨p₁, hp₁, q₁, hq₁, rfl⟩ := hr₁
      obtain ⟨p₂, hp₂, q₂, hq₂, rfl⟩ := hr₂
      by_cases hparent : p₁ = p₂
      · subst p₂
        have hqne : q₁ ≠ q₂ := by
          intro h
          exact hrne (by rw [h])
        rw [dyadicDescendant_append, dyadicDescendant_append]
        exact disjoint_dyadicDescendant_of_firstPrefixStop
          (dyadicDescendant I p₁) hq₁ hq₂ hqne
      · have hparents := ih hp₁ hp₂ hparent
        have hsub₁ : (dyadicDescendant I (p₁ ++ q₁) : Set (Vec d)) ⊆
            (dyadicDescendant I p₁ : Set (Vec d)) := by
          rw [dyadicDescendant_append]
          exact dyadicDescendant_le (dyadicDescendant I p₁) q₁
        have hsub₂ : (dyadicDescendant I (p₂ ++ q₂) : Set (Vec d)) ⊆
            (dyadicDescendant I p₂ : Set (Vec d)) := by
          rw [dyadicDescendant_append]
          exact dyadicDescendant_le (dyadicDescendant I p₂) q₂
        exact hparents.mono hsub₁ hsub₂

end PDE
