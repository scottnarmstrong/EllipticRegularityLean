module

public import PDEFoundation.Geometry.FirstDyadicStop
public import PDEFoundation.Sobolev.Mean

/-!
# John–Nirenberg stopping generations

For the John–Nirenberg inequality on cubes (Lemma 1.16), a literal dyadic descendant of
a root box `P` is selected when the average of `|v - (v)_P|` over it exceeds a threshold `lam`.
The first stopping descendants form one generation (the family `𝒮(P)` of the manuscript);
recursive generations `𝒢ₘ` append the first stops of every current root.
-/

@[expose] public section

namespace PDE.JohnNirenberg

open BoxIntegral MeasureTheory Set

/-- The John–Nirenberg stopping predicate relative to the root box `P`: the average of
`|v - (v)_P|` over the descendant along `q` exceeds `lam`. -/
def jnBad {d : ℕ} (P : Box (Fin d)) (v : Vec d → ℝ) (lam : ℝ) (q : List (Set (Fin d))) :
    Prop :=
  lam < integralAverage (dyadicDescendant P q : Set (Vec d))
    (fun x => |v x - integralAverage (P : Set (Vec d)) v|)

/-- The union of the first stopping descendants of the root `P`. -/
def jnStopUnion {d : ℕ} (P : Box (Fin d)) (v : Vec d → ℝ) (lam : ℝ) : Set (Vec d) :=
  ⋃ q : List (Set (Fin d)), ⋃ (_ : IsFirstPrefixStop (jnBad P v lam) q),
    (dyadicDescendant P q : Set (Vec d))

/-- Recursive stopping generations: generation zero is the root path; generation `n + 1`
appends to every path of generation `n` each first stop relative to that descendant. -/
def jnGeneration {d : ℕ} (I : Box (Fin d)) (v : Vec d → ℝ) (lam : ℝ) :
    ℕ → Set (List (Set (Fin d)))
  | 0 => {[]}
  | n + 1 => {r | ∃ p ∈ jnGeneration I v lam n,
      ∃ q, IsFirstPrefixStop (jnBad (dyadicDescendant I p) v lam) q ∧ r = p ++ q}

/-- The union of the descendants in generation `n`. -/
def jnRegion {d : ℕ} (I : Box (Fin d)) (v : Vec d → ℝ) (lam : ℝ) (n : ℕ) : Set (Vec d) :=
  ⋃ p : {p // p ∈ jnGeneration I v lam n}, (dyadicDescendant I p.1 : Set (Vec d))

@[simp]
theorem mem_jnGeneration_zero {d : ℕ} (I : Box (Fin d)) (v : Vec d → ℝ) (lam : ℝ)
    (p : List (Set (Fin d))) : p ∈ jnGeneration I v lam 0 ↔ p = [] :=
  Iff.rfl

theorem mem_jnGeneration_succ {d : ℕ} (I : Box (Fin d)) (v : Vec d → ℝ) (lam : ℝ) (n : ℕ)
    (r : List (Set (Fin d))) :
    r ∈ jnGeneration I v lam (n + 1) ↔
      ∃ p ∈ jnGeneration I v lam n,
        ∃ q, IsFirstPrefixStop (jnBad (dyadicDescendant I p) v lam) q ∧ r = p ++ q :=
  Iff.rfl

theorem measurableSet_jnStopUnion {d : ℕ} (P : Box (Fin d)) (v : Vec d → ℝ) (lam : ℝ) :
    MeasurableSet (jnStopUnion P v lam) :=
  MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
    measurableSet_dyadicDescendant P q

theorem jnStopUnion_subset {d : ℕ} (P : Box (Fin d)) (v : Vec d → ℝ) (lam : ℝ) :
    jnStopUnion P v lam ⊆ (P : Set (Vec d)) := by
  intro x hx
  obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx
  obtain ⟨_, hxq⟩ := Set.mem_iUnion.mp hq
  exact dyadicDescendant_le P q hxq

theorem measurableSet_jnRegion {d : ℕ} (I : Box (Fin d)) (v : Vec d → ℝ) (lam : ℝ) (n : ℕ) :
    MeasurableSet (jnRegion I v lam n) :=
  MeasurableSet.iUnion fun p => measurableSet_dyadicDescendant I p.1

@[simp]
theorem jnRegion_zero {d : ℕ} (I : Box (Fin d)) (v : Vec d → ℝ) (lam : ℝ) :
    jnRegion I v lam 0 = (I : Set (Vec d)) := by
  ext x
  simp [jnRegion]

theorem mem_jnRegion_of_mem {d : ℕ} {I : Box (Fin d)} {v : Vec d → ℝ} {lam : ℝ} {n : ℕ}
    {p : List (Set (Fin d))} (hp : p ∈ jnGeneration I v lam n) {x : Vec d}
    (hx : x ∈ (dyadicDescendant I p : Set (Vec d))) : x ∈ jnRegion I v lam n :=
  Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hx⟩

/-- Descendants of one recursive generation are pairwise disjoint. -/
theorem pairwiseDisjoint_jnGeneration {d : ℕ} (I : Box (Fin d)) (v : Vec d → ℝ) (lam : ℝ)
    (n : ℕ) :
    (jnGeneration I v lam n).Pairwise
      (fun p q => Disjoint (dyadicDescendant I p : Set (Vec d))
        (dyadicDescendant I q : Set (Vec d))) := by
  induction n with
  | zero =>
      intro p hp q hq hpq
      simp only [mem_jnGeneration_zero] at hp hq
      exact (hpq (hp.trans hq.symm)).elim
  | succ n ih =>
      intro r₁ hr₁ r₂ hr₂ hrne
      rw [mem_jnGeneration_succ] at hr₁ hr₂
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
      · have hsub₁ : (dyadicDescendant I (p₁ ++ q₁) : Set (Vec d)) ⊆
            (dyadicDescendant I p₁ : Set (Vec d)) := by
          rw [dyadicDescendant_append]
          exact dyadicDescendant_le (dyadicDescendant I p₁) q₁
        have hsub₂ : (dyadicDescendant I (p₂ ++ q₂) : Set (Vec d)) ⊆
            (dyadicDescendant I p₂ : Set (Vec d)) := by
          rw [dyadicDescendant_append]
          exact dyadicDescendant_le (dyadicDescendant I p₂) q₂
        exact (ih hp₁ hp₂ hparent).mono hsub₁ hsub₂

/-- The next generation's region is covered by the first stops of the current roots. -/
theorem jnRegion_succ_subset_iUnion {d : ℕ} (I : Box (Fin d)) (v : Vec d → ℝ) (lam : ℝ)
    (n : ℕ) :
    jnRegion I v lam (n + 1) ⊆
      ⋃ p : {p // p ∈ jnGeneration I v lam n}, jnStopUnion (dyadicDescendant I p.1) v lam := by
  intro x hx
  obtain ⟨r, hxr⟩ := Set.mem_iUnion.mp hx
  obtain ⟨p, hp, q, hq, hr⟩ := (mem_jnGeneration_succ I v lam n r.1).mp r.2
  refine Set.mem_iUnion.mpr ⟨⟨p, hp⟩, Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq, ?_⟩⟩⟩
  rwa [hr, dyadicDescendant_append] at hxr

theorem jnRegion_succ_subset {d : ℕ} (I : Box (Fin d)) (v : Vec d → ℝ) (lam : ℝ) (n : ℕ) :
    jnRegion I v lam (n + 1) ⊆ jnRegion I v lam n := by
  intro x hx
  obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp (jnRegion_succ_subset_iUnion I v lam n hx)
  exact Set.mem_iUnion.mpr ⟨p, jnStopUnion_subset _ v lam hxp⟩

end PDE.JohnNirenberg
