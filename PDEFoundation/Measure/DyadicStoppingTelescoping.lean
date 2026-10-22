module

public import PDEFoundation.Measure.DyadicSparseRemainder
public import PDEFoundation.Measure.DyadicStoppingFiniteChains
public import PDEFoundation.Measure.DyadicStoppingMeanJump

/-! # Finite telescoping along dyadic stopping chains -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory Set

noncomputable section

/-- The square root of the quadratic mean oscillation on a literal dyadic
descendant. -/
def dyadicMeanOscillation {d m : ℕ} (I : Box (Fin d))
    (g : Vec d → Vec m) (p : List (Set (Fin d))) : ℝ :=
  Real.sqrt (integralAverage (dyadicDescendant I p : Set (Vec d))
    (fun x => vecNormSq
      (g x - coordinateVectorAverage (dyadicDescendant I p : Set (Vec d)) g)))

/-- Conditional finite stopping-chain domination. If pointwise recovery holds
on every local remainder containing `x`, then exiting after `N` further
generations bounds the oscillation at the starting path by a finite sum of
mean oscillations over paths in the actual sparse family. -/
theorem finite_stopping_domination_of_good_recovery
    {d m : ℕ} (I : Box (Fin d)) (g : Vec d → Vec m)
    (hg : ∀ i : Fin m,
      MemLp (fun y => g y i) 2 (volumeOn (I : Set (Vec d))))
    (x : Vec d)
    (hgood : ∀ r : List (Set (Fin d)),
      x ∈ (dyadicDescendant I r : Set (Vec d)) →
      x ∉ dyadicOscillationStopUnion (dyadicDescendant I r) g →
      vecEuclideanNorm
          (g x - coordinateVectorAverage (dyadicDescendant I r : Set (Vec d)) g) ≤
        2 * dyadicMeanOscillation I g r)
    (N k : ℕ) (p : List (Set (Fin d)))
    (hp : p ∈ dyadicStoppingGeneration I g k)
    (hxp : x ∈ (dyadicDescendant I p : Set (Vec d)))
    (hxout : x ∉ dyadicStoppingRegion I g (k + N)) :
    ∃ T : Finset (List (Set (Fin d))),
      (∀ r ∈ T, r ∈ dyadicSparseFamily I g ∧
        x ∈ (dyadicDescendant I r : Set (Vec d)) ∧ p.length ≤ r.length) ∧
      vecEuclideanNorm
          (g x - coordinateVectorAverage (dyadicDescendant I p : Set (Vec d)) g) ≤
        (2 : ℝ) ^ (1 + (d : ℝ) / 2) * ∑ r ∈ T, dyadicMeanOscillation I g r := by
  classical
  induction N generalizing k p with
  | zero =>
      exfalso
      apply hxout
      simpa only [Nat.add_zero, dyadicStoppingRegion] using
        Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hxp⟩
  | succ N ih =>
      let C : ℝ := (2 : ℝ) ^ (1 + (d : ℝ) / 2)
      by_cases hxstop : x ∈ dyadicOscillationStopUnion (dyadicDescendant I p) g
      · obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hxstop
        obtain ⟨hq, hxq⟩ := Set.mem_iUnion.mp hxq
        let p' := p ++ q
        have hp' : p' ∈ dyadicStoppingGeneration I g (k + 1) := by
          rw [mem_dyadicStoppingGeneration_succ]
          exact ⟨p, hp, q, hq, rfl⟩
        have hxp' : x ∈ (dyadicDescendant I p' : Set (Vec d)) := by
          simpa only [p', dyadicDescendant_append] using hxq
        have hxout' : x ∉ dyadicStoppingRegion I g ((k + 1) + N) := by
          simpa only [Nat.add_assoc, Nat.add_comm N 1] using hxout
        obtain ⟨T, hT, hbound⟩ := ih (k + 1) p' hp' hxp' hxout'
        have hqne : q ≠ [] :=
          firstPrefixStop_dyadicOscillationBad_ne_nil (dyadicDescendant I p) g hq
        have hplen : p.length < p'.length := by
          simp only [p', List.length_append]
          exact Nat.lt_add_of_pos_right (List.length_pos_iff.mpr hqne)
        have hpnot : p ∉ T := by
          intro hpT
          have := (hT p hpT).2.2
          omega
        refine ⟨insert p T, ?_, ?_⟩
        · intro r hr
          rcases Finset.mem_insert.mp hr with rfl | hr
          · exact ⟨⟨k, hp⟩, hxp, le_rfl⟩
          · obtain ⟨hrfam, hxr, hlen⟩ := hT r hr
            exact ⟨hrfam, hxr, hplen.le.trans hlen⟩
        · have hsub : (dyadicDescendant I p : Set (Vec d)) ⊆ (I : Set (Vec d)) :=
            dyadicDescendant_le I p
          have hg' : ∀ i : Fin m, MemLp (fun y => g y i) 2
              (volumeOn (dyadicDescendant I p : Set (Vec d))) := fun i =>
            (hg i).mono_measure (Measure.restrict_mono hsub le_rfl)
          have hjump : vecEuclideanNorm
              (coordinateVectorAverage (dyadicDescendant I p' : Set (Vec d)) g -
                coordinateVectorAverage (dyadicDescendant I p : Set (Vec d)) g) ≤
              C * dyadicMeanOscillation I g p := by
            simpa only [C, p', dyadicDescendant_append, dyadicMeanOscillation,
              dyadicOscillationBad] using
              vecEuclideanNorm_coordinateVectorAverage_firstPrefixStop_le
                (dyadicDescendant I p) g hg' q hq
          have hdecomp :
              g x - coordinateVectorAverage (dyadicDescendant I p : Set (Vec d)) g =
                (g x - coordinateVectorAverage (dyadicDescendant I p' : Set (Vec d)) g) +
                (coordinateVectorAverage (dyadicDescendant I p' : Set (Vec d)) g -
                  coordinateVectorAverage (dyadicDescendant I p : Set (Vec d)) g) := by
            module
          calc
            vecEuclideanNorm
                (g x - coordinateVectorAverage (dyadicDescendant I p : Set (Vec d)) g) =
                vecEuclideanNorm
                  ((g x - coordinateVectorAverage (dyadicDescendant I p' : Set (Vec d)) g) +
                    (coordinateVectorAverage (dyadicDescendant I p' : Set (Vec d)) g -
                      coordinateVectorAverage (dyadicDescendant I p : Set (Vec d)) g)) := by rw [hdecomp]
            _ ≤ vecEuclideanNorm
                  (g x - coordinateVectorAverage (dyadicDescendant I p' : Set (Vec d)) g) +
                vecEuclideanNorm
                  (coordinateVectorAverage (dyadicDescendant I p' : Set (Vec d)) g -
                    coordinateVectorAverage (dyadicDescendant I p : Set (Vec d)) g) :=
              vecEuclideanNorm_add_le _ _
            _ ≤ C * (∑ r ∈ T, dyadicMeanOscillation I g r) +
                C * dyadicMeanOscillation I g p := add_le_add hbound hjump
            _ = C * ∑ r ∈ insert p T, dyadicMeanOscillation I g r := by
              rw [Finset.sum_insert hpnot]
              ring
      · refine ⟨{p}, ?_, ?_⟩
        · intro r hr
          simp only [Finset.mem_singleton] at hr
          subst r
          exact ⟨⟨k, hp⟩, hxp, le_rfl⟩
        · have hC : 2 ≤ C := by
            rw [show C = 2 * (2 : ℝ) ^ ((d : ℝ) / 2) by
              simp only [C, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]]
            exact le_mul_of_one_le_right (by norm_num)
              (Real.one_le_rpow (by norm_num) (by positivity))
          have he : 0 ≤ dyadicMeanOscillation I g p := Real.sqrt_nonneg _
          simpa only [Finset.sum_singleton, mul_assoc] using
            (hgood p hxp hxstop).trans (mul_le_mul_of_nonneg_right hC he)

end

end PDE
