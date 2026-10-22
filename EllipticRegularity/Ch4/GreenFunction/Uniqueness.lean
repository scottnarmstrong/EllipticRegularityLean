module

public import PDEFoundation
public import EllipticRegularity.Green.GreenFunctionDef

/-!
# Uniqueness of the Green function (Step 1 of Proposition 4.40)

Given solvability of the adjoint Dirichlet problem for `L²` sources (interface hypothesis
`hEx`, to be instantiated with `greenDirichlet_full`), two Green functions agree a.e.
-/

@[expose] public section

namespace PDE.Ch4Green

open MeasureTheory PDE

variable {d : ℕ}

/-- Two Green functions coincide a.e. on `B_R`, given adjoint Dirichlet solvability. -/
theorem green_unique_of_solvable (hd : 0 < d) {R : ℝ} (hR : 0 < R) {a : CoeffField d}
    (hEx : ∀ g : Vec d → ℝ, MemL2On (euclideanBall (0 : Vec d) R) g →
      ∃ v : H10Function (euclideanBall (0 : Vec d) R),
        IsWeakDivergenceFormH10SolutionOn (adjointCoeffField a) (euclideanBall (0 : Vec d) R)
          v.toH1Function g (0 : Vec d → Vec d))
    {G G' : Vec d → ℝ} (hG : IsGreenFunction a R G) (hG' : IsGreenFunction a R G') :
    G =ᵐ[volumeOn (euclideanBall (0 : Vec d) R)] G' := by
  obtain ⟨-, hGL, hGd⟩ := hG
  obtain ⟨-, hGL', hGd'⟩ := hG'
  set B := euclideanBall (0 : Vec d) R with hB
  have hBm : MeasurableSet B := measurableSet_euclideanBall _ _
  have key : ∀ ε : ℝ, 0 < ε → ε < R →
      ∀ᵐ x ∂(volumeOn (B \ euclideanBall (0 : Vec d) ε)), G x = G' x := by
    intro ε hε hεR
    set S := B \ euclideanBall (0 : Vec d) ε with hS
    have hSm : MeasurableSet S := hBm.diff (measurableSet_euclideanBall _ _)
    have hSB : S ⊆ B := Set.sdiff_subset
    have hL : MemLpOn S (2 : ENNReal) (fun x => G x - G' x) :=
      (hGL ε hε hεR).sub (hGL' ε hε hεR)
    have hgL : MemL2On B (S.indicator (fun x => G x - G' x)) := by
      refine (memLp_indicator_iff_restrict (μ := volume.restrict B) hSm
        (f := fun x => G x - G' x) (p := 2)).2 ?_
      unfold MemLpOn at hL
      rwa [Measure.restrict_restrict hSm, Set.inter_eq_left.2 hSB]
    have hg0 : ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) ε)),
        S.indicator (fun x => G x - G' x) x = 0 := by
      refine (ae_restrict_iff' (measurableSet_euclideanBall _ _)).2
        (Filter.Eventually.of_forall ?_)
      intro x hx
      exact Set.indicator_of_notMem (fun h => h.2 hx) _
    obtain ⟨v, hv⟩ := hEx _ hgL
    have heq := tendsto_nhds_unique (hGd ε hε hεR _ hgL hg0 v hv) (hGd' ε hε hεR _ hgL hg0 v hv)
    have intB : ∀ H : Vec d → ℝ, ∫ x in B, H x * S.indicator (fun x => G x - G' x) x
        = ∫ x in S, H x * (G x - G' x) := by
      intro H
      have : ∀ x, H x * S.indicator (fun x => G x - G' x) x
          = S.indicator (fun x => H x * (G x - G' x)) x := by
        intro x
        by_cases hx : x ∈ S <;> simp [hx]
      simp_rw [this]
      rw [integral_indicator hSm, Measure.restrict_restrict hSm, Set.inter_eq_left.2 hSB]
    have hI : ∀ H : Vec d → ℝ, MemLpOn S (2 : ENNReal) H →
        Integrable (fun x => H x * (G x - G' x)) (volume.restrict S) := fun H hH =>
      MemLp.integrable_mul (p := 2) (q := 2) hH hL
    have hint : ∫ x in S, (G x - G' x) ^ 2 = 0 := by
      have e := sub_eq_zero.2 heq
      rw [intB, intB, ← integral_sub (hI G (hGL ε hε hεR)) (hI G' (hGL' ε hε hεR))] at e
      rw [← e]
      congr 1; ext x; ring
    have hint2 : Integrable (fun x => (G x - G' x) ^ 2) (volume.restrict S) := hL.integrable_sq
    have := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hint2).1 hint
    filter_upwards [this] with x hx
    have : (G x - G' x) ^ 2 = 0 := hx
    linarith [pow_eq_zero_iff (two_ne_zero) |>.1 this]
  have hcov : B ⊆ {0} ∪ ⋃ n : ℕ, B \ euclideanBall (0 : Vec d) (R / (n + 2)) := by
    intro x hx
    by_cases h0 : x = 0
    · exact Or.inl h0
    · refine Or.inr (Set.mem_iUnion.2 ?_)
      have hpos : 0 < vecEuclideanNorm x := vecEuclideanNorm_pos_iff.mpr h0
      obtain ⟨n, hn⟩ := exists_nat_gt (R / vecEuclideanNorm x)
      refine ⟨n, hx, fun hin => ?_⟩
      have hRn : 0 < R / ((n : ℝ) + 2) := by positivity
      have := (mem_euclideanBall_iff_vecEuclideanNorm_lt hRn).1 hin
      rw [sub_zero, lt_div_iff₀ (by positivity)] at this
      rw [div_lt_iff₀ hpos] at hn
      nlinarith
  have hnull : volume ({0} : Set (Vec d)) = 0 := by
    have : NeZero d := ⟨hd.ne'⟩
    exact measure_singleton _
  refine ae_restrict_of_ae_restrict_of_subset hcov ?_
  rw [ae_restrict_union_iff]
  refine ⟨?_, ?_⟩
  · rw [Measure.restrict_eq_zero.2 hnull]; simp
  · rw [ae_restrict_iUnion_iff]
    intro n
    have hRn : 0 < R / ((n : ℝ) + 2) := by positivity
    refine key _ hRn ?_
    rw [div_lt_iff₀ (by positivity)]
    nlinarith

end PDE.Ch4Green
