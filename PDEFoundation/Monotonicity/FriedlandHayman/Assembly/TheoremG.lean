module

public import PDEFoundation.Monotonicity.FriedlandHayman.Assembly.Eigen
public import PDEFoundation.Monotonicity.FriedlandHayman.Assembly.Tail
public import PDEFoundation.Monotonicity.FriedlandHayman.Assembly.DegreeLimit
public import PDEFoundation.Monotonicity.FriedlandHayman.Suspension.Main
public import PDEFoundation.Monotonicity.FriedlandHayman.Suspension.Measure
public import PDEFoundation.Monotonicity.FriedlandHayman.Gauss.BKP
public import PDEFoundation.Monotonicity.FriedlandHayman.Basic

/-!
# Friedland--Hayman: Theorem G and the disjoint inequality

Theorem G (`CH2_FH_CAP_PROOF.md` §2): for a measurable `Ω ⊆ S^{n-1}` missing a point of the
sphere with `|Ω| ≤ γ((t, ∞))`, `α(Ω) ≥ β(t)`. The proof suspends `Ω` into `S^{n+N-1}`, applies
the Gaussian lower bound there and lets `N → ∞`. Combined with the Beckner--Kenig--Pipher
inequality it gives the Friedland--Hayman inequality for disjoint relatively open sets.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE.FHLane

noncomputable section

theorem measurableSet_suspension {n N : ℕ} {Ω : Set (Vec n)} (hΩ : MeasurableSet Ω) :
    MeasurableSet (suspension n N Ω) := by
  have hp : Measurable (projFst : Vec (n + N) → Vec n) :=
    (continuous_pi fun i => continuous_apply _).measurable
  have hn : Measurable fun x : Vec (n + N) => vecEuclideanNorm (projFst x) :=
    continuous_vecEuclideanNorm.measurable.comp hp
  exact (isClosed_euclideanSphere (0 : Vec (n + N)) 1).measurableSet.inter
    (((measurableSet_singleton (0 : Vec n)).compl.preimage hp).inter
      (hΩ.preimage (hn.inv.smul hp)))

theorem suspension_subset_sphere {n N : ℕ} (Ω : Set (Vec n)) :
    suspension n N Ω ⊆ euclideanSphere (0 : Vec (n + N)) 1 := fun _ hx => hx.1

theorem sphFrac_suspension {n N : ℕ} [NeZero n] [NeZero N] {Ω : Set (Vec n)}
    (hΩ : MeasurableSet Ω) : sphFrac (n + N) (suspension n N Ω) = sphFrac n Ω := by
  unfold sphFrac
  rw [Set.inter_eq_left.2 (suspension_subset_sphere Ω)]
  exact suspension_measure hΩ

/-- Theorem G. -/
theorem ofReal_gaussBeta_le_eigenvalueDegree {n : ℕ} (hn : 2 ≤ n)
    {Ω : Set (Vec n)} (hΩ : MeasurableSet Ω)
    (hmiss : ∃ p ∈ euclideanSphere (0 : Vec n) 1, p ∉ Ω) {t : ℝ}
    (ht : sphFrac n Ω ≤ gaussTail t) :
    ENNReal.ofReal (gaussBeta t) ≤ eigenvalueDegree n (sphereDirichletEigenvalue n Ω) := by
  have : NeZero n := ⟨by omega⟩
  refine ofReal_le_of_degree_bound (n := n) (gaussBeta_nonneg t) fun N hN => ?_
  have : NeZero N := ⟨by omega⟩
  have hD : 3 ≤ n + N := by omega
  have hfrac : sphFrac (n + N) (suspension n N Ω) ≤ gaussTail t := by
    rw [sphFrac_suspension hΩ]
    exact ht
  have hlam := lambda_ge_gaussBeta hD (measurableSet_suspension hΩ) hfrac
  calc eigenvalueDegree (n + N) (ENNReal.ofReal ((((n + N : ℕ) : ℝ) - 2) * gaussBeta t))
      ≤ eigenvalueDegree (n + N) (sphereDirichletEigenvalue (n + N) (suspension n N Ω)) :=
        eigenvalueDegree_mono _ hlam
    _ ≤ eigenvalueDegree n (sphereDirichletEigenvalue n Ω) :=
        eigenvalueDegree_suspension_le hn hN hmiss

/-- The Friedland--Hayman inequality for disjoint relatively open subsets of the sphere. -/
theorem fh_of_disjoint (d : ℕ) (hd : 2 ≤ d) (Ωp Ωm : Set (Vec d))
    (hp : ∃ U : Set (Vec d), IsOpen U ∧ Ωp = U ∩ euclideanSphere (0 : Vec d) 1)
    (hm : ∃ U : Set (Vec d), IsOpen U ∧ Ωm = U ∩ euclideanSphere (0 : Vec d) 1)
    (hdisj : Disjoint Ωp Ωm) :
    2 ≤ eigenvalueDegree d (sphereDirichletEigenvalue d Ωp) +
      eigenvalueDegree d (sphereDirichletEigenvalue d Ωm) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Up, hUp, rfl⟩ := hp
  obtain ⟨Um, hUm, rfl⟩ := hm
  have hS := isClosed_euclideanSphere (0 : Vec d) 1
  -- empty cases
  rcases (Up ∩ euclideanSphere (0 : Vec d) 1).eq_empty_or_nonempty with hpe | hpne
  · rw [hpe, sphereDirichletEigenvalue_empty, eigenvalueDegree_top, top_add]
    exact le_top
  rcases (Um ∩ euclideanSphere (0 : Vec d) 1).eq_empty_or_nonempty with hme | hmne
  · rw [hme, sphereDirichletEigenvalue_empty, eigenvalueDegree_top, add_top]
    exact le_top
  have hmp : MeasurableSet (Up ∩ euclideanSphere (0 : Vec d) 1) :=
    hUp.measurableSet.inter hS.measurableSet
  have hmm : MeasurableSet (Um ∩ euclideanSphere (0 : Vec d) 1) :=
    hUm.measurableSet.inter hS.measurableSet
  have hfrac_eq : ∀ U : Set (Vec d),
      sphFrac d (U ∩ euclideanSphere (0 : Vec d) 1) = sphFrac d U := by
    intro U
    unfold sphFrac
    rw [Set.inter_assoc, Set.inter_self]
  have hpos : 0 < sphFrac d (Up ∩ euclideanSphere (0 : Vec d) 1) := by
    rw [hfrac_eq]
    exact sphFrac_pos hUp hpne
  have hdisjU : Disjoint (Up ∩ euclideanSphere (0 : Vec d) 1) Um := by
    rw [Set.disjoint_left]
    intro x hx hxU
    exact Set.disjoint_left.1 hdisj hx ⟨hxU, hx.2⟩
  have hlt : sphFrac d (Up ∩ euclideanSphere (0 : Vec d) 1) < 1 :=
    sphFrac_lt_one hmp hUm hmne hdisjU
  obtain ⟨t, ht⟩ := exists_gaussTail_eq ⟨hpos, hlt⟩
  have hsum := sphFrac_add_le hmp hmm hdisj
  have htm : sphFrac d (Um ∩ euclideanSphere (0 : Vec d) 1) ≤ gaussTail (-t) := by
    rw [gaussTail_neg, ht]
    linarith
  have hmissp : ∃ p ∈ euclideanSphere (0 : Vec d) 1, p ∉ Up ∩ euclideanSphere (0 : Vec d) 1 := by
    obtain ⟨q, hq⟩ := hmne
    exact ⟨q, hq.2, fun hqp => Set.disjoint_left.1 hdisj hqp hq⟩
  have hmissm : ∃ p ∈ euclideanSphere (0 : Vec d) 1, p ∉ Um ∩ euclideanSphere (0 : Vec d) 1 := by
    obtain ⟨q, hq⟩ := hpne
    exact ⟨q, hq.2, fun hqm => Set.disjoint_left.1 hdisj hq hqm⟩
  have hp' := ofReal_gaussBeta_le_eigenvalueDegree hd hmp hmissp ht.ge
  have hm' := ofReal_gaussBeta_le_eigenvalueDegree hd hmm hmissm htm
  have hbkp := gaussBeta_add_neg t
  calc (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    _ ≤ ENNReal.ofReal (gaussBeta t + gaussBeta (-t)) := ENNReal.ofReal_le_ofReal hbkp
    _ = ENNReal.ofReal (gaussBeta t) + ENNReal.ofReal (gaussBeta (-t)) :=
        ENNReal.ofReal_add (gaussBeta_nonneg t) (gaussBeta_nonneg (-t))
    _ ≤ _ := add_le_add hp' hm'

end

end PDE.FHLane

