module

public import PDEFoundation.Analysis.Newtonian.WeakType.DecompositionStoppingAvg
public import PDEFoundation.Measure.EuclideanVectorIntegral
public import PDEFoundation.Geometry.BoxCenter

/-! # The Calderón–Zygmund stopping cubes

For `F : Vec d → Vec d` integrable on a dyadic equal-side box `I` and a height
`λ > ⨍_I |F|`, the first-stop dyadic subcubes of `I` for `|F|` form a countable family of
pairwise disjoint boxes with `λ < ⨍_Q |F| ≤ 2^d λ`, total volume at most `‖F‖₁ / λ`, and
`|F| ≤ λ` almost everywhere on `I` off their union.
-/

@[expose] public section

open BoxIntegral MeasureTheory Set Filter
open scoped ENNReal Topology Function

namespace PDE.NewtonWeakType

noncomputable section

variable {d : ℕ}

/-- The stopping cubes of the Calderón–Zygmund decomposition of `F` in the box `I` at height
`lam`: a countable family of pairwise disjoint equal-side dyadic subboxes. -/
structure CZStopping (I : Box (Fin d)) (F : Vec d → Vec d) (lam : ℝ) where
  /-- The countable index type of the stopping cubes. -/
  ι : Type
  /-- The index type is countable. -/
  countable : Countable ι
  /-- The stopping cubes. -/
  cube : ι → Box (Fin d)
  /-- The (common coordinate) side of each stopping cube. -/
  side : ι → ℝ
  lam_pos : 0 < lam
  le_root : ∀ k, cube k ≤ I
  pairwise_disjoint : Pairwise (Disjoint on fun k => (cube k : Set (Vec d)))
  side_pos : ∀ k, 0 < side k
  width : ∀ k i, (cube k).upper i - (cube k).lower i = side k
  avg_gt : ∀ k, lam < integralAverage (cube k : Set (Vec d)) fun x => vecEuclideanNorm (F x)
  avg_le : ∀ k, integralAverage (cube k : Set (Vec d)) (fun x => vecEuclideanNorm (F x)) ≤
    2 ^ d * lam
  tsum_volume_le : ENNReal.ofReal lam * ∑' k, volume (cube k : Set (Vec d)) ≤
    ∫⁻ x in (I : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (F x))
  ae_le : ∀ᵐ x ∂(volume : Measure (Vec d)),
    x ∈ (I : Set (Vec d)) → (∀ k, x ∉ (cube k : Set (Vec d))) → vecEuclideanNorm (F x) ≤ lam

attribute [instance] CZStopping.countable

/-- **Existence of the Calderón–Zygmund stopping cubes.** -/
theorem exists_czStopping (hd : 0 < d) (I : Box (Fin d)) (L : ℝ)
    (hwidth : ∀ i, I.upper i - I.lower i = L) {F : Vec d → Vec d}
    (hF : ∀ i, IntegrableOn (fun x => F x i) (I : Set (Vec d))) {lam : ℝ}
    (hlam : integralAverage (I : Set (Vec d)) (fun x => vecEuclideanNorm (F x)) < lam) :
    Nonempty (CZStopping I F lam) := by
  classical
  set b : Vec d → ℝ := fun x => vecEuclideanNorm (F x) with hbdef
  have hb : IntegrableOn b (I : Set (Vec d)) :=
    integrable_vecEuclideanNorm_of_coord (μ := volume.restrict (I : Set (Vec d))) F hF
  have hb0 : ∀ x, 0 ≤ b x := fun x => vecEuclideanNorm_nonneg _
  have hlam0 : 0 ≤ lam :=
    (integralAverage_nonneg I.measurableSet_coe (fun x _ => hb0 x)).trans hlam.le
  have hroot : ¬ ENNReal.ofReal lam < dyadicBoxAverage I b [] := by
    rw [dyadicBoxAverage_eq_ofReal_integralAverage I hb hb0 [], not_lt,
      ENNReal.ofReal_le_ofReal_iff (by linarith [hlam0])]
    exact hlam.le
  have hL : 0 < L := by
    rw [← hwidth ⟨0, hd⟩]
    exact sub_pos.mpr (I.lower_lt_upper _)
  let bad : List (Set (Fin d)) → Prop := fun p => ENNReal.ofReal lam < dyadicBoxAverage I b p
  let S := {p : List (Set (Fin d)) // IsFirstPrefixStop bad p}
  let P : S → Set (Vec d) := fun p => (dyadicDescendant I p.1 : Set (Vec d))
  have hmeas (p : S) : MeasurableSet (P p) := measurableSet_dyadicDescendant I p.1
  have hdisj : Pairwise (Disjoint on P) := by
    intro p q hpq
    exact disjoint_dyadicDescendant_of_firstPrefixStop I p.2 q.2 (Subtype.coe_ne_coe.mpr hpq)
  have hlevel : {x | ENNReal.ofReal lam < dyadicBoxMaximal I b x} = ⋃ p : S, P p := by
    rw [set_lt_dyadicBoxMaximal_eq_firstStops]
    ext x
    simp only [mem_iUnion, P, S, bad]
    constructor
    · rintro ⟨p, hp, hxp⟩
      exact ⟨⟨p, hp⟩, hxp⟩
    · rintro ⟨p, hxp⟩
      exact ⟨p.1, p.2, hxp⟩
  refine ⟨{
    ι := S
    countable := inferInstance
    cube := fun p => dyadicDescendant I p.1
    side := fun p => L / 2 ^ p.1.length
    lam_pos := (integralAverage_nonneg I.measurableSet_coe (fun x _ => hb0 x)).trans_lt hlam
    le_root := fun p => dyadicDescendant_le I p.1
    pairwise_disjoint := hdisj
    side_pos := fun p => by positivity
    width := fun p i => upper_sub_lower_dyadicDescendant_of_commonWidth I L hwidth p.1 i
    avg_gt := fun p => lt_integralAverage_of_bad I hb hb0 p.2.1
    avg_le := fun p => integralAverage_firstStop_le I hb hb0 hlam0 hroot p.2
    tsum_volume_le := ?_
    ae_le := ?_ }⟩
  · have hweak := ofReal_mul_volume_set_lt_dyadicBoxMaximal_le_lintegral I b lam
    rw [hlevel, measure_iUnion hdisj hmeas] at hweak
    refine hweak.trans ?_
    have hsub : (⋃ p : S, P p) ⊆ (I : Set (Vec d)) :=
      iUnion_subset fun p => dyadicDescendant_subset_root I p.1
    refine (lintegral_mono_set hsub).trans (le_of_eq ?_)
    apply lintegral_congr
    intro x
    simp only [b, abs_of_nonneg (vecEuclideanNorm_nonneg _)]
  · have hdiff := ae_tendsto_integralAverage_dyadicBoxAtDepth I hd hb
    rw [ae_restrict_iff' I.measurableSet_coe] at hdiff
    filter_upwards [hdiff] with x hx hxI hxn
    have hnot : ∀ n, integralAverage (dyadicBoxAtDepth I x hxI n : Set (Vec d)) b ≤ lam := by
      intro n
      have hnb : ¬ bad (dyadicPathAtDepth I x hxI n) := by
        intro hbad
        obtain ⟨q, hqp, hq⟩ := exists_firstPrefixStop bad hbad
        apply hxn ⟨q, hq⟩
        exact dyadicDescendant_subset_of_isPrefix I hqp (mem_dyadicBoxAtDepth I x hxI n)
      exact integralAverage_le_of_not_bad I hb hb0 hlam0 hnb
    exact le_of_tendsto' (hx hxI hxI) hnot

end

end PDE.NewtonWeakType
