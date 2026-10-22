module

public import PDEFoundation.Analysis.Inequalities.JohnNirenberg.Stopping
public import PDEFoundation.Measure.DyadicBoxDifferentiation
public import PDEFoundation.Measure.DyadicChildAverage

/-!
# Local properties of one John–Nirenberg stopping generation

Items (ii) and (iii) of Step 1 of Lemma 1.16: off the first stops, `|v - (v)_P| ≤ lam`
almost everywhere (dyadic Lebesgue differentiation), and at a first stop the mean jumps by at
most `2 ^ d lam` (the parent is unselected).
-/

@[expose] public section

namespace PDE.JohnNirenberg

open BoxIntegral MeasureTheory Filter Set
open scoped ENNReal Topology

/-- Item (ii): off the first stops, `|v - (v)_P| ≤ lam` almost everywhere in `P`. -/
theorem ae_abs_sub_integralAverage_le_of_notMem_jnStopUnion {d : ℕ} (P : Box (Fin d))
    (hd : 0 < d) {v : Vec d → ℝ} (hv : IntegrableOn v (P : Set (Vec d))) (lam : ℝ) :
    ∀ᵐ x ∂volume.restrict (P : Set (Vec d)),
      x ∉ jnStopUnion P v lam → |v x - integralAverage (P : Set (Vec d)) v| ≤ lam := by
  set c := integralAverage (P : Set (Vec d)) v
  have hInt : IntegrableOn (fun y => |v y - c|) (P : Set (Vec d)) volume :=
    (hv.sub (integrableOn_const (P.measure_coe_lt_top volume).ne)).abs
  have hDiff := ae_tendsto_integralAverage_dyadicBoxAtDepth P hd hInt
  filter_upwards [hDiff, ae_restrict_mem P.measurableSet_coe] with x hxDiff hxP
  intro hxGood
  have hmeans : ∀ n : ℕ,
      integralAverage (dyadicBoxAtDepth P x hxP n : Set (Vec d)) (fun y => |v y - c|) ≤ lam := by
    intro n
    apply le_of_not_gt
    intro hgt
    have hbad : jnBad P v lam (dyadicPathAtDepth P x hxP n) := hgt
    obtain ⟨q, hqp, hqStop⟩ := exists_firstPrefixStop (jnBad P v lam) hbad
    exact hxGood (Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hqStop,
      dyadicDescendant_subset_of_isPrefix P hqp (mem_dyadicBoxAtDepth P x hxP n)⟩⟩)
  exact le_of_tendsto' (hxDiff hxP) hmeans

/-- Item (ii) simultaneously for every literal descendant of `I` taken as the root. -/
theorem ae_forall_abs_sub_integralAverage_le {d : ℕ} (I : Box (Fin d)) (hd : 0 < d)
    {v : Vec d → ℝ} (hv : IntegrableOn v (I : Set (Vec d))) (lam : ℝ) :
    ∀ᵐ x ∂volume, ∀ r : List (Set (Fin d)), x ∈ (dyadicDescendant I r : Set (Vec d)) →
      x ∉ jnStopUnion (dyadicDescendant I r) v lam →
        |v x - integralAverage (dyadicDescendant I r : Set (Vec d)) v| ≤ lam := by
  rw [ae_all_iff]
  intro r
  have hsub : (dyadicDescendant I r : Set (Vec d)) ⊆ (I : Set (Vec d)) :=
    dyadicDescendant_le I r
  exact (ae_restrict_iff' (measurableSet_dyadicDescendant I r)).mp
    (ae_abs_sub_integralAverage_le_of_notMem_jnStopUnion (dyadicDescendant I r) hd
      (hv.mono_set hsub) lam)

/-- Item (iii): at a first stop the mean moves by at most `2 ^ d lam`, provided the root
oscillation is at most `lam`. -/
theorem abs_integralAverage_sub_le_of_firstPrefixStop {d : ℕ} (P : Box (Fin d))
    {v : Vec d → ℝ} (hv : IntegrableOn v (P : Set (Vec d))) {lam : ℝ}
    (hroot : integralAverage (P : Set (Vec d))
      (fun x => |v x - integralAverage (P : Set (Vec d)) v|) ≤ lam)
    {q : List (Set (Fin d))} (hq : IsFirstPrefixStop (jnBad P v lam) q) :
    |integralAverage (dyadicDescendant P q : Set (Vec d)) v -
        integralAverage (P : Set (Vec d)) v| ≤ (2 : ℝ) ^ d * lam := by
  set c := integralAverage (P : Set (Vec d)) v
  have hInt : IntegrableOn (fun y => |v y - c|) (P : Set (Vec d)) volume :=
    (hv.sub (integrableOn_const (P.measure_coe_lt_top volume).ne)).abs
  have hrootGood : ¬jnBad P v lam [] := by
    unfold jnBad
    rw [dyadicDescendant_nil]
    exact not_lt_of_ge hroot
  have hqne : q ≠ [] := firstPrefixStop_ne_nil hrootGood hq
  set q' := q.dropLast
  set s := q.getLast hqne
  have hdecomp : q' ++ [s] = q := List.dropLast_append_getLast hqne
  have hq'prefix : q' <+: q := List.dropLast_prefix q
  have hq'ne : q' ≠ q := by
    intro h
    have hlen := congrArg List.length h
    have hpos : 0 < q.length := List.length_pos_iff.mpr hqne
    simp only [q', List.length_dropLast] at hlen
    omega
  have hparent : integralAverage (dyadicDescendant P q' : Set (Vec d)) (fun y => |v y - c|) ≤
      lam := le_of_not_gt (hq.2 q' hq'prefix hq'ne)
  have hparentSub : (dyadicDescendant P q' : Set (Vec d)) ⊆ (P : Set (Vec d)) :=
    dyadicDescendant_le P q'
  have hchild := integralAverage_splitCenterBox_le_pow_mul (dyadicDescendant P q') s
    (fun y => |v y - c|) (hInt.mono_set hparentSub) (ae_of_all _ fun y => abs_nonneg _)
  have hbox : dyadicDescendant P q = (dyadicDescendant P q').splitCenterBox s := by
    rw [← hdecomp, dyadicDescendant_append]
    rfl
  have hsub : (dyadicDescendant P q : Set (Vec d)) ⊆ (P : Set (Vec d)) :=
    dyadicDescendant_le P q
  have hQpos : 0 < volume (dyadicDescendant P q : Set (Vec d)) :=
    (ENNReal.toReal_pos_iff.mp (volume_box_toReal_pos (dyadicDescendant P q))).1
  have hjensen := abs_integralAverage_sub_le_integralAverage_abs_sub c (hv.mono_set hsub) hQpos
    (volume_dyadicDescendant_lt_top P q)
  calc
    |integralAverage (dyadicDescendant P q : Set (Vec d)) v - c| ≤
        integralAverage (dyadicDescendant P q : Set (Vec d)) (fun y => |v y - c|) := hjensen
    _ ≤ (2 : ℝ) ^ d *
        integralAverage (dyadicDescendant P q' : Set (Vec d)) (fun y => |v y - c|) := by
      rw [hbox]; exact hchild
    _ ≤ (2 : ℝ) ^ d * lam := mul_le_mul_of_nonneg_left hparent (by positivity)

end PDE.JohnNirenberg
