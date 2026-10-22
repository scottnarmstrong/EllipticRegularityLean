module

public import PDEFoundation.Measure.DyadicChildAverage
public import PDEFoundation.Measure.FiniteVectorAverageJensen
public import PDEFoundation.Geometry.FirstDyadicStop

/-! # Mean jump at a first dyadic stopping descendant -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory
open scoped ENNReal

/-- At a first stopping descendant, the squared jump of the vector mean is
bounded by the exact child amplification of the stopping threshold. -/
theorem vecNormSq_coordinateVectorAverage_firstPrefixStop_le
    {d m : ℕ} (I : Box (Fin d)) (g : Vec d → Vec m)
    (hg : ∀ i : Fin m, MemLp (fun x => g x i) 2 (volumeOn (I : Set (Vec d))))
    (p : List (Set (Fin d)))
    (hp : IsFirstPrefixStop
      (fun q => integralAverage (dyadicDescendant I q : Set (Vec d))
        (fun x => vecNormSq (g x - coordinateVectorAverage (I : Set (Vec d)) g)) >
          4 * integralAverage (I : Set (Vec d))
            (fun x => vecNormSq (g x - coordinateVectorAverage (I : Set (Vec d)) g))) p) :
    vecNormSq (coordinateVectorAverage (dyadicDescendant I p : Set (Vec d)) g -
        coordinateVectorAverage (I : Set (Vec d)) g) ≤
      (2 : ℝ) ^ d *
        (4 * integralAverage (I : Set (Vec d))
          (fun x => vecNormSq (g x - coordinateVectorAverage (I : Set (Vec d)) g))) := by
  let c := coordinateVectorAverage (I : Set (Vec d)) g
  let e2 := integralAverage (I : Set (Vec d)) (fun x => vecNormSq (g x - c))
  let bad : List (Set (Fin d)) → Prop := fun q =>
    integralAverage (dyadicDescendant I q : Set (Vec d))
      (fun x => vecNormSq (g x - c)) > 4 * e2
  have hp' : IsFirstPrefixStop bad p := by simpa [bad, e2, c] using hp
  have hItop : volume (I : Set (Vec d)) < ∞ := I.measure_coe_lt_top volume
  have hIpos : 0 < volume (I : Set (Vec d)) := by
    apply (ENNReal.toReal_pos_iff.mp ?_).1
    rw [Box.volume_apply']
    exact Finset.prod_pos fun i _ => sub_pos.mpr (I.lower_lt_upper i)
  have he2 : 0 ≤ e2 := integralAverage_nonneg I.measurableSet_coe
    (fun x _ => vecNormSq_nonneg _)
  have hroot : ¬bad [] := by
    dsimp [bad]
    change ¬e2 > 4 * e2
    exact not_lt_of_ge (by linarith)
  have hpne : p ≠ [] := firstPrefixStop_ne_nil hroot hp'
  let q := p.dropLast
  let s := p.getLast hpne
  have hpdecomp : q ++ [s] = p := List.dropLast_append_getLast hpne
  have hqprefix : q <+: p := List.dropLast_prefix p
  have hqne : q ≠ p := by
    intro hqp
    have := congrArg List.length hqp
    have hplen : 0 < p.length := List.length_pos_iff.mpr hpne
    simp only [q, List.length_dropLast] at this
    omega
  have hqgood : ¬bad q := hp'.2 q hqprefix hqne
  have hparent : integralAverage (dyadicDescendant I q : Set (Vec d))
      (fun x => vecNormSq (g x - c)) ≤ 4 * e2 := le_of_not_gt hqgood
  have hIntRoot : IntegrableOn (fun x => vecNormSq (g x - c))
      (I : Set (Vec d)) volume :=
    integrableOn_vecNormSq_sub_const_of_coordinate_memLp hg hItop c
  have hparentSub : (dyadicDescendant I q : Set (Vec d)) ⊆ (I : Set (Vec d)) :=
    dyadicDescendant_le I q
  have hchild : integralAverage
      ((dyadicDescendant I q).splitCenterBox s : Set (Vec d))
        (fun x => vecNormSq (g x - c)) ≤
      (2 : ℝ) ^ d * integralAverage (dyadicDescendant I q : Set (Vec d))
        (fun x => vecNormSq (g x - c)) :=
    integralAverage_splitCenterBox_le_pow_mul (dyadicDescendant I q) s _
      (hIntRoot.mono_set hparentSub)
      (ae_of_all _ fun x => vecNormSq_nonneg _)
  have hbox : dyadicDescendant I p = (dyadicDescendant I q).splitCenterBox s := by
    rw [← hpdecomp, dyadicDescendant_append]
    rfl
  have hchildBound : integralAverage (dyadicDescendant I p : Set (Vec d))
      (fun x => vecNormSq (g x - c)) ≤ (2 : ℝ) ^ d * (4 * e2) := by
    rw [hbox]
    exact hchild.trans (mul_le_mul_of_nonneg_left hparent (by positivity))
  have hsub : (dyadicDescendant I p : Set (Vec d)) ⊆ (I : Set (Vec d)) :=
    dyadicDescendant_le I p
  have hgChild : ∀ i : Fin m,
      MemLp (fun x => g x i) 2 (volumeOn (dyadicDescendant I p : Set (Vec d))) := by
    intro i
    exact (hg i).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hQpos : 0 < volume (dyadicDescendant I p : Set (Vec d)) := by
    apply (ENNReal.toReal_pos_iff.mp ?_).1
    rw [Box.volume_apply']
    exact Finset.prod_pos fun i _ =>
      sub_pos.mpr ((dyadicDescendant I p).lower_lt_upper i)
  have hQtop := volume_dyadicDescendant_lt_top I p
  have hjensen := vecNormSq_coordinateVectorAverage_sub_le_integralAverage
    hgChild hQpos hQtop c
  simpa [c, e2] using hjensen.trans hchildBound

/-- Square root form of the first-stop mean jump, with the source constant
`2 ^ (1 + d / 2)`. -/
theorem vecEuclideanNorm_coordinateVectorAverage_firstPrefixStop_le
    {d m : ℕ} (I : Box (Fin d)) (g : Vec d → Vec m)
    (hg : ∀ i : Fin m, MemLp (fun x => g x i) 2 (volumeOn (I : Set (Vec d))))
    (p : List (Set (Fin d)))
    (hp : IsFirstPrefixStop
      (fun q => integralAverage (dyadicDescendant I q : Set (Vec d))
        (fun x => vecNormSq (g x - coordinateVectorAverage (I : Set (Vec d)) g)) >
          4 * integralAverage (I : Set (Vec d))
            (fun x => vecNormSq (g x - coordinateVectorAverage (I : Set (Vec d)) g))) p) :
    vecEuclideanNorm (coordinateVectorAverage (dyadicDescendant I p : Set (Vec d)) g -
        coordinateVectorAverage (I : Set (Vec d)) g) ≤
      (2 : ℝ) ^ (1 + (d : ℝ) / 2) *
        Real.sqrt (integralAverage (I : Set (Vec d))
          (fun x => vecNormSq (g x - coordinateVectorAverage (I : Set (Vec d)) g))) := by
  unfold vecEuclideanNorm
  let E := integralAverage (I : Set (Vec d))
    (fun x => vecNormSq (g x - coordinateVectorAverage (I : Set (Vec d)) g))
  have h := Real.sqrt_le_sqrt
    (vecNormSq_coordinateVectorAverage_firstPrefixStop_le I g hg p hp)
  change Real.sqrt (vecNormSq _) ≤ (2 : ℝ) ^ (1 + (d : ℝ) / 2) * Real.sqrt E
  change Real.sqrt (vecNormSq _) ≤ Real.sqrt ((2 : ℝ) ^ d * (4 * E)) at h
  refine h.trans_eq ?_
  rw [Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ) ^ d), Real.sqrt_mul (by norm_num)]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  ring_nf

end PDE
