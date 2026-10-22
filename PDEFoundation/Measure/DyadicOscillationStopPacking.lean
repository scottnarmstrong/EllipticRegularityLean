module

public import PDEFoundation.Measure.DyadicFirstStopPacking
public import PDEFoundation.Measure.DyadicBoxMaximalZero
public import PDEFoundation.Measure.FiniteVectorMean

/-! # Packing of local quadratic oscillation stopping boxes -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory Set
open scoped ENNReal

private theorem dyadicBoxAverage_eq_ofReal_integralAverage_of_nonneg
    {d : ℕ} (I : Box (Fin d)) (h : Vec d → ℝ)
    (hh : IntegrableOn h (I : Set (Vec d))) (hn : ∀ x, 0 ≤ h x)
    (p : List (Set (Fin d))) :
    dyadicBoxAverage I h p =
      ENNReal.ofReal (integralAverage (dyadicDescendant I p : Set (Vec d)) h) := by
  have hsub : (dyadicDescendant I p : Set (Vec d)) ⊆ (I : Set (Vec d)) :=
    dyadicDescendant_le I p
  have hpInt := hh.mono_set hsub
  have hvTop := volume_dyadicDescendant_lt_top I p
  have hvReal : 0 < (volume (dyadicDescendant I p : Set (Vec d))).toReal := by
    rw [Box.volume_apply']
    exact Finset.prod_pos fun i _ =>
      sub_pos.mpr ((dyadicDescendant I p).lower_lt_upper i)
  unfold dyadicBoxAverage integralAverage
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr ENNReal.toReal_nonneg),
    ENNReal.ofReal_inv_of_pos hvReal, ENNReal.ofReal_toReal hvTop.ne,
    ofReal_integral_eq_lintegral_ofReal hpInt (ae_of_all _ hn)]
  simp_rw [abs_of_nonneg (hn _)]

/-- First descendants where the quadratic oscillation average exceeds four
times its root value occupy at most one quarter of the root box. This includes
the zero-energy branch. -/
theorem volume_iUnion_firstPrefixStop_vecNormSq_le
    {d m : ℕ} (I : Box (Fin d)) (g : Vec d → Vec m)
    (hg : ∀ i : Fin m, MemLp (fun x => g x i) 2 (volumeOn (I : Set (Vec d)))) :
    volume (⋃ p : List (Set (Fin d)),
      ⋃ (_ : IsFirstPrefixStop
        (fun q => 4 * integralAverage (I : Set (Vec d))
          (fun x => vecNormSq (g x - coordinateVectorAverage (I : Set (Vec d)) g)) <
            integralAverage (dyadicDescendant I q : Set (Vec d))
              (fun x => vecNormSq
                (g x - coordinateVectorAverage (I : Set (Vec d)) g))) p),
        (dyadicDescendant I p : Set (Vec d))) ≤
      (4 : ℝ≥0∞)⁻¹ * volume (I : Set (Vec d)) := by
  let c := coordinateVectorAverage (I : Set (Vec d)) g
  let h : Vec d → ℝ := fun x => vecNormSq (g x - c)
  let e2 := integralAverage (I : Set (Vec d)) h
  have hItop := I.measure_coe_lt_top volume
  have hh : IntegrableOn h (I : Set (Vec d)) volume :=
    integrableOn_vecNormSq_sub_const_of_coordinate_memLp hg hItop c
  have hn (x : Vec d) : 0 ≤ h x := vecNormSq_nonneg _
  have he2 : 0 ≤ e2 := integralAverage_nonneg I.measurableSet_coe
    (fun x _ => hn x)
  have havgAbs : integralAverage (I : Set (Vec d)) (fun x => |h x|) = e2 := by
    calc
      integralAverage (I : Set (Vec d)) (fun x => |h x|) =
          integralAverage (I : Set (Vec d)) h := by
        congr 2
        funext x
        rw [abs_of_nonneg (hn x)]
      _ = e2 := rfl
  by_cases he : e2 = 0
  · have hmax : ∀ x, dyadicBoxMaximal I h x = 0 :=
      dyadicBoxMaximal_eq_zero_of_integralAverage_abs_eq_zero I h hh
        (havgAbs.trans he)
    have hnone (p : List (Set (Fin d))) : ¬IsFirstPrefixStop
        (fun q => 4 * e2 < integralAverage (dyadicDescendant I q : Set (Vec d)) h) p := by
      intro hp
      obtain ⟨x, hx⟩ := (dyadicDescendant I p).exists_mem
      have havg := dyadicBoxAverage_le_dyadicBoxMaximal I h p hx
      rw [hmax x] at havg
      have hbridge := dyadicBoxAverage_eq_ofReal_integralAverage_of_nonneg I h hh hn p
      have hpos : 0 < integralAverage (dyadicDescendant I p : Set (Vec d)) h := by
        simpa [he] using hp.1
      rw [hbridge] at havg
      exact (not_lt_of_ge havg) (ENNReal.ofReal_pos.mpr hpos)
    simp [c, h, e2, hnone]
  · have hepos : 0 < e2 := lt_of_le_of_ne he2 (Ne.symm he)
    have hpack := volume_iUnion_firstPrefixStop_dyadicBoxAverage_le I h hh
      (havgAbs.trans_gt hepos)
    have hpred : (fun q => ENNReal.ofReal (4 * integralAverage (I : Set (Vec d))
        (fun x => |h x|)) < dyadicBoxAverage I h q) =
        (fun q => 4 * e2 < integralAverage (dyadicDescendant I q : Set (Vec d)) h) := by
      funext q
      apply propext
      rw [havgAbs, dyadicBoxAverage_eq_ofReal_integralAverage_of_nonneg I h hh hn q,
        ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg (by norm_num) he2)]
    rw [hpred] at hpack
    simpa [c, h, e2] using hpack

end PDE
