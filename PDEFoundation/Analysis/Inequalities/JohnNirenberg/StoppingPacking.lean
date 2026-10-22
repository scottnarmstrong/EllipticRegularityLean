module

public import PDEFoundation.Analysis.Inequalities.JohnNirenberg.Stopping
public import PDEFoundation.Measure.DyadicBoxMaximalWeak
public import PDEFoundation.Geometry.DyadicBoxVolumeRatio

/-!
# Packing of John–Nirenberg stopping generations

Item (i) of Step 1 of Lemma 1.16: the first stops of a root `P` have total volume at
most `lam⁻¹ ∫_P |v - (v)_P|`. Iterating over the recursive generations gives geometric decay of
the stopping regions.
-/

@[expose] public section

namespace PDE.JohnNirenberg

open BoxIntegral MeasureTheory Set
open scoped ENNReal

/-- The extended absolute dyadic average is the extended real average for integrable data. -/
theorem dyadicBoxAverage_eq_ofReal_integralAverage_abs {d : ℕ} (P : Box (Fin d))
    {b : Vec d → ℝ} (hb : IntegrableOn b (P : Set (Vec d))) (q : List (Set (Fin d))) :
    dyadicBoxAverage P b q =
      ENNReal.ofReal (integralAverage (dyadicDescendant P q : Set (Vec d)) fun x => |b x|) := by
  have hsub : (dyadicDescendant P q : Set (Vec d)) ⊆ (P : Set (Vec d)) :=
    dyadicDescendant_le P q
  have hqInt : IntegrableOn (fun x => |b x|) (dyadicDescendant P q : Set (Vec d)) volume :=
    (hb.mono_set hsub).abs
  have hvTop := volume_dyadicDescendant_lt_top P q
  have hvReal := volume_box_toReal_pos (dyadicDescendant P q)
  unfold dyadicBoxAverage integralAverage
  beta_reduce
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr ENNReal.toReal_nonneg),
    ENNReal.ofReal_inv_of_pos hvReal, ENNReal.ofReal_toReal hvTop.ne,
    ofReal_integral_eq_lintegral_ofReal hqInt (ae_of_all _ fun x => abs_nonneg (b x))]

/-- The John–Nirenberg first stops are exactly a strict superlevel set of the dyadic maximal
function of `v - (v)_P`. -/
theorem jnStopUnion_eq_setOf_lt_dyadicBoxMaximal {d : ℕ} (P : Box (Fin d)) {v : Vec d → ℝ}
    (hv : IntegrableOn v (P : Set (Vec d))) {lam : ℝ} (hlam : 0 ≤ lam) :
    jnStopUnion P v lam =
      {x | ENNReal.ofReal lam <
        dyadicBoxMaximal P (fun y => v y - integralAverage (P : Set (Vec d)) v) x} := by
  have hb : IntegrableOn (fun y => v y - integralAverage (P : Set (Vec d)) v)
      (P : Set (Vec d)) volume :=
    hv.sub (integrableOn_const (P.measure_coe_lt_top volume).ne)
  have hpred : jnBad P v lam = fun q => ENNReal.ofReal lam <
      dyadicBoxAverage P (fun y => v y - integralAverage (P : Set (Vec d)) v) q := by
    funext q
    apply propext
    rw [dyadicBoxAverage_eq_ofReal_integralAverage_abs P hb q,
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg hlam]
    rfl
  rw [set_lt_dyadicBoxMaximal_eq_firstStops, jnStopUnion, hpred]

/-- Item (i): the first stops occupy at most `lam⁻¹ ⨍_P |v - (v)_P|` of the root. -/
theorem ofReal_mul_volume_jnStopUnion_le {d : ℕ} (P : Box (Fin d)) {v : Vec d → ℝ}
    (hv : IntegrableOn v (P : Set (Vec d))) {lam : ℝ} (hlam : 0 ≤ lam) :
    ENNReal.ofReal lam * volume (jnStopUnion P v lam) ≤
      ENNReal.ofReal (integralAverage (P : Set (Vec d))
        (fun x => |v x - integralAverage (P : Set (Vec d)) v|)) * volume (P : Set (Vec d)) := by
  set c := integralAverage (P : Set (Vec d)) v
  set A := integralAverage (P : Set (Vec d)) (fun x => |v x - c|)
  have hb : IntegrableOn (fun y => v y - c) (P : Set (Vec d)) volume :=
    hv.sub (integrableOn_const (P.measure_coe_lt_top volume).ne)
  have hE := jnStopUnion_eq_setOf_lt_dyadicBoxMaximal P hv hlam
  have hweak := ofReal_mul_volume_set_lt_dyadicBoxMaximal_le_lintegral P (fun y => v y - c) lam
  rw [← hE] at hweak
  have hmono : (∫⁻ x in jnStopUnion P v lam, ENNReal.ofReal |v x - c|) ≤
      ∫⁻ x in (P : Set (Vec d)), ENNReal.ofReal |v x - c| :=
    lintegral_mono_set (jnStopUnion_subset P v lam)
  have hroot : (∫⁻ x in (P : Set (Vec d)), ENNReal.ofReal |v x - c|) =
      ENNReal.ofReal A * volume (P : Set (Vec d)) := by
    have hvTop := P.measure_coe_lt_top volume
    have hvReal := volume_box_toReal_pos P
    have hA : 0 ≤ A := integralAverage_nonneg P.measurableSet_coe fun x _ => abs_nonneg _
    have hint : ∫ x in (P : Set (Vec d)), |v x - c| = A * (volume (P : Set (Vec d))).toReal := by
      simp only [A, integralAverage]
      field_simp
    rw [← ofReal_integral_eq_lintegral_ofReal hb.abs
      (ae_of_all _ fun x => abs_nonneg (v x - c)), hint, ENNReal.ofReal_mul hA,
      ENNReal.ofReal_toReal hvTop.ne]
  exact hweak.trans (hmono.trans hroot.le)

/-- Item (i) in ratio form: with root oscillation at most `N`, the first stops occupy at most
`N / lam` of the root. -/
theorem volume_jnStopUnion_le {d : ℕ} (P : Box (Fin d)) {v : Vec d → ℝ}
    (hv : IntegrableOn v (P : Set (Vec d))) {lam N : ℝ} (hlam : 0 < lam)
    (hosc : integralAverage (P : Set (Vec d))
      (fun x => |v x - integralAverage (P : Set (Vec d)) v|) ≤ N) :
    volume (jnStopUnion P v lam) ≤ ENNReal.ofReal (N / lam) * volume (P : Set (Vec d)) := by
  have h := (ofReal_mul_volume_jnStopUnion_le P hv hlam.le).trans
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal hosc) _)
  have h0 : ENNReal.ofReal lam ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hlam
  have hle : volume (jnStopUnion P v lam) ≤
      ENNReal.ofReal N * volume (P : Set (Vec d)) / ENNReal.ofReal lam :=
    (ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl ENNReal.ofReal_ne_top)).mpr
      (by rw [mul_comm]; exact h)
  rwa [ENNReal.mul_div_right_comm, ← ENNReal.ofReal_div_of_pos hlam] at hle

/-- One recursive generation shrinks the stopping region by the factor `N / lam`. -/
theorem volume_jnRegion_succ_le {d : ℕ} (I : Box (Fin d)) {v : Vec d → ℝ}
    (hv : IntegrableOn v (I : Set (Vec d))) {lam N : ℝ} (hlam : 0 < lam)
    (hosc : ∀ p : List (Set (Fin d)),
      integralAverage (dyadicDescendant I p : Set (Vec d))
        (fun x => |v x - integralAverage (dyadicDescendant I p : Set (Vec d)) v|) ≤ N)
    (n : ℕ) :
    volume (jnRegion I v lam (n + 1)) ≤
      ENNReal.ofReal (N / lam) * volume (jnRegion I v lam n) := by
  let P := {p // p ∈ jnGeneration I v lam n}
  calc
    volume (jnRegion I v lam (n + 1)) ≤
        volume (⋃ p : P, jnStopUnion (dyadicDescendant I p.1) v lam) :=
      measure_mono (jnRegion_succ_subset_iUnion I v lam n)
    _ ≤ ∑' p : P, volume (jnStopUnion (dyadicDescendant I p.1) v lam) := measure_iUnion_le _
    _ ≤ ∑' p : P, ENNReal.ofReal (N / lam) *
        volume (dyadicDescendant I p.1 : Set (Vec d)) := by
      refine ENNReal.tsum_le_tsum fun p => ?_
      exact volume_jnStopUnion_le _ (hv.mono_set (dyadicDescendant_le I p.1)) hlam (hosc p.1)
    _ = ENNReal.ofReal (N / lam) * ∑' p : P, volume (dyadicDescendant I p.1 : Set (Vec d)) :=
      ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (N / lam) * volume (jnRegion I v lam n) := by
      congr 1
      rw [jnRegion, measure_iUnion]
      · exact (pairwiseDisjoint_jnGeneration I v lam n).subtype _ _
      · exact fun p => measurableSet_dyadicDescendant I p.1

/-- Geometric decay of the recursive John–Nirenberg stopping regions. -/
theorem volume_jnRegion_le {d : ℕ} (I : Box (Fin d)) {v : Vec d → ℝ}
    (hv : IntegrableOn v (I : Set (Vec d))) {lam N : ℝ} (hlam : 0 < lam) (hN : 0 ≤ N)
    (hosc : ∀ p : List (Set (Fin d)),
      integralAverage (dyadicDescendant I p : Set (Vec d))
        (fun x => |v x - integralAverage (dyadicDescendant I p : Set (Vec d)) v|) ≤ N)
    (n : ℕ) :
    volume (jnRegion I v lam n) ≤ ENNReal.ofReal ((N / lam) ^ n) * volume (I : Set (Vec d)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hr : 0 ≤ N / lam := div_nonneg hN hlam.le
      calc
        volume (jnRegion I v lam (n + 1)) ≤
            ENNReal.ofReal (N / lam) * volume (jnRegion I v lam n) :=
          volume_jnRegion_succ_le I hv hlam hosc n
        _ ≤ ENNReal.ofReal (N / lam) *
            (ENNReal.ofReal ((N / lam) ^ n) * volume (I : Set (Vec d))) :=
          mul_le_mul_right ih _
        _ = ENNReal.ofReal ((N / lam) ^ (n + 1)) * volume (I : Set (Vec d)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hr, pow_succ, mul_comm (N / lam)]

end PDE.JohnNirenberg
