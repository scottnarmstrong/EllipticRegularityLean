module

public import PDEFoundation.Measure.DyadicBoxMaximal

/-! # Sharp weak estimate for the dyadic box maximal function -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory Set
open scoped ENNReal Function

/-- The strict superlevel of the literal dyadic maximal function satisfies the
sharp distribution estimate, with no integrability or finiteness premise. -/
theorem ofReal_mul_volume_set_lt_dyadicBoxMaximal_le_lintegral
    {d : ℕ} (I : Box (Fin d)) (b : Vec d → ℝ) (t : ℝ) :
    ENNReal.ofReal t * volume {x | ENNReal.ofReal t < dyadicBoxMaximal I b x} ≤
      ∫⁻ x in {x | ENNReal.ofReal t < dyadicBoxMaximal I b x}, ENNReal.ofReal |b x| := by
  classical
  let bad : List (Set (Fin d)) → Prop :=
    fun p => ENNReal.ofReal t < dyadicBoxAverage I b p
  let S := {p : List (Set (Fin d)) // IsFirstPrefixStop bad p}
  let P : S → Set (Vec d) := fun p => (dyadicDescendant I p.1 : Set (Vec d))
  have hlevel : {x | ENNReal.ofReal t < dyadicBoxMaximal I b x} = ⋃ p : S, P p := by
    rw [set_lt_dyadicBoxMaximal_eq_firstStops]
    ext x
    simp only [mem_iUnion, P, S, bad]
    constructor
    · rintro ⟨p, hp, hxp⟩
      exact ⟨⟨p, hp⟩, hxp⟩
    · rintro ⟨p, hxp⟩
      exact ⟨p.1, p.2, hxp⟩
  have hmeas (p : S) : MeasurableSet (P p) :=
    measurableSet_dyadicDescendant I p.1
  have hdisj : Pairwise (Disjoint on P) := by
    intro p q hpq
    exact disjoint_dyadicDescendant_of_firstPrefixStop I p.2 q.2
      (Subtype.coe_ne_coe.mpr hpq)
  have hbox (p : S) :
      ENNReal.ofReal t * volume (P p) ≤
        ∫⁻ x in P p, ENNReal.ofReal |b x| := by
    let v := volume (P p)
    let A := ∫⁻ x in P p, ENNReal.ofReal |b x|
    have hvTop : v ≠ ⊤ :=
      (volume_dyadicDescendant_lt_top I p.1).ne
    have hvReal : 0 < v.toReal := by
      dsimp only [v, P]
      rw [Box.volume_apply']
      exact Finset.prod_pos fun i _ => sub_pos.mpr ((dyadicDescendant I p.1).lower_lt_upper i)
    have hv0 : v ≠ 0 := by
      intro hv
      rw [hv, ENNReal.toReal_zero] at hvReal
      exact (lt_self_iff_false 0).mp hvReal
    have hstop : ENNReal.ofReal t < v⁻¹ * A := p.2.1
    calc
      ENNReal.ofReal t * v ≤ (v⁻¹ * A) * v :=
        mul_le_mul_left hstop.le v
      _ = A := by
        calc
          v⁻¹ * A * v = (v⁻¹ * v) * A := by ac_rfl
          _ = A := by rw [ENNReal.inv_mul_cancel hv0 hvTop, one_mul]
  rw [hlevel, measure_iUnion hdisj hmeas,
    lintegral_iUnion hmeas hdisj]
  rw [← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum hbox

end PDE
