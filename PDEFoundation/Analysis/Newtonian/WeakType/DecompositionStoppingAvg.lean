module

public import PDEFoundation.Measure.DyadicFirstStopPacking
public import PDEFoundation.Measure.DyadicBoxDifferentiation
public import PDEFoundation.Geometry.DyadicBoxVolumeRatio

/-! # Averages along first dyadic stops

Conversion of the extended dyadic averages of a nonnegative integrable function to real
`integralAverage`s, the parent bound `avg_Q ≤ 2^d λ` for a first stop `Q`, and the almost
everywhere bound off the stopping set.
-/

@[expose] public section

open BoxIntegral MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE.NewtonWeakType

noncomputable section

variable {d : ℕ}

theorem dyadicDescendant_subset_root (I : Box (Fin d)) (p : List (Set (Fin d))) :
    (dyadicDescendant I p : Set (Vec d)) ⊆ (I : Set (Vec d)) :=
  fun _ hx => dyadicDescendant_le I p hx

/-- The extended dyadic average of a nonnegative integrable function is the `ofReal` of the
real integral average. -/
theorem dyadicBoxAverage_eq_ofReal_integralAverage (I : Box (Fin d)) {b : Vec d → ℝ}
    (hb : IntegrableOn b (I : Set (Vec d))) (hb0 : ∀ x, 0 ≤ b x) (p : List (Set (Fin d))) :
    dyadicBoxAverage I b p =
      ENNReal.ofReal (integralAverage (dyadicDescendant I p : Set (Vec d)) b) := by
  set Q := dyadicDescendant I p with hQ
  have hint : IntegrableOn b (Q : Set (Vec d)) := hb.mono_set (dyadicDescendant_subset_root I p)
  have hvpos : 0 < (volume (Q : Set (Vec d))).toReal := volume_box_toReal_pos Q
  have hvtop : volume (Q : Set (Vec d)) ≠ ⊤ := (volume_dyadicDescendant_lt_top I p).ne
  unfold dyadicBoxAverage integralAverage
  have habs : ∀ x, ENNReal.ofReal |b x| = ENNReal.ofReal (b x) := fun x => by
    rw [abs_of_nonneg (hb0 x)]
  simp_rw [habs]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hb0),
    ENNReal.ofReal_mul (inv_nonneg.mpr hvpos.le), ENNReal.ofReal_inv_of_pos hvpos,
    ENNReal.ofReal_toReal hvtop]

/-- A real average bound from the negation of a stopping condition. -/
theorem integralAverage_le_of_not_bad (I : Box (Fin d)) {b : Vec d → ℝ}
    (hb : IntegrableOn b (I : Set (Vec d))) (hb0 : ∀ x, 0 ≤ b x) {lam : ℝ} (hlam : 0 ≤ lam)
    {p : List (Set (Fin d))} (hp : ¬ ENNReal.ofReal lam < dyadicBoxAverage I b p) :
    integralAverage (dyadicDescendant I p : Set (Vec d)) b ≤ lam := by
  rw [dyadicBoxAverage_eq_ofReal_integralAverage I hb hb0 p, not_lt,
    ENNReal.ofReal_le_ofReal_iff hlam] at hp
  exact hp

/-- The real stopping condition. -/
theorem lt_integralAverage_of_bad (I : Box (Fin d)) {b : Vec d → ℝ}
    (hb : IntegrableOn b (I : Set (Vec d))) (hb0 : ∀ x, 0 ≤ b x) {lam : ℝ}
    {p : List (Set (Fin d))} (hp : ENNReal.ofReal lam < dyadicBoxAverage I b p) :
    lam < integralAverage (dyadicDescendant I p : Set (Vec d)) b := by
  rw [dyadicBoxAverage_eq_ofReal_integralAverage I hb hb0 p] at hp
  exact (ENNReal.ofReal_lt_ofReal_iff'.mp hp).1

/-- Real set integral of the function over a descendant equals average times volume. -/
theorem setIntegral_eq_integralAverage_mul (Q : Set (Vec d)) (b : Vec d → ℝ)
    (hQ : 0 < (volume Q).toReal) :
    ∫ x in Q, b x = integralAverage Q b * (volume Q).toReal := by
  unfold integralAverage
  field_simp

/-- A first stop has average at most `2^d λ`. -/
theorem integralAverage_firstStop_le (I : Box (Fin d)) {b : Vec d → ℝ}
    (hb : IntegrableOn b (I : Set (Vec d))) (hb0 : ∀ x, 0 ≤ b x) {lam : ℝ} (hlam : 0 ≤ lam)
    (hroot : ¬ ENNReal.ofReal lam < dyadicBoxAverage I b [])
    {p : List (Set (Fin d))}
    (hp : IsFirstPrefixStop (fun q => ENNReal.ofReal lam < dyadicBoxAverage I b q) p) :
    integralAverage (dyadicDescendant I p : Set (Vec d)) b ≤ 2 ^ d * lam := by
  have hpne : p ≠ [] := firstPrefixStop_ne_nil hroot hp
  set q := p.dropLast with hq
  have hqp : q <+: p := List.dropLast_prefix p
  have hlen : q.length + 1 = p.length := by
    rw [hq, List.length_dropLast]
    have : 0 < p.length := List.length_pos_iff.mpr hpne
    omega
  have hqne : q ≠ p := fun h => by rw [h] at hlen; omega
  have hnb : ¬ ENNReal.ofReal lam < dyadicBoxAverage I b q := hp.2 q hqp hqne
  have hq_le := integralAverage_le_of_not_bad I hb hb0 hlam hnb
  have hsub : (dyadicDescendant I p : Set (Vec d)) ⊆ (dyadicDescendant I q : Set (Vec d)) :=
    dyadicDescendant_subset_of_isPrefix I hqp
  have hQp : 0 < (volume (dyadicDescendant I p : Set (Vec d))).toReal :=
    volume_box_toReal_pos _
  have hQq : 0 < (volume (dyadicDescendant I q : Set (Vec d))).toReal :=
    volume_box_toReal_pos _
  have hvol : (volume (dyadicDescendant I q : Set (Vec d))).toReal =
      2 ^ d * (volume (dyadicDescendant I p : Set (Vec d))).toReal := by
    rw [volume_dyadicDescendant_toReal, volume_dyadicDescendant_toReal, ← hlen, mul_add,
      mul_one, pow_add]
    have : (0 : ℝ) < 2 ^ (d * q.length) := by positivity
    field_simp
  have hmono : ∫ x in (dyadicDescendant I p : Set (Vec d)), b x ≤
      ∫ x in (dyadicDescendant I q : Set (Vec d)), b x :=
    setIntegral_mono_set (hb.mono_set (dyadicDescendant_subset_root I q))
      (Eventually.of_forall hb0) (Eventually.of_forall hsub)
  rw [setIntegral_eq_integralAverage_mul _ _ hQp,
    setIntegral_eq_integralAverage_mul _ _ hQq, hvol] at hmono
  have h2 : integralAverage (dyadicDescendant I p : Set (Vec d)) b *
      (volume (dyadicDescendant I p : Set (Vec d))).toReal ≤
      (2 ^ d * lam) * (volume (dyadicDescendant I p : Set (Vec d))).toReal := by
    calc _ ≤ integralAverage (dyadicDescendant I q : Set (Vec d)) b *
          (2 ^ d * (volume (dyadicDescendant I p : Set (Vec d))).toReal) := hmono
      _ ≤ lam * (2 ^ d * (volume (dyadicDescendant I p : Set (Vec d))).toReal) :=
        mul_le_mul_of_nonneg_right hq_le (by positivity)
      _ = _ := by ring
  exact le_of_mul_le_mul_right h2 hQp

end

end PDE.NewtonWeakType
