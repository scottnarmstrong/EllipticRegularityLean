module

public import PDEFoundation.Geometry.DyadicBoxVolume
public import PDEFoundation.Geometry.EuclideanBall
public import PDEFoundation.Geometry.AxisBox

/-! # Centers and round-ball geometry of equal-side boxes -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory Set

/-- The coordinate midpoint of a Mathlib box. -/
noncomputable def boxCenter {d : ℕ} (I : Box (Fin d)) : Vec d :=
  fun i => (I.lower i + I.upper i) / 2

/-- The open interior of an equal-side box is the corresponding centered open
axis cube. -/
theorem Box.Ioo_eq_centeredAxisCube_of_commonWidth {d : ℕ}
    (I : Box (Fin d)) (L : ℝ)
    (hwidth : ∀ i, I.upper i - I.lower i = L) :
    Box.Ioo I = centeredAxisCube (boxCenter I) (L / 2) := by
  ext x
  change x ∈ Set.univ.pi (fun i => Set.Ioo (I.lower i) (I.upper i)) ↔
    x ∈ centeredAxisCube (boxCenter I) (L / 2)
  simp only [Set.mem_pi, Set.mem_univ, forall_const, centeredAxisCube, axisBox]
  change (∀ i, I.lower i < x i ∧ x i < I.upper i) ↔
    ∀ i, boxCenter I i - L / 2 < x i ∧ x i < boxCenter I i + L / 2
  apply forall_congr'
  intro i
  dsimp only [boxCenter]
  have hi := hwidth i
  constructor <;> rintro ⟨hlo, hup⟩ <;> constructor <;> linarith

/-- A box carrier and its open interior agree almost everywhere. -/
theorem Box.coe_ae_eq_Ioo {d : ℕ} (I : Box (Fin d)) :
    (I : Set (Vec d)) =ᵐ[volume] Box.Ioo I :=
  I.coe_ae_eq_Icc.trans I.Ioo_ae_eq_Icc.symm

/-- The exact volume of an equal-side box. -/
theorem volume_box_toReal_eq_pow_of_commonWidth {d : ℕ}
    (I : Box (Fin d)) (L : ℝ)
    (hwidth : ∀ i, I.upper i - I.lower i = L) :
    (volume (I : Set (Vec d))).toReal = L ^ d := by
  rw [Box.volume_apply']
  simp_rw [hwidth]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Equal coordinate widths scale exactly along a literal dyadic path. -/
theorem upper_sub_lower_dyadicDescendant_of_commonWidth {d : ℕ}
    (I : Box (Fin d)) (L : ℝ)
    (hwidth : ∀ i, I.upper i - I.lower i = L)
    (p : List (Set (Fin d))) (i : Fin d) :
    (dyadicDescendant I p).upper i - (dyadicDescendant I p).lower i =
      L / (2 : ℝ) ^ p.length := by
  rw [upper_sub_lower_dyadicDescendant, hwidth]

/-- The open interior of an equal-side box lies strictly inside its exact
circumscribed round Euclidean ball. -/
theorem Box.Ioo_subset_euclideanBall_boxCenter {d : ℕ}
    (I : Box (Fin d)) (L : ℝ) (hd : 0 < d)
    (hwidth : ∀ i, I.upper i - I.lower i = L) :
    Box.Ioo I ⊆ euclideanBall (boxCenter I) (Real.sqrt d * L / 2) := by
  have i0 : Fin d := ⟨0, hd⟩
  have hL : 0 < L := by
    rw [← hwidth i0]
    exact sub_pos.mpr (I.lower_lt_upper i0)
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hr : 0 < Real.sqrt d * L / 2 := by positivity
  intro x hx
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mpr
  rw [vecEuclideanNorm, Real.sqrt_lt' hr, vecNormSq_eq_sum_sq]
  have hcoord (i : Fin d) :
      (x i - boxCenter I i) ^ 2 < (L / 2) ^ 2 := by
    have hxi : I.lower i < x i ∧ x i < I.upper i := hx i (Set.mem_univ i)
    dsimp only [boxCenter]
    have hi := hwidth i
    have habs : |x i - (I.lower i + I.upper i) / 2| < L / 2 := by
      rw [abs_lt]
      constructor <;> linarith
    rw [sq_lt_sq]
    simpa [abs_of_pos (show 0 < L / 2 by positivity)] using habs
  have hsum : ∑ i : Fin d, (x i - boxCenter I i) ^ 2 <
      ∑ _i : Fin d, (L / 2) ^ 2 := by
    exact Finset.sum_lt_sum (fun i _ => (hcoord i).le)
      ⟨i0, Finset.mem_univ i0, hcoord i0⟩
  calc
    ∑ i : Fin d, (x i - boxCenter I i) ^ 2 <
        ∑ _i : Fin d, (L / 2) ^ 2 := hsum
    _ = (Real.sqrt d * L / 2) ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc
        (d : ℝ) * (L / 2) ^ 2 = (Real.sqrt d) ^ 2 * (L / 2) ^ 2 := by
          rw [Real.sq_sqrt hdR.le]
        _ = (Real.sqrt d * L / 2) ^ 2 := by ring

end PDE
