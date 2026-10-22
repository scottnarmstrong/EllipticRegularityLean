module

public import PDEFoundation.Geometry.BoxGrid
public import PDEFoundation.Geometry.BoxCircumscribedContainment

/-! # Retained cube cover for the local Calderón--Zygmund estimate -/

@[expose] public section

namespace PDE

open BoxIntegral Set

noncomputable section

/-- The source cube side length between radii `s < t`. -/
def calderonZygmundCubeSide (d : ℕ) (s t : ℝ) : ℝ :=
  (t - s) / (2 * Real.sqrt d)

/-- The source cube side length is positive in nonzero dimension. -/
theorem calderonZygmundCubeSide_pos {d : ℕ} (hd : 0 < d)
    {s t : ℝ} (hst : s < t) :
    0 < calderonZygmundCubeSide d s t := by
  unfold calderonZygmundCubeSide
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  exact div_pos (sub_pos.mpr hst) (mul_pos (by norm_num) hsqrt)

/-- The literal grid root associated with an integer index. -/
def calderonZygmundGridBox {d : ℕ} (hd : 0 < d)
    {s t : ℝ} (hst : s < t) (k : Fin d → ℤ) : Box (Fin d) :=
  boxGrid (calderonZygmundCubeSide d s t)
    (calderonZygmundCubeSide_pos hd hst) k

/-- The literal subtype of grid roots whose half-open carrier meets `B_s(0)`. -/
def calderonZygmundRetainedIndices {d : ℕ} (hd : 0 < d)
    {s t : ℝ} (hst : s < t) :=
  {k : Fin d → ℤ //
    ((calderonZygmundGridBox hd hst k : Set (Vec d)) ∩
      euclideanBall (0 : Vec d) s).Nonempty}

/-- The circumscribed radius of a source grid root is `(t-s)/4`. -/
theorem calderonZygmund_circumscribedRadius_eq {d : ℕ} (hd : 0 < d)
    (s t : ℝ) :
    Real.sqrt d * calderonZygmundCubeSide d s t / 2 = (t - s) / 4 := by
  unfold calderonZygmundCubeSide
  have hsqrt : Real.sqrt d ≠ 0 :=
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)).ne'
  field_simp
  ring

/-- Every retained root has the common source side length. -/
theorem upper_sub_lower_calderonZygmundGridBox {d : ℕ} (hd : 0 < d)
    {s t : ℝ} (hst : s < t) (k : Fin d → ℤ) (i : Fin d) :
    (calderonZygmundGridBox hd hst k).upper i -
        (calderonZygmundGridBox hd hst k).lower i =
      calderonZygmundCubeSide d s t :=
  upper_sub_lower_boxGrid _ (calderonZygmundCubeSide_pos hd hst) k i

/-- Open interiors of distinct retained roots are pairwise disjoint. -/
theorem pairwiseDisjoint_calderonZygmundRetained_Ioo
    {d : ℕ} (hd : 0 < d) {s t : ℝ} (hst : s < t) :
    Pairwise fun k l : calderonZygmundRetainedIndices hd hst =>
      Disjoint (Box.Ioo (calderonZygmundGridBox hd hst k.1))
        (Box.Ioo (calderonZygmundGridBox hd hst l.1)) := by
  intro k l hkl
  apply disjoint_boxGrid_Ioo (calderonZygmundCubeSide_pos hd hst)
  intro hval
  exact hkl (Subtype.ext hval)

/-- The retained half-open roots cover the inner round ball. -/
theorem euclideanBall_subset_iUnion_calderonZygmundRetained
    {d : ℕ} (hd : 0 < d) {s t : ℝ} (hst : s < t) :
    euclideanBall (0 : Vec d) s ⊆
      ⋃ k : calderonZygmundRetainedIndices hd hst,
        (calderonZygmundGridBox hd hst k.1 : Set (Vec d)) := by
  intro x hx
  let ell := calderonZygmundCubeSide d s t
  let k := boxGridIndex ell x
  have hell : 0 < ell := calderonZygmundCubeSide_pos hd hst
  have hxk : x ∈ calderonZygmundGridBox hd hst k := by
    exact mem_boxGrid_index hell x
  let kr : calderonZygmundRetainedIndices hd hst :=
    ⟨k, ⟨x, hxk, hx⟩⟩
  exact Set.mem_iUnion.mpr ⟨kr, hxk⟩

/-- Every retained root has its doubled circumscribed ball inside the outer
round ball `B_t(0)`. -/
theorem euclideanBall_two_mul_circumscribedRadius_retained_subset
    {d : ℕ} (hd : 0 < d) {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (k : calderonZygmundRetainedIndices hd hst) :
    euclideanBall (boxCenter (calderonZygmundGridBox hd hst k.1))
        (2 * (Real.sqrt d * calderonZygmundCubeSide d s t / 2)) ⊆
      euclideanBall (0 : Vec d) t := by
  obtain ⟨y, hyQ, hys⟩ := k.2
  apply euclideanBall_two_mul_circumscribedRadius_subset_of_mem
    (calderonZygmundGridBox hd hst k.1)
    (calderonZygmundCubeSide d s t) s t hd
    (upper_sub_lower_calderonZygmundGridBox hd hst k.1) hs y hyQ hys
  rw [calderonZygmund_circumscribedRadius_eq hd s t]
  linarith

end

end PDE
