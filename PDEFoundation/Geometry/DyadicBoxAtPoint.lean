module

public import PDEFoundation.Geometry.DyadicBoxPartition

/-! # The literal dyadic descendant at a point and depth -/

@[expose] public section

namespace PDE

open BoxIntegral

/-- The unique literal path of length `n` whose descendant contains `x`. -/
noncomputable def dyadicPathAtDepth {d : ℕ} (I : Box (Fin d))
    (x : Vec d) (hx : x ∈ (I : Set (Vec d))) (n : ℕ) :
    List (Set (Fin d)) :=
  (existsUnique_mem_dyadicDescendant_of_length I hx n).exists.choose

/-- The literal descendant selected at `x` and depth `n`. -/
noncomputable def dyadicBoxAtDepth {d : ℕ} (I : Box (Fin d))
    (x : Vec d) (hx : x ∈ (I : Set (Vec d))) (n : ℕ) : Box (Fin d) :=
  dyadicDescendant I (dyadicPathAtDepth I x hx n)

theorem length_dyadicPathAtDepth {d : ℕ} (I : Box (Fin d))
    (x : Vec d) (hx : x ∈ (I : Set (Vec d))) (n : ℕ) :
    (dyadicPathAtDepth I x hx n).length = n :=
  (existsUnique_mem_dyadicDescendant_of_length I hx n).exists.choose_spec.1

theorem mem_dyadicBoxAtDepth {d : ℕ} (I : Box (Fin d))
    (x : Vec d) (hx : x ∈ (I : Set (Vec d))) (n : ℕ) :
    x ∈ (dyadicBoxAtDepth I x hx n : Set (Vec d)) :=
  (existsUnique_mem_dyadicDescendant_of_length I hx n).exists.choose_spec.2

theorem dyadicPathAtDepth_eq_iff {d : ℕ} (I : Box (Fin d))
    (x : Vec d) (hx : x ∈ (I : Set (Vec d))) (n : ℕ)
    (p : List (Set (Fin d))) :
    dyadicPathAtDepth I x hx n = p ↔
      p.length = n ∧ x ∈ (dyadicDescendant I p : Set (Vec d)) := by
  constructor
  · rintro rfl
    exact ⟨length_dyadicPathAtDepth I x hx n, mem_dyadicBoxAtDepth I x hx n⟩
  · intro hp
    exact (existsUnique_mem_dyadicDescendant_of_length I hx n).unique
      (existsUnique_mem_dyadicDescendant_of_length I hx n).exists.choose_spec hp

theorem dyadicBoxAtDepth_radius_nonneg {d : ℕ} (I : Box (Fin d)) (n : ℕ) :
    0 ≤ ‖I.upper - I.lower‖ / (2 : ℝ) ^ n :=
  div_nonneg (norm_nonneg _) (by positivity)

theorem dyadicBoxAtDepth_radius_pos {d : ℕ} (I : Box (Fin d))
    (hd : 0 < d) (n : ℕ) :
    0 < ‖I.upper - I.lower‖ / (2 : ℝ) ^ n := by
  apply div_pos _ (by positivity)
  rw [norm_pos_iff]
  intro hzero
  have hi := congrFun hzero ⟨0, hd⟩
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hi
  exact (I.lower_lt_upper ⟨0, hd⟩).ne hi.symm

/-- A selected descendant is contained in the closed supremum metric ball
whose radius is its root supremum width divided by `2 ^ n`. -/
theorem dyadicBoxAtDepth_subset_closedBall {d : ℕ} (I : Box (Fin d))
    (x : Vec d) (hx : x ∈ (I : Set (Vec d))) (n : ℕ) :
    (dyadicBoxAtDepth I x hx n : Set (Vec d)) ⊆
      Metric.closedBall x (‖I.upper - I.lower‖ / (2 : ℝ) ^ n) := by
  intro y hy
  rw [Metric.mem_closedBall, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (div_nonneg (norm_nonneg _) (by positivity))).2
  intro i
  rw [Real.norm_eq_abs]
  change |y i - x i| ≤ _
  have hxQ := mem_dyadicBoxAtDepth I x hx n i
  have hyQ := hy i
  change x i ∈ Set.Ioc
    ((dyadicDescendant I (dyadicPathAtDepth I x hx n)).lower i)
    ((dyadicDescendant I (dyadicPathAtDepth I x hx n)).upper i) at hxQ
  change y i ∈ Set.Ioc
    ((dyadicDescendant I (dyadicPathAtDepth I x hx n)).lower i)
    ((dyadicDescendant I (dyadicPathAtDepth I x hx n)).upper i) at hyQ
  rcases hxQ with ⟨hxlo, hxup⟩
  rcases hyQ with ⟨hylo, hyup⟩
  have hwidth := upper_sub_lower_dyadicDescendant I
    (dyadicPathAtDepth I x hx n) i
  rw [length_dyadicPathAtDepth I x hx n] at hwidth
  have hcoord : |y i - x i| ≤
      (I.upper i - I.lower i) / (2 : ℝ) ^ n := by
    rw [abs_le]
    constructor <;> linarith
  refine hcoord.trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hnonneg : 0 ≤ I.upper i - I.lower i := sub_nonneg.mpr (I.lower_le_upper i)
  rw [← abs_of_nonneg hnonneg]
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using
    ((pi_norm_le_iff_of_nonneg (norm_nonneg (I.upper - I.lower))).mp le_rfl i)

end PDE
