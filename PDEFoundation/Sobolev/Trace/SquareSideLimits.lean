module

public import PDEFoundation.Measure.SquareLoopFubini

/-!
# Limits on the actual sides of a good square

The common-radius construction controls the four sides on fixed enlarged open
intervals.  This file transfers that summable control to the actual closed
sides.  The one-dimensional integrability assumptions are explicit: they are
needed for set-integral monotonicity and prevent using the convention that a
nonintegrable Bochner integral is zero.
-/

@[expose] public section

namespace PDE

open Filter MeasureTheory Set

noncomputable section

/-- Dyadically summable enlarged side energy forces the squared errors on all
four actual closed square sides to vanish.  The comparison from each actual
side to its enlarged counterpart has constant `1`. -/
theorem tendsto_actual_square_side_scalar_error_integrals_of_summable
    {f : ℕ → Vec 2 → ℝ} {x₀ : Vec 2} {r ρ : ℝ}
    (_hr : 0 < r) (hρ : ρ ∈ Ioo r (2 * r))
    (hRightIntegrable : ∀ n, IntegrableOn
      (fun t : ℝ => f n (squarePoint (x₀ 0 + ρ) t) ^ 2)
      (Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r)))
    (hLeftIntegrable : ∀ n, IntegrableOn
      (fun t : ℝ => f n (squarePoint (x₀ 0 - ρ) t) ^ 2)
      (Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r)))
    (hTopIntegrable : ∀ n, IntegrableOn
      (fun t : ℝ => f n (squarePoint t (x₀ 1 + ρ)) ^ 2)
      (Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r)))
    (hBottomIntegrable : ∀ n, IntegrableOn
      (fun t : ℝ => f n (squarePoint t (x₀ 1 - ρ)) ^ 2)
      (Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r)))
    (hsum : Summable (fun n => (2 : ℝ) ^ n *
      enlargedSquareSideScalarEnergy (f n) x₀ r ρ)) :
    Tendsto (fun n =>
      ∫ t in Icc (x₀ 1 - ρ) (x₀ 1 + ρ),
        f n (squarePoint (x₀ 0 + ρ) t) ^ 2) atTop (nhds 0) ∧
    Tendsto (fun n =>
      ∫ t in Icc (x₀ 1 - ρ) (x₀ 1 + ρ),
        f n (squarePoint (x₀ 0 - ρ) t) ^ 2) atTop (nhds 0) ∧
    Tendsto (fun n =>
      ∫ t in Icc (x₀ 0 - ρ) (x₀ 0 + ρ),
        f n (squarePoint t (x₀ 1 + ρ)) ^ 2) atTop (nhds 0) ∧
    Tendsto (fun n =>
      ∫ t in Icc (x₀ 0 - ρ) (x₀ 0 + ρ),
        f n (squarePoint t (x₀ 1 - ρ)) ^ 2) atTop (nhds 0) := by
  have hsmallSide : Ioo (x₀ 1 - ρ) (x₀ 1 + ρ) ⊆
      Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r) := by
    intro t ht
    change x₀ 1 - ρ < t ∧ t < x₀ 1 + ρ at ht
    change x₀ 1 - 2 * r < t ∧ t < x₀ 1 + 2 * r
    constructor <;> linarith [hρ.2]
  have hsmallHorizontal : Ioo (x₀ 0 - ρ) (x₀ 0 + ρ) ⊆
      Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r) := by
    intro t ht
    change x₀ 0 - ρ < t ∧ t < x₀ 0 + ρ at ht
    change x₀ 0 - 2 * r < t ∧ t < x₀ 0 + 2 * r
    constructor <;> linarith [hρ.2]
  have hright : ∀ n,
      (∫ t in Icc (x₀ 1 - ρ) (x₀ 1 + ρ),
        f n (squarePoint (x₀ 0 + ρ) t) ^ 2) ≤
        enlargedSquareSideScalarEnergy (f n) x₀ r ρ := by
    intro n
    rw [integral_Icc_eq_integral_Ioo]
    have hmono :
        (∫ t in Ioo (x₀ 1 - ρ) (x₀ 1 + ρ),
          f n (squarePoint (x₀ 0 + ρ) t) ^ 2) ≤
        ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
          f n (squarePoint (x₀ 0 + ρ) t) ^ 2 :=
      setIntegral_mono_set (hRightIntegrable n)
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        (Filter.Eventually.of_forall hsmallSide)
    have hleftNonneg : 0 ≤
        ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
          f n (squarePoint (x₀ 0 - ρ) t) ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    have htopNonneg : 0 ≤
        ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
          f n (squarePoint t (x₀ 1 + ρ)) ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    have hbottomNonneg : 0 ≤
        ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
          f n (squarePoint t (x₀ 1 - ρ)) ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    unfold enlargedSquareSideScalarEnergy
    linarith
  have hleft : ∀ n,
      (∫ t in Icc (x₀ 1 - ρ) (x₀ 1 + ρ),
        f n (squarePoint (x₀ 0 - ρ) t) ^ 2) ≤
        enlargedSquareSideScalarEnergy (f n) x₀ r ρ := by
    intro n
    rw [integral_Icc_eq_integral_Ioo]
    have hmono :
        (∫ t in Ioo (x₀ 1 - ρ) (x₀ 1 + ρ),
          f n (squarePoint (x₀ 0 - ρ) t) ^ 2) ≤
        ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
          f n (squarePoint (x₀ 0 - ρ) t) ^ 2 :=
      setIntegral_mono_set (hLeftIntegrable n)
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        (Filter.Eventually.of_forall hsmallSide)
    have hrightNonneg : 0 ≤
        ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
          f n (squarePoint (x₀ 0 + ρ) t) ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    have htopNonneg : 0 ≤
        ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
          f n (squarePoint t (x₀ 1 + ρ)) ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    have hbottomNonneg : 0 ≤
        ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
          f n (squarePoint t (x₀ 1 - ρ)) ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    unfold enlargedSquareSideScalarEnergy
    linarith
  have htop : ∀ n,
      (∫ t in Icc (x₀ 0 - ρ) (x₀ 0 + ρ),
        f n (squarePoint t (x₀ 1 + ρ)) ^ 2) ≤
        enlargedSquareSideScalarEnergy (f n) x₀ r ρ := by
    intro n
    rw [integral_Icc_eq_integral_Ioo]
    have hmono :
        (∫ t in Ioo (x₀ 0 - ρ) (x₀ 0 + ρ),
          f n (squarePoint t (x₀ 1 + ρ)) ^ 2) ≤
        ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
          f n (squarePoint t (x₀ 1 + ρ)) ^ 2 :=
      setIntegral_mono_set (hTopIntegrable n)
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        (Filter.Eventually.of_forall hsmallHorizontal)
    have hrightNonneg : 0 ≤
        ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
          f n (squarePoint (x₀ 0 + ρ) t) ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    have hleftNonneg : 0 ≤
        ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
          f n (squarePoint (x₀ 0 - ρ) t) ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    have hbottomNonneg : 0 ≤
        ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
          f n (squarePoint t (x₀ 1 - ρ)) ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    unfold enlargedSquareSideScalarEnergy
    linarith
  have hbottom : ∀ n,
      (∫ t in Icc (x₀ 0 - ρ) (x₀ 0 + ρ),
        f n (squarePoint t (x₀ 1 - ρ)) ^ 2) ≤
        enlargedSquareSideScalarEnergy (f n) x₀ r ρ := by
    intro n
    rw [integral_Icc_eq_integral_Ioo]
    have hmono :
        (∫ t in Ioo (x₀ 0 - ρ) (x₀ 0 + ρ),
          f n (squarePoint t (x₀ 1 - ρ)) ^ 2) ≤
        ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
          f n (squarePoint t (x₀ 1 - ρ)) ^ 2 :=
      setIntegral_mono_set (hBottomIntegrable n)
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        (Filter.Eventually.of_forall hsmallHorizontal)
    have hrightNonneg : 0 ≤
        ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
          f n (squarePoint (x₀ 0 + ρ) t) ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    have hleftNonneg : 0 ≤
        ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
          f n (squarePoint (x₀ 0 - ρ) t) ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    have htopNonneg : 0 ≤
        ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
          f n (squarePoint t (x₀ 1 + ρ)) ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    unfold enlargedSquareSideScalarEnergy
    linarith
  have hweight : ∀ n,
      enlargedSquareSideScalarEnergy (f n) x₀ r ρ ≤
        (2 : ℝ) ^ n * enlargedSquareSideScalarEnergy (f n) x₀ r ρ := by
    intro n
    calc
      enlargedSquareSideScalarEnergy (f n) x₀ r ρ =
          1 * enlargedSquareSideScalarEnergy (f n) x₀ r ρ := (one_mul _).symm
      _ ≤ (2 : ℝ) ^ n * enlargedSquareSideScalarEnergy (f n) x₀ r ρ :=
        mul_le_mul_of_nonneg_right
          (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
          (enlargedSquareSideScalarEnergy_nonneg (f n) x₀ r ρ)
  have hrightNonneg : ∀ n, 0 ≤
      ∫ t in Icc (x₀ 1 - ρ) (x₀ 1 + ρ),
        f n (squarePoint (x₀ 0 + ρ) t) ^ 2 := by
    intro n
    rw [integral_Icc_eq_integral_Ioo]
    exact integral_nonneg fun _ => sq_nonneg _
  have hleftNonneg : ∀ n, 0 ≤
      ∫ t in Icc (x₀ 1 - ρ) (x₀ 1 + ρ),
        f n (squarePoint (x₀ 0 - ρ) t) ^ 2 := by
    intro n
    rw [integral_Icc_eq_integral_Ioo]
    exact integral_nonneg fun _ => sq_nonneg _
  have htopNonneg : ∀ n, 0 ≤
      ∫ t in Icc (x₀ 0 - ρ) (x₀ 0 + ρ),
        f n (squarePoint t (x₀ 1 + ρ)) ^ 2 := by
    intro n
    rw [integral_Icc_eq_integral_Ioo]
    exact integral_nonneg fun _ => sq_nonneg _
  have hbottomNonneg : ∀ n, 0 ≤
      ∫ t in Icc (x₀ 0 - ρ) (x₀ 0 + ρ),
        f n (squarePoint t (x₀ 1 - ρ)) ^ 2 := by
    intro n
    rw [integral_Icc_eq_integral_Ioo]
    exact integral_nonneg fun _ => sq_nonneg _
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hsum.tendsto_atTop_zero
      (Filter.Eventually.of_forall hrightNonneg) ?_
    filter_upwards with n
    exact (hright n).trans (hweight n)
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hsum.tendsto_atTop_zero
      (Filter.Eventually.of_forall hleftNonneg) ?_
    filter_upwards with n
    exact (hleft n).trans (hweight n)
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hsum.tendsto_atTop_zero
      (Filter.Eventually.of_forall htopNonneg) ?_
    filter_upwards with n
    exact (htop n).trans (hweight n)
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hsum.tendsto_atTop_zero
      (Filter.Eventually.of_forall hbottomNonneg) ?_
    filter_upwards with n
    exact (hbottom n).trans (hweight n)

end

end PDE
