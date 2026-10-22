module

public import EllipticRegularity.Parabolic.Sobolev.EndpointTransfer

/-!
# All-dimensional parabolic spatial Gagliardo--Nirenberg estimates

The endpoint proofs in dimensions one and two complement the Sobolev
interpolation estimate in dimensions at least three.  This module exposes the
same powered energy inequality uniformly for every positive dimension.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic

open MeasureTheory Set

/-- Whole-space spatial Gagliardo--Nirenberg inequality in every positive
dimension, in the powered energy form used by parabolic iteration.  The
finite constant depends only on `d`. -/
theorem exists_spatial_gagliardo_nirenberg_energy_constant
    (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ u : H1Function (Set.univ : Set (Vec d)),
        (eLpNorm u.toFun (ENNReal.ofReal (2 * ((d : ℝ) + 2) / d)) volume) ^
              (2 * ((d : ℝ) + 2) / d) ≤
          C * (eLpNorm u.toFun 2 volume) ^ (4 / (d : ℝ)) *
              (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 volume) ^
                (2 : ℝ) := by
  by_cases hlarge : 3 ≤ d
  · obtain ⟨C, hC, hGN⟩ :=
      exists_spatial_gagliardo_nirenberg_energy_constant_ge_three d hlarge
    refine ⟨(ENNReal.ofReal C) ^ (2 : ℝ),
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top, ?_⟩
    exact hGN
  · have hsmall : d = 1 ∨ d = 2 := by omega
    rcases hsmall with h1 | h2
    · subst d
      refine ⟨ENNReal.ofReal 4, ENNReal.ofReal_ne_top, fun u => ?_⟩
      have h := h1_one_dimensional_gagliardo_nirenberg_energy u
      convert h using 1 <;> norm_num
    · subst d
      let k : ℝ := 4 * (sobolevOneConstant 2 : ℝ)
      refine ⟨(ENNReal.ofReal k) ^ (2 : ℝ),
        ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top, fun u => ?_⟩
      have h := h1_two_dimensional_gagliardo_nirenberg_energy u
      convert h using 1 <;> norm_num [k]

/-- Time-integrated parabolic Gagliardo--Nirenberg inequality for a
measurable family of whole-space `H¹` slices, in every positive dimension.
`S` bounds the essential supremum of the squared spatial `L²` norm. -/
theorem exists_time_integrated_gagliardo_nirenberg_constant
    (d : ℕ) (hd : 1 ≤ d) {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (u : α → H1Function (Set.univ : Set (Vec d)))
    (S : ℝ≥0∞)
    (hS : ∀ᵐ t ∂μ, (eLpNorm (u t).toFun 2 volume) ^ (2 : ℝ) ≤ S)
    (hD : Measurable fun t =>
      (eLpNorm (fun x => vecEuclideanNorm ((u t).grad x)) 2 volume) ^ (2 : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∫⁻ t,
          (eLpNorm (u t).toFun
              (ENNReal.ofReal (2 * ((d : ℝ) + 2) / d)) volume) ^
                (2 * ((d : ℝ) + 2) / d) ∂μ ≤
        C * S ^ (2 / (d : ℝ)) *
          ∫⁻ t,
            (eLpNorm (fun x => vecEuclideanNorm ((u t).grad x)) 2 volume) ^
                (2 : ℝ) ∂μ := by
  obtain ⟨C, hC, hspace⟩ :=
    exists_spatial_gagliardo_nirenberg_energy_constant d hd
  let A : α → ℝ≥0∞ := fun t =>
    (eLpNorm (u t).toFun
      (ENNReal.ofReal (2 * ((d : ℝ) + 2) / d)) volume) ^
        (2 * ((d : ℝ) + 2) / d)
  let B : α → ℝ≥0∞ := fun t =>
    (eLpNorm (u t).toFun 2 volume) ^ (2 : ℝ)
  let D : α → ℝ≥0∞ := fun t =>
    (eLpNorm (fun x => vecEuclideanNorm ((u t).grad x)) 2 volume) ^ (2 : ℝ)
  have hGN : ∀ᵐ t ∂μ, A t ≤ C * B t ^ (2 / (d : ℝ)) * D t :=
    Filter.Eventually.of_forall fun t => by
      have hBpow (t : α) :
          (eLpNorm (u t).toFun 2 volume) ^ (4 / (d : ℝ)) =
            B t ^ (2 / (d : ℝ)) := by
        dsimp [B]
        rw [show (4 / (d : ℝ)) = (2 : ℝ) * (2 / (d : ℝ)) by
          have hdne : (d : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (by omega : 0 < d))
          field_simp
          ring]
        rw [ENNReal.rpow_mul]
      rw [← hBpow t]
      simpa only [A, B, D, ENNReal.rpow_natCast] using hspace (u t)
  have hCfinite : C ≠ ∞ := hC
  refine ⟨C, hCfinite, ?_⟩
  simpa only [A, B, D] using
    lintegral_le_of_ae_gagliardo_nirenberg μ d hd C S hD hS hGN

end PDE.Parabolic
