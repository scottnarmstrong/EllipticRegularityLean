module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.HahnBanach


/-! # Lions representation

This is an adapted copy of `KineticCoarse.WholeSpace.lions_representation` from
`KineticCoarse/WholeSpace/WellposedLions.lean` in the
`hypoelliptic-coarse-graining` repository. Attribution is retained here because the argument and
API are ported from that source. The theorem is the abstract input for the whole-space parabolic
Cauchy construction.
-/

@[expose] public section

set_option autoImplicit false

open scoped InnerProductSpace

namespace PDE.Parabolic.Lions

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Lions representation theorem.** If `J` and `T` are linear maps into a real Hilbert space
and `⟪J φ, T φ⟫` controls `‖J φ‖²`, then every continuous functional of the form
`φ ↦ ⟪f, J φ⟫` is represented as `φ ↦ ⟪z, T φ⟫` by an element `z` in the closure of the range
of `J`. -/
theorem lions_representation_with_norm_bound (J T : V →ₗ[ℝ] X) {α : ℝ} (hα : 0 < α)
    (hcoer : ∀ φ, α * ‖J φ‖ ^ 2 ≤ ⟪J φ, T φ⟫_ℝ) (f : X) :
    ∃ z ∈ (LinearMap.range J).topologicalClosure,
      (∀ φ, ⟪z, T φ⟫_ℝ = ⟪f, J φ⟫_ℝ) ∧ ‖z‖ ≤ ‖f‖ / α := by
  set K := (LinearMap.range J).topologicalClosure with hK
  have hKc : IsClosed (K : Set X) := Submodule.isClosed_topologicalClosure _
  have : CompleteSpace K := hKc.completeSpace_coe
  let P : X →L[ℝ] X := K.starProjection
  let T' : V →ₗ[ℝ] X := P.toLinearMap ∘ₗ T
  have hJK : ∀ φ, J φ ∈ K := fun φ =>
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self J φ)
  -- Coercivity survives the orthogonal projection.
  have hinner : ∀ φ, ⟪J φ, T' φ⟫_ℝ = ⟪J φ, T φ⟫_ℝ := by
    intro φ
    change ⟪J φ, K.starProjection (T φ)⟫_ℝ = _
    rw [← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 (hJK φ)]
  have hlow : ∀ φ, α * ‖J φ‖ ≤ ‖T' φ‖ := by
    intro φ
    have h1 := hcoer φ
    rw [← hinner] at h1
    have h2 := real_inner_le_norm (J φ) (T' φ)
    rcases eq_or_lt_of_le (norm_nonneg (J φ)) with h0 | hpos
    · rw [← h0]; simp
    · have hmul : α * ‖J φ‖ ^ 2 ≤ ‖J φ‖ * ‖T' φ‖ := h1.trans h2
      nlinarith
  -- The functional on the range of `T'`.
  let L : V →ₗ[ℝ] ℝ := (innerₛₗ ℝ f).comp J
  have hker : LinearMap.ker T' ≤ LinearMap.ker L := by
    intro φ hφ
    rw [LinearMap.mem_ker] at hφ ⊢
    have h := hlow φ
    rw [hφ, norm_zero] at h
    have hJ : ‖J φ‖ = 0 :=
      le_antisymm (by nlinarith [norm_nonneg (J φ)]) (norm_nonneg _)
    simp [L, norm_eq_zero.1 hJ]
  let ℓ₀ : LinearMap.range T' →ₗ[ℝ] ℝ :=
    ((LinearMap.ker T').liftQ L hker).comp T'.quotKerEquivRange.symm.toLinearMap
  have hℓ₀ : ∀ φ, ℓ₀ ⟨T' φ, LinearMap.mem_range_self T' φ⟩ = L φ := by
    intro φ
    have hquot : T'.quotKerEquivRange.symm ⟨T' φ, LinearMap.mem_range_self T' φ⟩ =
        Submodule.Quotient.mk φ := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [ℓ₀, LinearMap.comp_apply, LinearEquiv.coe_coe, hquot, Submodule.liftQ_apply]
  have hbound : ∀ y : LinearMap.range T', ‖ℓ₀ y‖ ≤ (‖f‖ / α) * ‖y‖ := by
    rintro ⟨y, φ, rfl⟩
    rw [hℓ₀ φ]
    have h1 : ‖L φ‖ ≤ ‖f‖ * ‖J φ‖ := by
      change |⟪f, J φ⟫_ℝ| ≤ _
      exact abs_real_inner_le_norm f (J φ)
    have h2 : ‖J φ‖ ≤ ‖T' φ‖ / α := by
      rw [le_div_iff₀ hα, mul_comm]
      exact hlow φ
    calc
      ‖L φ‖ ≤ ‖f‖ * ‖J φ‖ := h1
      _ ≤ ‖f‖ * (‖T' φ‖ / α) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = (‖f‖ / α) * ‖(⟨T' φ, LinearMap.mem_range_self T' φ⟩ : LinearMap.range T')‖ := by
        rw [show ‖(⟨T' φ, LinearMap.mem_range_self T' φ⟩ : LinearMap.range T')‖ = ‖T' φ‖
          from rfl]
        ring
  let ℓ : StrongDual ℝ (LinearMap.range T') := ℓ₀.mkContinuous (‖f‖ / α) hbound
  obtain ⟨ℓ', hℓ', hℓ'norm⟩ := exists_extension_norm_eq (LinearMap.range T') ℓ
  let z₀ : X := (InnerProductSpace.toDual ℝ X).symm ℓ'
  refine ⟨P z₀, ?_, ?_, ?_⟩
  · change K.starProjection z₀ ∈ K
    rw [Submodule.starProjection_apply]
    exact Submodule.coe_mem _
  · intro φ
    have h1 : ⟪P z₀, T φ⟫_ℝ = ⟪z₀, T' φ⟫_ℝ := by
      change ⟪K.starProjection z₀, T φ⟫_ℝ = ⟪z₀, K.starProjection (T φ)⟫_ℝ
      exact Submodule.inner_starProjection_left_eq_right K z₀ (T φ)
    rw [h1, InnerProductSpace.toDual_symm_apply]
    have h2 := hℓ' ⟨T' φ, LinearMap.mem_range_self T' φ⟩
    simp only at h2
    rw [h2]
    change ℓ₀ ⟨T' φ, LinearMap.mem_range_self T' φ⟩ = _
    rw [hℓ₀ φ]
    simp [L]
  · calc
      ‖P z₀‖ ≤ ‖z₀‖ := K.norm_starProjection_apply_le z₀
      _ = ‖ℓ'‖ := by
        dsimp [z₀]
        exact (InnerProductSpace.toDual ℝ X).symm.norm_map ℓ'
      _ = ‖ℓ‖ := hℓ'norm
      _ ≤ ‖f‖ / α := by
        dsimp [ℓ]
        exact LinearMap.mkContinuous_norm_le _ (div_nonneg (norm_nonneg _) hα.le) hbound

/-- **Lions representation theorem.** If `J` and `T` are linear maps into a real Hilbert space
and `⟪J φ, T φ⟫` controls `‖J φ‖²`, then every continuous functional of the form
`φ ↦ ⟪f, J φ⟫` is represented as `φ ↦ ⟪z, T φ⟫` by an element `z` in the closure of the range
of `J`. -/
theorem lions_representation (J T : V →ₗ[ℝ] X) {α : ℝ} (hα : 0 < α)
    (hcoer : ∀ φ, α * ‖J φ‖ ^ 2 ≤ ⟪J φ, T φ⟫_ℝ) (f : X) :
    ∃ z ∈ (LinearMap.range J).topologicalClosure, ∀ φ, ⟪z, T φ⟫_ℝ = ⟪f, J φ⟫_ℝ := by
  obtain ⟨z, hz, hrep, -⟩ := lions_representation_with_norm_bound J T hα hcoer f
  exact ⟨z, hz, hrep⟩

end PDE.Parabolic.Lions
