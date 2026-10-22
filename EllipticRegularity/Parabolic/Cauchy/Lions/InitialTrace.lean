module

public import EllipticRegularity.Parabolic.Cauchy.Lions.LionsRepresentation
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! # Lions representation with an initial trace

The Cauchy construction pairs the initial datum with the trace of the test function at the initial
time. This corollary packages that trace as a second Hilbert-space component. Coercivity must then
control both the space-time graph norm and the initial trace norm.
-/

@[expose] public section

set_option autoImplicit false

open scoped InnerProductSpace

namespace PDE.Parabolic.Lions

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The value and initial-trace components of a test function. -/
noncomputable def initialTraceMap (J : V →ₗ[ℝ] X) (γ : V →ₗ[ℝ] Y) :
    V →ₗ[ℝ] WithLp 2 (X × Y) where
  toFun φ := WithLp.toLp 2 (J φ, γ φ)
  map_add' φ ψ := by
    apply (WithLp.equiv 2 (X × Y)).injective
    simp
  map_smul' c φ := by
    apply (WithLp.equiv 2 (X × Y)).injective
    simp

/-- The test operator placed in the space-time component, with zero trace component. -/
noncomputable def initialTraceOperator (T : V →ₗ[ℝ] X) :
    V →ₗ[ℝ] WithLp 2 (X × Y) where
  toFun φ := WithLp.toLp 2 (T φ, 0)
  map_add' φ ψ := by
    apply (WithLp.equiv 2 (X × Y)).injective
    simp
  map_smul' c φ := by
    apply (WithLp.equiv 2 (X × Y)).injective
    simp

/-- Lions representation when the right-hand side is paired with a test-function trace.

The coercivity hypothesis explicitly controls the `J` norm and the trace norm. The result is a
pair `(z, z₀)` in the closure of the joint graph of `(J, γ)`, and its first component represents
the functional `φ ↦ ⟪f, γ φ⟫` against `T`.
-/
theorem lions_representation_initial_trace
    (J T : V →ₗ[ℝ] X) (γ : V →ₗ[ℝ] Y) {α : ℝ} (hα : 0 < α)
    (hcoer : ∀ φ, α * (‖J φ‖ ^ 2 + ‖γ φ‖ ^ 2) ≤ ⟪J φ, T φ⟫_ℝ) (f : Y) :
    ∃ z : WithLp 2 (X × Y),
      z ∈ (LinearMap.range (initialTraceMap J γ)).topologicalClosure ∧
      ∀ φ, ⟪z, initialTraceOperator T φ⟫_ℝ =
        ⟪WithLp.toLp 2 (0, f), initialTraceMap J γ φ⟫_ℝ := by
  let J' : V →ₗ[ℝ] WithLp 2 (X × Y) := initialTraceMap J γ
  let T' : V →ₗ[ℝ] WithLp 2 (X × Y) := initialTraceOperator T
  have hcoer' : ∀ φ, α * ‖J' φ‖ ^ 2 ≤ ⟪J' φ, T' φ⟫_ℝ := by
    intro φ
    have hnorm : ‖J' φ‖ ^ 2 = ‖J φ‖ ^ 2 + ‖γ φ‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2]
      rfl
    rw [hnorm, WithLp.prod_inner_apply]
    simpa [J', T', initialTraceMap, initialTraceOperator] using hcoer φ
  let f' : WithLp 2 (X × Y) := WithLp.toLp 2 (0, f)
  obtain ⟨z, hz, hrep⟩ :=
    lions_representation J' T' hα hcoer' f'
  refine ⟨z, hz, ?_⟩
  intro φ
  simpa [J', T', f', initialTraceMap, initialTraceOperator] using hrep φ

/-- Component form of `lions_representation_initial_trace`. The represented space-time component
and trace component are returned separately, while their pair remains in the closure of the joint
test-function graph. -/
theorem lions_representation_initial_trace_components
    (J T : V →ₗ[ℝ] X) (γ : V →ₗ[ℝ] Y) {α : ℝ} (hα : 0 < α)
    (hcoer : ∀ φ, α * (‖J φ‖ ^ 2 + ‖γ φ‖ ^ 2) ≤ ⟪J φ, T φ⟫_ℝ) (f : Y) :
    ∃ z : X, ∃ z₀ : Y,
      WithLp.toLp 2 (z, z₀) ∈
        (LinearMap.range (initialTraceMap J γ)).topologicalClosure ∧
      ∀ φ, ⟪z, T φ⟫_ℝ = ⟪f, γ φ⟫_ℝ := by
  obtain ⟨w, hw, hrep⟩ := lions_representation_initial_trace J T γ hα hcoer f
  let p := WithLp.ofLp w
  refine ⟨p.1, p.2, ?_, ?_⟩
  · change WithLp.toLp 2 (WithLp.ofLp w) ∈ _
    simpa using hw
  · intro φ
    have h := hrep φ
    rw [WithLp.prod_inner_apply] at h
    simpa [p, initialTraceMap, initialTraceOperator] using h

/-- The component form of the initial-trace representation, with the norm bound inherited from
the abstract Hahn--Banach representation. -/
theorem lions_representation_initial_trace_components_norm_bound
    (J T : V →ₗ[ℝ] X) (γ : V →ₗ[ℝ] Y) {α : ℝ} (hα : 0 < α)
    (hcoer : ∀ φ, α * (‖J φ‖ ^ 2 + ‖γ φ‖ ^ 2) ≤ ⟪J φ, T φ⟫_ℝ) (f : Y) :
    ∃ z : X, ∃ z₀ : Y,
      WithLp.toLp 2 (z, z₀) ∈
        (LinearMap.range (initialTraceMap J γ)).topologicalClosure ∧
      (∀ φ, ⟪z, T φ⟫_ℝ = ⟪f, γ φ⟫_ℝ) ∧
      ‖WithLp.toLp 2 (z, z₀)‖ ≤ ‖f‖ / α := by
  let J' : V →ₗ[ℝ] WithLp 2 (X × Y) := initialTraceMap J γ
  let T' : V →ₗ[ℝ] WithLp 2 (X × Y) := initialTraceOperator T
  have hcoer' : ∀ φ, α * ‖J' φ‖ ^ 2 ≤ ⟪J' φ, T' φ⟫_ℝ := by
    intro φ
    have hnorm : ‖J' φ‖ ^ 2 = ‖J φ‖ ^ 2 + ‖γ φ‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2]
      rfl
    rw [hnorm, WithLp.prod_inner_apply]
    simpa [J', T', initialTraceMap, initialTraceOperator] using hcoer φ
  let f' : WithLp 2 (X × Y) := WithLp.toLp 2 ((0 : X), f)
  obtain ⟨w, hw, hrep, hnorm⟩ :=
    lions_representation_with_norm_bound J' T' hα hcoer' f'
  let p := WithLp.ofLp w
  refine ⟨p.1, p.2, ?_, ?_, ?_⟩
  · change WithLp.toLp 2 (WithLp.ofLp w) ∈ _
    simpa using hw
  · intro φ
    have h := hrep φ
    rw [WithLp.prod_inner_apply] at h
    simpa [p, J', T', f', initialTraceMap, initialTraceOperator] using h
  · have hp : WithLp.toLp 2 (p.1, p.2) = w := by
      change WithLp.toLp 2 (WithLp.ofLp w) = w
      simp
    rw [hp]
    simpa [f'] using hnorm

end PDE.Parabolic.Lions
