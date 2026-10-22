module

public import EllipticRegularity.DeGiorgi.Holder.Interface
public import EllipticRegularity.DeGiorgi.Holder.Scaling
public import PDEFoundation.Regularity.EssentialOscillationHolder
public import Mathlib.Analysis.Complex.ExponentialBounds
public import PDEFoundation.Geometry.EuclideanBall.Topology

/-!
# One step of oscillation decay from expansion of positivity

Given the expansion-of-positivity statement, class stability under affine changes
of the solution, and stability under rescaling of balls, the essential range of a
solution on `B_ρ(z)` contracts by the factor `1 - δ` on `B_{ρ/2}(z)`, where
`δ = exp (-(Ce + 1) Λ ^ ((d + 2) / 4))`.  This is inequality (4.53) of the manuscript.
-/

@[expose] public section

namespace PDE.DGNMHolder

open PDE MeasureTheory

variable {d : ℕ}

/-- The contraction constant `δ` of the oscillation decay. -/
noncomputable def decayConst (d : ℕ) (Ce Λ : ℝ) : ℝ :=
  Real.exp (-((Ce + 1) * Λ ^ (((d : ℝ) + 2) / 4)))

theorem decayConst_pos (d : ℕ) (Ce Λ : ℝ) : 0 < decayConst d Ce Λ := Real.exp_pos _

theorem decayConst_le_half {Ce Λ : ℝ} (d : ℕ) (hCe : 0 < Ce) (hΛ : 1 ≤ Λ) :
    decayConst d Ce Λ ≤ 1 / 2 := by
  have hone : (1 : ℝ) ≤ Λ ^ (((d : ℝ) + 2) / 4) :=
    Real.one_le_rpow hΛ (by positivity)
  unfold decayConst
  have h1 : -((Ce + 1) * Λ ^ (((d : ℝ) + 2) / 4)) ≤ -1 := by nlinarith
  calc Real.exp (-((Ce + 1) * Λ ^ (((d : ℝ) + 2) / 4))) ≤ Real.exp (-1) := Real.exp_le_exp.2 h1
    _ ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_eq_one_div]
      have := Real.exp_one_gt_two
      rw [div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]
      linarith

theorem decayConst_le_expansion {Ce Λ : ℝ} (d : ℕ) (hCe : 0 < Ce) (hΛ : 1 ≤ Λ) :
    decayConst d Ce Λ ≤
      Real.exp (-(Ce * (1 / 2 : ℝ) ^ ((1 : ℝ) / d) * Λ ^ (((d : ℝ) + 2) / 4))) / 2 := by
  set X : ℝ := Λ ^ (((d : ℝ) + 2) / 4) with hX
  have hX1 : (1 : ℝ) ≤ X := Real.one_le_rpow hΛ (by positivity)
  have hhalf : (1 / 2 : ℝ) ^ ((1 : ℝ) / d) ≤ 1 :=
    Real.rpow_le_one (by norm_num) (by norm_num) (by positivity)
  have hexp : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    have := Real.exp_one_gt_two
    rw [div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  unfold decayConst
  rw [← hX]
  have h1 : -((Ce + 1) * X) = -(Ce * X) + -X := by ring
  have h2 : Real.exp (-X) ≤ 1 / 2 :=
    (Real.exp_le_exp.2 (by linarith)).trans hexp
  have h3 : Real.exp (-(Ce * X)) ≤ Real.exp (-(Ce * (1 / 2 : ℝ) ^ ((1 : ℝ) / d) * X)) := by
    apply Real.exp_le_exp.2
    have : Ce * (1 / 2 : ℝ) ^ ((1 : ℝ) / d) * X ≤ Ce * X := by
      have : Ce * X * (1 / 2 : ℝ) ^ ((1 : ℝ) / d) ≤ Ce * X * 1 :=
        mul_le_mul_of_nonneg_left hhalf (by positivity)
      linarith
    linarith
  rw [h1, Real.exp_add]
  calc Real.exp (-(Ce * X)) * Real.exp (-X)
      ≤ Real.exp (-(Ce * X)) * (1 / 2) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ ≤ Real.exp (-(Ce * (1 / 2 : ℝ) ^ ((1 : ℝ) / d) * X)) * (1 / 2) :=
        mul_le_mul_of_nonneg_right h3 (by norm_num)
    _ = _ := by ring

/-- Essential range bounds pull back under `y ↦ ρ • y + z`. -/
theorem range_scale_fwd {ρ : ℝ} (hρ : 0 < ρ) {z : Vec d} {f w : Vec d → ℝ} {m M : ℝ}
    (hw : w =ᵐ[volumeOn (euclideanBall (0 : Vec d) 1)] fun y => f (ρ • y + z))
    (hr : EssentialRangeBoundsOn f (euclideanBall z ρ) m M) :
    ∀ᵐ y ∂volumeOn (euclideanBall (0 : Vec d) 1), w y ∈ Set.Icc m M := by
  have h1 : ∀ᵐ y ∂volumeOn (euclideanBall (0 : Vec d) 1), f (ρ • y + z) ∈ Set.Icc m M :=
    (ae_affine_ball_iff hρ z 1 (fun x => f x ∈ Set.Icc m M)).2 (by rw [mul_one]; exact hr)
  filter_upwards [h1, hw] with y h1 h2
  rw [h2]; exact h1

/-- Essential range bounds on the half ball push forward under `y ↦ ρ • y + z`. -/
theorem range_scale_back {ρ : ℝ} (hρ : 0 < ρ) {z : Vec d} {f w : Vec d → ℝ} {m M : ℝ}
    (hw : w =ᵐ[volumeOn (euclideanBall (0 : Vec d) 1)] fun y => f (ρ • y + z))
    (h : ∀ᵐ y ∂volumeOn (euclideanBall (0 : Vec d) (1 / 2)), w y ∈ Set.Icc m M) :
    EssentialRangeBoundsOn f (euclideanBall z (ρ / 2)) m M := by
  have hsub : euclideanBall (0 : Vec d) (1 / 2) ⊆ euclideanBall (0 : Vec d) 1 :=
    euclideanBall_mono (by norm_num) (by norm_num)
  have hw' := ae_restrict_of_ae_restrict_of_subset hsub hw
  have h1 : ∀ᵐ y ∂volumeOn (euclideanBall (0 : Vec d) (1 / 2)), f (ρ • y + z) ∈ Set.Icc m M := by
    filter_upwards [h, hw'] with y h1 h2
    rw [← h2]; exact h1
  have := (ae_affine_ball_iff hρ z (1 / 2) (fun x => f x ∈ Set.Icc m M)).1 h1
  rwa [show ρ * (1 / 2) = ρ / 2 by ring] at this

theorem volumeOn_euclideanBall_ne_zero {z : Vec d} {ρ : ℝ} (hρ : 0 < ρ) :
    volumeOn (euclideanBall z ρ) ≠ 0 := by
  intro h
  have hpos : 0 < volume (euclideanBall z ρ) :=
    (isOpen_euclideanBall z ρ).measure_pos volume ⟨z, center_mem_euclideanBall z hρ⟩
  have := congrArg (fun μ : Measure (Vec d) => μ Set.univ) h
  simp [volumeOn] at this
  exact hpos.ne' this

theorem le_of_essentialRange {f : Vec d → ℝ} {z : Vec d} {ρ m M : ℝ} (hρ : 0 < ρ)
    (h : EssentialRangeBoundsOn f (euclideanBall z ρ) m M) : m ≤ M := by
  have : (ae (volumeOn (euclideanBall z ρ))).NeBot :=
    ae_neBot.2 (volumeOn_euclideanBall_ne_zero hρ)
  obtain ⟨x, hx⟩ := h.exists
  exact hx.1.trans hx.2

end PDE.DGNMHolder
