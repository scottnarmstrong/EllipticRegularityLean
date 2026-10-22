module

public import EllipticRegularity.Parabolic.WeakHarnack.LogEstimateSliceA
public import EllipticRegularity.Parabolic.Sobolev.ParabolicSlices
public import PDEFoundation.Sobolev.Ch4.ChainRule

/-!
# Time slices of `G ∘ u` and the per-slice lower bound
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PDE.Parabolic.WeakHarnack

variable {d : ℕ}

/-- For a.e. `t`, the slice `x ↦ G (u (x,t))` is an `H¹(B₁)` function with gradient
`G'(u) ∇u`. -/
theorem logSlice_ae {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ s, |deriv G s| ≤ M)
    (u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)) :
    ∀ᵐ t ∂(volume.restrict (Ioc (-1 : ℝ) 0)),
      ∃ h : H1Function (euclideanBall (0 : Vec d) 1),
        (∀ x, h.toFun x = G (u.toFun (x, t))) ∧
          ∀ x, h.grad x = deriv G (u.toFun (x, t)) • u.grad (x, t) := by
  filter_upwards [ae_parH1_slice_h1 (isOpen_euclideanBall 0 1) u] with t ht
  obtain ⟨v, hv, hg⟩ := ht
  refine ⟨PDE.Ch4Infra.compOpen (isOpen_euclideanBall 0 1) (volume_euclideanBall_ne_top 0
    zero_le_one) v hG hM0 hM, fun x => ?_, fun x => ?_⟩
  · simp [hv, parSlice]
  · ext i
    simp [hv, hg, parSlice]

/-- Per-slice lower bound in terms of `logQ`. -/
theorem logSlice_lower_Q {Λ : ℝ} (hΛ : 0 ≤ Λ) {G : ℝ → ℝ}
    (u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)) {t : ℝ}
    (h : H1Function (euclideanBall (0 : Vec d) 1))
    (hh : ∀ x, h.toFun x = G (u.toFun (x, t)))
    (hg : ∀ x, h.grad x = deriv G (u.toFun (x, t)) • u.grad (x, t)) :
    logTailC d * (∫ x, (G (u.toFun (x, t)) -
        ∫ y, G (u.toFun (y, t)) ∂(cutoffMeasure d)) ^ 2 ∂(cutoffMeasure d)) - Λ * logTailK0 d ≤
      (cutoffZ d)⁻¹ * ∫ x in euclideanBall (0 : Vec d) 1, logQ Λ G u (x, t) := by
  have := logSlice_lower hΛ h
  simp only [hh, hg] at this
  unfold logQ
  exact this

end PDE.Parabolic.WeakHarnack
