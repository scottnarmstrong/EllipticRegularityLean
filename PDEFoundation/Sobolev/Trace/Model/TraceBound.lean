module

public import PDEFoundation.Sobolev.Trace.Model.Hardy
public import PDEFoundation.Sobolev.Trace.Model.TraceLp
public import PDEFoundation.Sobolev.Trace.Model.TraceGagliardo

/-!
# Trace bounds on the half-space model

This module collects the three results of Steps 1-3 of the proof of the trace theorem on the
half-space `Vec n × (0, ∞)`:

* `PDE.TraceLane.hardy_lintegral` (Hardy's inequality, `Hardy.lean`);
* `PDE.TraceLane.model_trace_Lp` (the `L^p` bound of the trace, `TraceLp.lean`);
* `PDE.TraceLane.model_trace_gagliardo` (the Gagliardo seminorm of the trace, below).

The vertical and horizontal pieces of Step 3 live in `TraceVertical`, `TraceHorizontal`,
`TraceKernel` and `TraceGagliardo`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped ENNReal NNReal

/-- On `Vec 0` (a point) the Gagliardo seminorm vanishes. -/
theorem flatGagliardo_zero (q p : ℝ) (hp : 0 < p) (w : Vec 0 → ℝ) : flatGagliardo 0 q p w = 0 := by
  unfold flatGagliardo
  have : ∀ x' y' : Vec 0, ENNReal.ofReal (|w x' - w y'| ^ p / vecEuclideanNorm (x' - y') ^ q) = 0 := by
    intro x' y'
    rw [Subsingleton.elim x' y']
    simp [Real.zero_rpow hp.ne']
  rw [lintegral_congr (fun x' => lintegral_congr (fun y' => this x' y'))]
  simp

/-- Manuscript Steps 2-3: the Gagliardo seminorm of the trace on the half-space. -/
theorem model_trace_gagliardo (n : ℕ) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ≥0, ∀ v : Vec n × ℝ → ℝ, ContDiffOn ℝ 1 v (closedUpperHalf n) →
      (∃ K, IsCompact K ∧ ∀ z ∉ K, v z = 0) →
      flatGagliardo n (n + p - 1) p (fun x' => v (x', 0)) ≤
        (C : ℝ≥0∞) * ∫⁻ z in upperHalf n, ENNReal.ofReal (modelGradNorm v z ^ p) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, fun v _ _ => ?_⟩
    rw [flatGagliardo_zero _ _ (by linarith)]
    exact zero_le
  · have : NeZero n := ⟨hn.ne'⟩
    obtain ⟨C, hC⟩ := model_trace_gagliardo_pos n hp
    exact ⟨C, fun v hv _ => hC v hv⟩

end PDE.TraceLane
