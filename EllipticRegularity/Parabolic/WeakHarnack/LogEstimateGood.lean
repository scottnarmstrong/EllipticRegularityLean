module

public import EllipticRegularity.Parabolic.WeakHarnack.LogEstimateVar

/-!
# Good times for the logarithmic estimate

Outside a null set of times, the slice of `G ∘ u` is `H¹(B₁)` and the slice of `u` is a.e.
nonnegative; there `log (u + ε) = G ∘ u` `ν`-a.e. and the `ν`-statistics of the two agree.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PDE.Parabolic.WeakHarnack

variable {d : ℕ}

theorem logGood_null {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ s, |deriv G s| ≤ M)
    (u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hu0 : ∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
      0 ≤ u.toFun z) :
    ∃ N : Set ℝ, volume N = 0 ∧ ∀ t ∈ Ioc (-1 : ℝ) 0, t ∉ N →
      (∃ h : H1Function (euclideanBall (0 : Vec d) 1),
        (∀ x, h.toFun x = G (u.toFun (x, t))) ∧
          ∀ x, h.grad x = deriv G (u.toFun (x, t)) • u.grad (x, t)) ∧
      ∀ᵐ x ∂(volume.restrict (euclideanBall (0 : Vec d) 1)), 0 ≤ u.toFun (x, t) := by
  have hgood := logSlice_ae hG hM0 hM u
  have hnn : ∀ᵐ t ∂(volume.restrict (Ioc (-1 : ℝ) 0)),
      ∀ᵐ x ∂(volume.restrict (euclideanBall (0 : Vec d) 1)), 0 ≤ u.toFun (x, t) := by
    rw [PDE.Parabolic.Energy.volume_restrict_prod] at hu0
    exact PDE.Parabolic.Energy.ae_ae_swap hu0
  have h := (ae_restrict_iff' measurableSet_Ioc).1 (hgood.and hnn)
  refine ⟨{t | ¬ (t ∈ Ioc (-1 : ℝ) 0 → _)}, ae_iff.1 h, fun t ht htN => ?_⟩
  simp only [mem_ofPred_eq, not_not] at htN
  exact htN ht

theorem log_ae_eq_G {G : ℝ → ℝ} {ε : ℝ}
    (hGlog : ∀ s, 0 ≤ s → G s = Real.log (s + ε))
    (u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)) {t : ℝ}
    (hnn : ∀ᵐ x ∂(volume.restrict (euclideanBall (0 : Vec d) 1)), 0 ≤ u.toFun (x, t)) :
    (fun x => Real.log (u.toFun (x, t) + ε)) =ᵐ[cutoffMeasure d]
      fun x => G (u.toFun (x, t)) := by
  filter_upwards [(cutoffMeasure_ac d).ae_le hnn] with x hx
  exact (hGlog _ hx).symm

theorem mean_log_eq {G : ℝ → ℝ} {ε : ℝ}
    (hGlog : ∀ s, 0 ≤ s → G s = Real.log (s + ε))
    (u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)) {t : ℝ}
    (hnn : ∀ᵐ x ∂(volume.restrict (euclideanBall (0 : Vec d) 1)), 0 ≤ u.toFun (x, t)) :
    ∫ y, Real.log (u.toFun (y, t) + ε) ∂(cutoffMeasure d) =
      ∫ y, G (u.toFun (y, t)) ∂(cutoffMeasure d) :=
  integral_congr_ae (log_ae_eq_G hGlog u hnn)

theorem var_log_eq {G : ℝ → ℝ} {ε : ℝ}
    (hGlog : ∀ s, 0 ≤ s → G s = Real.log (s + ε))
    (u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)) {t : ℝ}
    (hnn : ∀ᵐ x ∂(volume.restrict (euclideanBall (0 : Vec d) 1)), 0 ≤ u.toFun (x, t)) :
    ∫ x, (Real.log (u.toFun (x, t) + ε) -
        ∫ y, Real.log (u.toFun (y, t) + ε) ∂(cutoffMeasure d)) ^ 2 ∂(cutoffMeasure d) =
      ∫ x, (G (u.toFun (x, t)) - ∫ y, G (u.toFun (y, t)) ∂(cutoffMeasure d)) ^ 2
        ∂(cutoffMeasure d) := by
  rw [mean_log_eq hGlog u hnn]
  refine integral_congr_ae ?_
  filter_upwards [log_ae_eq_G hGlog u hnn] with x hx
  rw [hx]

end PDE.Parabolic.WeakHarnack
