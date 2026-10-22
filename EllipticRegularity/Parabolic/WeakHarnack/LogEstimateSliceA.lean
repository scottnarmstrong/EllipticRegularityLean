module

public import EllipticRegularity.Parabolic.WeakHarnack.LogEstimateIntegrable
public import EllipticRegularity.Parabolic.Chain.Super.SliceForm

/-!
# The integrated lower bound for the logarithmic test

Consuming `weak_supersolution_renormalization_slice` with `F = G` (a `C²` profile equal to
`log (· + ε)` on `[0,∞)`) and the time-independent weight `φ = ζ²`:
for a.e. `s < t`,
`∫∫_{B₁ × (s,t]} (½ ζ² |G'(u) ∇u|² - 2Λ |∇ζ|²) ≤ ∫ G(u(t)) ζ² - ∫ G(u(s)) ζ²`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PDE.Parabolic.WeakHarnack

variable {d : ℕ}

theorem logQ_integral_le {Λ : ℝ} {a : ParCoeffField d}
    (ha : IsParabolicCoeff 1 Λ a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hu : IsParabolicWeakSupersolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u)
    (hu0 : ∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
      0 ≤ u.toFun z)
    {ε : ℝ} {G : ℝ → ℝ} (hG2 : ContDiff ℝ 2 G) (hLip : ∃ C : NNReal, LipschitzWith C G)
    (hG1b : ∃ C : NNReal, ∀ s, |deriv G s| ≤ C)
    (hG2b : ∃ C : NNReal, ∀ s, |deriv (deriv G) s| ≤ C) (hGmono : ∀ s, 0 ≤ deriv G s)
    (hGlog : ∀ s, 0 ≤ s → deriv G s = (s + ε)⁻¹ ∧
      deriv (deriv G) s = -((s + ε)⁻¹) ^ 2) (hε : 0 < ε) :
    ∃ N : Set ℝ, volume N = 0 ∧ ∀ s t : ℝ, s ∈ Ioc (-1 : ℝ) 0 → t ∈ Ioc (-1 : ℝ) 0 →
      s ∉ N → t ∉ N → s < t →
      ∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc s t, logQ Λ G u z ≤
        (∫ x in euclideanBall (0 : Vec d) 1, G (u.toFun (x, t)) * radialCutoff d x ^ 2) -
          ∫ x in euclideanBall (0 : Vec d) 1, G (u.toFun (x, s)) * radialCutoff d x ^ 2 := by
  have hKc : IsCompact (euclideanClosedBall (0 : Vec d) (7 / 8)) :=
    isCompact_euclideanClosedBall 0 (by norm_num)
  have hKU : euclideanClosedBall (0 : Vec d) (7 / 8) ⊆ euclideanBall (0 : Vec d) 1 :=
    euclideanClosedBall_subset_euclideanBall (by norm_num) (by norm_num)
  have hφK : ∀ x ∉ euclideanClosedBall (0 : Vec d) (7 / 8), ∀ τ : ℝ, phiZ d (x, τ) = 0 := by
    intro x hx τ
    rw [phiZ_apply]
    have : radialCutoff d x = 0 := radialCutoff_eq_zero fun h =>
      hx (euclideanBall_subset_euclideanClosedBall _ _ h)
    simp [this]
  obtain ⟨N, hN, hmain⟩ := PDE.Parabolic.Chain.weak_supersolution_renormalization_slice
    (isOpen_euclideanBall 0 1) Set.ordConnected_Ioc ha u hu G hG2 hLip hG1b hG2b hGmono (phiZ d)
    (contDiff_phiZ d) phiZ_nonneg hKc hKU hφK
  refine ⟨N, hN, fun s t hs ht hsN htN hst => ?_⟩
  obtain ⟨-, -, -, hineq⟩ := hmain s t hs ht hsN htN hst
  obtain ⟨M, hM⟩ := hG1b
  have hsub : euclideanBall (0 : Vec d) 1 ×ˢ Ioc s t ⊆
      euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 :=
    prod_mono subset_rfl (Ioc_subset_Ioc hs.1.le ht.2)
  have hQint : IntegrableOn (logQ Λ G u) (euclideanBall (0 : Vec d) 1 ×ˢ Ioc s t) :=
    (integrable_logQ (hG2.of_le (by norm_num)) (M := (M : ℝ)) hM u).mono_measure
      (Measure.restrict_mono hsub le_rfl)
  have hae : ∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
      logQ Λ G u z ≤ G (u.toFun z) * parTimeDeriv (phiZ d) z -
        deriv (deriv G) (u.toFun z) * phiZ d z *
          vecDot (matVecMul (a z) (u.grad z)) (u.grad z) -
        deriv G (u.toFun z) * vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad (phiZ d) z) := by
    filter_upwards [hu0, ha.elliptic] with z hz0 hzA
    obtain ⟨e1, e2⟩ := hGlog _ hz0
    have hv : 0 < u.toFun z + ε := by linarith
    have h := logPoint hzA (u.grad z) (spaceGradC1 (radialCutoff d) z.1) (ζ := radialCutoff d z.1) hv
    rw [parTimeDeriv_phiZ, parSpaceGrad_phiZ, phiZ_apply, e1, e2]
    unfold logQ
    rw [e1]
    linarith
  have hae' := ae_restrict_of_ae_restrict_of_subset hsub hae
  have hR : IntegrableOn (fun z => G (u.toFun z) * parTimeDeriv (phiZ d) z -
        deriv (deriv G) (u.toFun z) * phiZ d z *
          vecDot (matVecMul (a z) (u.grad z)) (u.grad z) -
        deriv G (u.toFun z) * vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad (phiZ d) z))
      (euclideanBall (0 : Vec d) 1 ×ˢ Ioc s t) := by
    obtain ⟨hR, -⟩ := hmain s t hs ht hsN htN hst |>.imp_left id
    exact hR
  refine (integral_mono_ae hQint hR hae').trans ?_
  simpa only [phiZ_apply] using hineq

end PDE.Parabolic.WeakHarnack
