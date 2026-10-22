module

public import EllipticRegularity.Ch4.GreenFunction.Exists
public import EllipticRegularity.Ch4.GreenHarnack.Pointwise

/-!
# Harnack inequality for the Green function on `D_r = B_{3r/2} \ B_{r/4}` (4.161)

For `r ≤ R/2`, `G` is `H¹`, nonnegative and `a`-harmonic in `V = B_{2r} \ B̄_{r/8}`; the Harnack
inequality in annuli (`PDE.Ch4GreenHarnack.harnack_annulus`) gives a constant `m ≥ 0`
with `m ≤ G ≤ exp(C_H √Λ) m` a.e. in `D_r`.
-/

@[expose] public section

open scoped Topology ENNReal

namespace PDE.Ch4Green

open MeasureTheory PDE Filter

variable {d : ℕ}

namespace ApproxSetting

variable {Λ R : ℝ} {a : CoeffField d}

/-- **Harnack bounds for `G` on `D_r`.** -/
theorem isGreen_harnack (hd : 3 ≤ d) :
    ∃ CH : ℝ, 0 < CH ∧ ∀ {Λ R : ℝ} {a : CoeffField d} (S : ApproxSetting d Λ R a),
      (∀ n, ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), 0 ≤ (S.G n).toH1Function.toFun x) →
      ∀ {G : Vec d → ℝ}, IsGreenFunction a R G → ∀ {r : ℝ}, 0 < r → r ≤ R / 2 →
      ∃ m : ℝ, 0 ≤ m ∧
        ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) (3 * r / 2) \ euclideanBall (0 : Vec d) (r / 4)),
          m ≤ G x ∧ G x ≤ Real.exp (CH * Real.sqrt Λ) * m := by
  obtain ⟨CH, hCH, hHarn⟩ := Ch4GreenHarnack.harnack_annulus d hd
  refine ⟨CH, hCH, ?_⟩
  intro Λ R a S hGnn G hG r hr hrR
  have hR := S.hR
  have hε : 0 < r / 8 := by positivity
  have hεR : r / 8 < R := by linarith
  obtain ⟨H, hHG, hHsol, -⟩ := S.exists_harmonic hd hG hε hεR
  have hUo : IsOpen (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 8)) :=
    (isOpen_euclideanBall _ _).sdiff (isClosed_euclideanClosedBall _ _)
  have hVo : IsOpen (euclideanBall (0 : Vec d) (2 * r) \ euclideanClosedBall (0 : Vec d) (r / 8)) :=
    (isOpen_euclideanBall _ _).sdiff (isClosed_euclideanClosedBall _ _)
  have hVU : euclideanBall (0 : Vec d) (2 * r) \ euclideanClosedBall (0 : Vec d) (r / 8) ⊆
      euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 8) := fun x hx =>
    ⟨euclideanBall_mono (by positivity) (by linarith) hx.1, hx.2⟩
  have hVB : euclideanBall (0 : Vec d) (2 * r) \ euclideanClosedBall (0 : Vec d) (r / 8) ⊆
      euclideanBall (0 : Vec d) R := fun x hx => (hVU hx).1
  have hsol := DGNM.solutionOn_restrict hHsol hUo hVo hVU
  have hnn : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) (2 * r) \
      euclideanClosedBall (0 : Vec d) (r / 8)), 0 ≤ (H.restrict hVo hVU).toFun x := by
    have := ae_restrict_of_ae_restrict_of_subset hVB (S.isGreen_nonneg hd hGnn hG)
    simpa only [H1Function.restrict_toFun, hHG] using this
  obtain ⟨m, hm0, hm⟩ := hHarn Λ a r hr
    (fun i j => (S.hmeas i j).mono_measure (Measure.restrict_mono hVB le_rfl))
    (fun x hx => S.hell x (hVB hx)) (H.restrict hVo hVU) hnn hsol
  refine ⟨m, hm0, ?_⟩
  simpa only [H1Function.restrict_toFun, hHG] using hm

end ApproxSetting

end PDE.Ch4Green
