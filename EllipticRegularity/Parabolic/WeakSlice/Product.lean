module

public import EllipticRegularity.Parabolic.ParabolicDef

/-!
# Product test functions `θ(t) ζ(x)` and Fubini bookkeeping on `U ×ˢ J`
-/

@[expose] public section

namespace PDE.Parabolic.WeakSlice

open MeasureTheory Set Filter Topology PDE

theorem vecDot_smul_right' {d : ℕ} (x y : Vec d) (c : ℝ) :
    vecDot x (c • y) = c * vecDot x y := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

section product
variable {d : ℕ} {θ : ℝ → ℝ} {ζ : Vec d → ℝ}

theorem prod_hasFDerivAt (hθ : ContDiff ℝ 1 θ) (hζ : ContDiff ℝ 1 ζ) (z : Vec d × ℝ) :
    HasFDerivAt (fun w : Vec d × ℝ => θ w.2 * ζ w.1)
      (θ z.2 • (fderiv ℝ ζ z.1).comp (ContinuousLinearMap.fst ℝ (Vec d) ℝ) +
        ζ z.1 • (deriv θ z.2 • ContinuousLinearMap.snd ℝ (Vec d) ℝ)) z := by
  have h1 : HasFDerivAt (fun w : Vec d × ℝ => θ w.2)
      (deriv θ z.2 • ContinuousLinearMap.snd ℝ (Vec d) ℝ) z := by
    have := ((hθ.differentiable one_ne_zero z.2).hasDerivAt).hasFDerivAt.comp z
      (hasFDerivAt_snd (𝕜 := ℝ) (E := Vec d) (F := ℝ) (p := z))
    refine this.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    simp [mul_comm]
  have h2 : HasFDerivAt (fun w : Vec d × ℝ => ζ w.1)
      ((fderiv ℝ ζ z.1).comp (ContinuousLinearMap.fst ℝ (Vec d) ℝ)) z :=
    ((hζ.differentiable one_ne_zero z.1).hasFDerivAt).comp z
      (hasFDerivAt_fst (𝕜 := ℝ) (E := Vec d) (F := ℝ) (p := z))
  exact h1.mul h2 |>.congr_fderiv (ContinuousLinearMap.ext fun v => by simp [mul_comm])

theorem parTimeDeriv_prod (hθ : ContDiff ℝ 1 θ) (hζ : ContDiff ℝ 1 ζ) (z : Vec d × ℝ) :
    parTimeDeriv (fun w : Vec d × ℝ => θ w.2 * ζ w.1) z = deriv θ z.2 * ζ z.1 := by
  unfold parTimeDeriv
  rw [(prod_hasFDerivAt hθ hζ z).fderiv]
  simp [mul_comm]

theorem parSpaceGrad_prod (hθ : ContDiff ℝ 1 θ) (hζ : ContDiff ℝ 1 ζ) (z : Vec d × ℝ) :
    parSpaceGrad (fun w : Vec d × ℝ => θ w.2 * ζ w.1) z = θ z.2 • spaceGradC1 ζ z.1 := by
  ext i
  unfold parSpaceGrad spaceGradC1
  rw [(prod_hasFDerivAt hθ hζ z).fderiv]
  simp

theorem contDiff_prod (hθ : ContDiff ℝ 1 θ) (hζ : ContDiff ℝ 1 ζ) :
    ContDiff ℝ 1 (fun w : Vec d × ℝ => θ w.2 * ζ w.1) :=
  (hθ.comp contDiff_snd).mul (hζ.comp contDiff_fst)

theorem tsupport_prod_subset :
    tsupport (fun w : Vec d × ℝ => θ w.2 * ζ w.1) ⊆ tsupport ζ ×ˢ tsupport θ := by
  show closure _ ⊆ closure (Function.support ζ) ×ˢ closure (Function.support θ)
  rw [← closure_prod_eq]
  refine closure_mono ?_
  intro w hw
  simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hw
  exact ⟨by simpa using hw.2, by simpa using hw.1⟩

theorem hasCompactSupport_prod (hθ : HasCompactSupport θ) (hζ : HasCompactSupport ζ) :
    HasCompactSupport (fun w : Vec d × ℝ => θ w.2 * ζ w.1) := by
  refine IsCompact.of_isClosed_subset (hζ.prod hθ) (isClosed_tsupport _) tsupport_prod_subset

end product

/-- Fubini on `U ×ˢ J` with the time integral outside. -/
theorem integral_prod_slices {d : ℕ} {U : Set (Vec d)} {J : Set ℝ} {f : Vec d × ℝ → ℝ}
    (hf : IntegrableOn f (U ×ˢ J)) :
    IntegrableOn (fun τ => ∫ x in U, f (x, τ)) J ∧
      ∫ z in U ×ˢ J, f z = ∫ τ in J, ∫ x in U, f (x, τ) := by
  have h : Integrable f ((volume.restrict U).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; exact hf
  refine ⟨h.integral_prod_right, ?_⟩
  have := integral_prod_symm f h
  rwa [Measure.prod_restrict, ← Measure.volume_eq_prod] at this

end PDE.Parabolic.WeakSlice
