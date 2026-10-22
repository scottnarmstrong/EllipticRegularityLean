module

public import PDEFoundation.Sobolev.ClassicalLaplacian
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# One-variable tests for the parabolic weak maximum principle

* a local maximum of a `C²` function has nonpositive diagonal second coordinate derivatives;
* a one-sided maximum at a point `t ∈ (t₀, t₁]` of `[t₀, t₁]` forces a nonnegative derivative.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace PDE

noncomputable section

variable {d : ℕ}

/-- Second derivative test along a coordinate line: a local maximum of a `C²` function has
`∂_i ∂_i f ≤ 0`. -/
theorem euclideanCoordSecondDeriv_diag_nonpos_of_isLocalMax {f : Vec d → ℝ} {x : Vec d}
    (hf : ContDiffAt ℝ 2 f x) (hmax : IsLocalMax f x) (i : Fin d) :
    euclideanCoordSecondDeriv i i f x ≤ 0 := by
  classical
  set e : Vec d := basisVec i with he
  set a : ℝ → Vec d := fun s => x + s • e with ha
  have ha0 : a 0 = x := by simp [ha]
  have hacont : Continuous a := by fun_prop
  have hahas : ∀ s, HasDerivAt a e s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => s • e) ((1 : ℝ) • e) s := (hasDerivAt_id s).smul_const e
    simpa [ha] using h1.const_add x
  have htend : Tendsto a (𝓝 0) (𝓝 x) := by
    have h := hacont.continuousAt (x := 0)
    rw [ContinuousAt, ha0] at h
    exact h
  have hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    (hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
    hf.fderiv_right (m := 1) (by norm_num)
  have hh : DifferentiableAt ℝ (euclideanCoordDeriv i f) x := by
    unfold euclideanCoordDeriv
    exact (hfd.differentiableAt (by norm_num)).clm_apply (differentiableAt_const _)
  set g : ℝ → ℝ := fun s => f (a s) with hg
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ f (a s) := by
    exact htend.eventually hdiff
  have hgd : deriv g =ᶠ[𝓝 0] fun s => euclideanCoordDeriv i f (a s) := by
    filter_upwards [hnear] with s hs
    have := hs.hasFDerivAt.comp_hasDerivAt s (hahas s)
    exact this.deriv
  have hdd : deriv (deriv g) 0 = euclideanCoordSecondDeriv i i f x := by
    rw [hgd.deriv_eq]
    have h1 : HasDerivAt (fun s => euclideanCoordDeriv i f (a s))
        (fderiv ℝ (euclideanCoordDeriv i f) x e) 0 := by
      have hh' : HasFDerivAt (euclideanCoordDeriv i f) (fderiv ℝ (euclideanCoordDeriv i f) x)
          (a 0) := by
        rw [ha0]; exact hh.hasFDerivAt
      exact hh'.comp_hasDerivAt 0 (hahas 0)
    rw [h1.deriv]
    rfl
  have hgmax : IsLocalMax g 0 := by
    unfold IsLocalMax IsMaxFilter
    filter_upwards [htend.eventually hmax] with s hs
    simpa [hg, ha0] using hs
  have hg0 : deriv g 0 = 0 := hgmax.deriv_eq_zero
  have hgcont : ContinuousAt g 0 :=
    ContinuousAt.comp_of_eq hf.continuousAt hacont.continuousAt ha0
  by_contra hpos
  have hc : deriv (deriv g) 0 > 0 := by
    rw [hdd]; exact lt_of_not_ge hpos
  have hmin : IsLocalMin g 0 := isLocalMin_of_deriv_deriv_pos hc hg0 hgcont
  have hconst : g =ᶠ[𝓝 0] fun _ => g 0 := by
    filter_upwards [hmin, hgmax] with s h1 h2
    exact le_antisymm h2 h1
  have hdz : deriv g =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
    have := hconst.deriv
    simpa using this
  have : deriv (deriv g) 0 = 0 := by
    rw [hdz.deriv_eq]; simp
  linarith

/-- If `g` is maximal on `[t₀, t₁]` at `t ∈ (t₀, t₁]` and differentiable at `t`, then
`g' ≥ 0`. -/
theorem deriv_nonneg_of_isMaxOn_Icc {g : ℝ → ℝ} {g' t₀ t₁ t : ℝ}
    (hg : HasDerivAt g g' t) (ht₀ : t₀ < t) (ht₁ : t ≤ t₁)
    (hmax : ∀ τ ∈ Icc t₀ t₁, g τ ≤ g t) : 0 ≤ g' := by
  have hloc : IsLocalMaxOn g (Icc t₀ t₁) t :=
    IsMaxOn.isLocalMaxOn (fun τ hτ => hmax τ hτ) 
  have hy : -(t - t₀) ∈ posTangentConeAt (Icc t₀ t₁) t := by
    apply mem_posTangentConeAt_of_segment_subset
    intro z hz
    have h0 : t + -(t - t₀) = t₀ := by ring
    rw [h0, segment_symm, segment_eq_Icc ht₀.le] at hz
    exact ⟨hz.1, hz.2.trans ht₁⟩
  have := hloc.hasFDerivWithinAt_nonpos hg.hasDerivWithinAt.hasFDerivWithinAt hy
  simp at this
  nlinarith

end

end PDE
