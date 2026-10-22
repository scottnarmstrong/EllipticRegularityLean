module

public import PDEFoundation.Monotonicity.Poon.BernsteinCalculus
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Bridge between joint derivatives and slice derivatives

For `g : ℝ × Vec d → ℝ` smooth on an open `Ω`, the slice `w t = g (t, ·)` has coordinate derivatives
and Laplacian given by `jEx` and `jLap`, and the time derivative is `jEt`.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace PDE

noncomputable section

variable {d : ℕ} {Ω : Set (ℝ × Vec d)} {g : ℝ × Vec d → ℝ}

theorem fderiv_slice_apply {t : ℝ} {x : Vec d} (hg : DifferentiableAt ℝ g (t, x)) (v : Vec d) :
    fderiv ℝ (fun y : Vec d => g (t, y)) x v = fderiv ℝ g (t, x) (0, v) := by
  have h1 : HasFDerivAt (fun y : Vec d => (t, y)) (ContinuousLinearMap.inr ℝ ℝ (Vec d)) x :=
    hasFDerivAt_prodMk_right t x
  have h2 : HasFDerivAt (fun y : Vec d => g (t, y)) _ x := hg.hasFDerivAt.comp x h1
  rw [h2.fderiv]
  simp

theorem deriv_slice_time {t : ℝ} {x : Vec d} (hg : DifferentiableAt ℝ g (t, x)) :
    deriv (fun τ : ℝ => g (τ, x)) t = fderiv ℝ g (t, x) ((1 : ℝ), (0 : Vec d)) := by
  have h1 : HasFDerivAt (fun τ : ℝ => (τ, x)) (ContinuousLinearMap.inl ℝ ℝ (Vec d)) t :=
    hasFDerivAt_prodMk_left t x
  have h2 : HasFDerivAt (fun τ : ℝ => g (τ, x)) _ t := hg.hasFDerivAt.comp t h1
  have h3 := h2.hasDerivAt
  rw [h3.deriv]
  simp

theorem euclideanCoordDeriv_slice (hΩ : IsOpen Ω) (hg : JSm Ω g) (i : Fin d) {t : ℝ} {y : Vec d}
    (hy : (t, y) ∈ Ω) :
    euclideanCoordDeriv i (fun y : Vec d => g (t, y)) y = jEx i g (t, y) :=
  fderiv_slice_apply (hg.differentiableAt hΩ hy) _

theorem euclideanCoordSecondDeriv_slice (hΩ : IsOpen Ω) (hg : JSm Ω g) (i : Fin d) {t : ℝ}
    {x : Vec d} (hx : (t, x) ∈ Ω) :
    euclideanCoordSecondDeriv i i (fun y : Vec d => g (t, y)) x = jEx i (jEx i g) (t, x) := by
  have hopen : IsOpen {y : Vec d | (t, y) ∈ Ω} :=
    hΩ.preimage (Continuous.prodMk_right t)
  have hev : euclideanCoordDeriv i (fun y : Vec d => g (t, y)) =ᶠ[𝓝 x]
      fun y => jEx i g (t, y) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact euclideanCoordDeriv_slice hΩ hg i hy
  unfold euclideanCoordSecondDeriv
  rw [hev.fderiv_eq]
  exact fderiv_slice_apply ((hg.jEx hΩ i).differentiableAt hΩ hx) _

theorem euclideanCoordLaplacian_slice (hΩ : IsOpen Ω) (hg : JSm Ω g) {t : ℝ} {x : Vec d}
    (hx : (t, x) ∈ Ω) :
    euclideanCoordLaplacian (fun y : Vec d => g (t, y)) x = jLap g (t, x) := by
  unfold euclideanCoordLaplacian jLap
  exact Finset.sum_congr rfl fun i _ => euclideanCoordSecondDeriv_slice hΩ hg i hx

end

end PDE
