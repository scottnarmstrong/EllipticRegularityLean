/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.CauchyDef

/-! # Initial-slice consequences for Cauchy energy solutions -/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Energy

open MeasureTheory Set

/-- Two Cauchy energy solutions with the same datum have the same initial slice a.e. -/
theorem cauchy_initial_slice_eq {d : ℕ} (a : ParCoeffField d) (s T : ℝ)
    (f : Vec d → ℝ) (u v : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) (hv : IsCauchySolution a s T f v) :
    ∀ᵐ x : Vec d, u.toFun (x, s) = v.toFun (x, s) := by
  change IsParabolicWeakSolution a univ (Icc s T) u ∧
      (∀ᵐ x : Vec d, u.toFun (x, s) = f x) at hu
  change IsParabolicWeakSolution a univ (Icc s T) v ∧
      (∀ᵐ x : Vec d, v.toFun (x, s) = f x) at hv
  filter_upwards [hu.2, hv.2] with x hux hvx
  rw [hux, hvx]

/-- Nonnegative Cauchy data give a nonnegative initial slice. -/
theorem cauchy_initial_slice_nonneg {d : ℕ} (a : ParCoeffField d) (s T : ℝ)
    (f : Vec d → ℝ) (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) (hf : ∀ᵐ x : Vec d, 0 ≤ f x) :
    ∀ᵐ x : Vec d, 0 ≤ u.toFun (x, s) := by
  change IsParabolicWeakSolution a univ (Icc s T) u ∧
      (∀ᵐ x : Vec d, u.toFun (x, s) = f x) at hu
  filter_upwards [hu.2, hf] with x hux hfx
  rw [hux]
  exact hfx

end PDE.Parabolic.Cauchy.Energy
