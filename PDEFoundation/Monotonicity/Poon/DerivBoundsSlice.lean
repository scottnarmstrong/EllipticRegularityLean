module

public import PDEFoundation.Monotonicity.Poon.DerivBoundsStep

/-!
# Slice derivatives of a caloric function

For `g` smooth on the slab `(a, b) × ℝᵈ` and `t ∈ (a, b)`, the iterated coordinate derivatives of the
time slice `g (t, ·)` are the slices of the joint derivatives `jEx`, and the time derivative is the
slice of `jEt`.  Also: one component of a gradient is bounded by its Euclidean norm.
-/

@[expose] public section

open Set Filter

namespace PDE

noncomputable section

variable {d : ℕ} {a b : ℝ} {g : ℝ × Vec d → ℝ}

theorem coordDeriv_slice_eq {h : ℝ × Vec d → ℝ} (hh : JSm (slab d a b) h) {t : ℝ}
    (ht : t ∈ Ioo a b) (j : Fin d) :
    euclideanCoordDeriv j (fun y : Vec d => h (t, y)) = fun y => jEx j h (t, y) :=
  funext fun y => euclideanCoordDeriv_slice (isOpen_slab a b) hh j ⟨ht, mem_univ y⟩

theorem deriv_slice_eq {h : ℝ × Vec d → ℝ} (hh : JSm (slab d a b) h) {t : ℝ}
    (ht : t ∈ Ioo a b) :
    (fun y : Vec d => deriv (fun τ : ℝ => h (τ, y)) t) = fun y => jEt h (t, y) :=
  funext fun y => deriv_slice_time (hh.differentiableAt (isOpen_slab a b) ⟨ht, mem_univ y⟩)

theorem abs_jEx_le_norm_gradient (hg : JSm (slab d a b) g) {t : ℝ} (ht : t ∈ Ioo a b) (x : Vec d)
    (i : Fin d) :
    |jEx i g (t, x)| ≤ vecEuclideanNorm (classicalGradient (fun y => g (t, y)) x) := by
  have h1 : jEx i g (t, x) = classicalGradient (fun y => g (t, y)) x i := by
    rw [← euclideanCoordDeriv_eq_classicalGradient_apply, coordDeriv_slice_eq hg ht]
  rw [h1]
  exact Real.abs_le_sqrt (sq_apply_le_vecNormSq _ i)

end

end PDE
