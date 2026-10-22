module

public import PDEFoundation.Euler.WeakProduct
public import PDEFoundation.Euler.MollifyL2ST

/-!
# Space-time integrals as time integrals of slice integrals

`∫₀ᵀ g(τ) ∑ₖ ∫_cube hₖ(x,τ) dx dτ = ∑ₖ ∫_{cube × [0,T]} g(t) hₖ`, for integrable `hₖ` and continuous `g`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE

theorem integral_spacetime_time_slice {T : ℝ} {h : Vec 2 × ℝ → ℝ} (hh : Integrable h (eulerMeasure T))
    {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ z, g z.2 * h z ∂(eulerMeasure T) =
      ∫ τ in Icc (0 : ℝ) T, g τ * ∫ x in torusCube, h (x, τ) := by
  have hi : Integrable (fun z : Vec 2 × ℝ => g z.2 * h z) (eulerMeasure T) :=
    integrable_cont_mul_coord hh (hg.comp continuous_snd)
  rw [eulerMeasure_eq_prod] at hi ⊢
  rw [integral_prod_symm _ hi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  simp only
  rw [integral_const_mul]

theorem integrable_time_slice {T : ℝ} {h : Vec 2 × ℝ → ℝ} (hh : Integrable h (eulerMeasure T))
    {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable (fun τ => g τ * ∫ x in torusCube, h (x, τ)) (volume.restrict (Icc (0 : ℝ) T)) := by
  have hi : Integrable (fun z : Vec 2 × ℝ => g z.2 * h z) (eulerMeasure T) :=
    integrable_cont_mul_coord hh (hg.comp continuous_snd)
  rw [eulerMeasure_eq_prod] at hi
  have := hi.integral_prod_right
  refine this.congr (Filter.Eventually.of_forall fun τ => ?_)
  simp only
  rw [integral_const_mul]

theorem time_slice_sum {T : ℝ} {ι : Type*} (s : Finset ι) {h : ι → Vec 2 × ℝ → ℝ}
    (hh : ∀ k ∈ s, Integrable (h k) (eulerMeasure T)) {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ τ in Icc (0 : ℝ) T, g τ * ∑ k ∈ s, ∫ x in torusCube, h k (x, τ) =
      ∑ k ∈ s, ∫ z, g z.2 * h k z ∂(eulerMeasure T) := by
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun k hk => integrable_time_slice (hh k hk) hg)]
  exact Finset.sum_congr rfl fun k hk => (integral_spacetime_time_slice (hh k hk) hg).symm

end PDE
