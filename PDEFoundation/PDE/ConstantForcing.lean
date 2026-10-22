module

public import PDEFoundation.PDE.WeakDivergenceForm

/-!
# Constant shifts of divergence forcing

A constant vector has zero distributional divergence. Subtracting its value
at the center therefore preserves the weak equation, including testability.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

theorem WeakTestFunction.integral_partialDeriv_eq_zero
    {U : Set (Vec d)} (φ : WeakTestFunction U) (i : Fin d) :
    ∫ x in U, φ.partialDeriv i x = 0 := by
  have h := HasWeakPartialDerivOn.of_contDiff (U := U) (i := i)
    (f := fun _ : Vec d => (1 : ℝ)) contDiff_const
  have htest := h φ.toFun φ.contDiff φ.hasCompactSupport φ.tsupport_subset
  simpa [WeakTestFunction.partialDeriv] using htest

/-- Pairing a constant vector with a compact smooth gradient integrates to
zero on the exact test domain. -/
theorem integral_vecDot_const_weakTestFunction_grad_eq_zero
    {U : Set (Vec d)} (c : Vec d) (φ : WeakTestFunction U) :
    ∫ x in U, vecDot c (φ.grad x) = 0 := by
  have hint : ∀ i : Fin d, Integrable (fun x => c i * φ.grad x i) (volumeOn U) := by
    intro i
    exact ((memLp_one_iff_integrable).mp (φ.memLp_partialDeriv i 1)).const_mul (c i)
  change (∫ x, ∑ i : Fin d, c i * φ.grad x i ∂volumeOn U) = 0
  rw [integral_finsetSum Finset.univ (fun i _ => hint i)]
  simp only [WeakTestFunction.grad_apply]
  simp_rw [integral_const_mul, φ.integral_partialDeriv_eq_zero]
  simp only [mul_zero, Finset.sum_const_zero]

theorem IsWeakDivergenceFormSolutionOn.sub_const_forcing
    {U : Set (Vec d)} {a : CoeffField d}
    {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hu : IsWeakDivergenceFormSolutionOn a U u f F) (c : Vec d) :
    IsWeakDivergenceFormSolutionOn a U u f (fun x => F x - c) := by
  intro φ
  have htest := hu φ
  have hcint : IntegrableOn (fun x => vecDot c (φ.grad x)) U := by
    change Integrable (fun x => ∑ i : Fin d, c i * φ.partialDeriv i x) (volumeOn U)
    exact integrable_finsetSum Finset.univ (fun i _ =>
      ((memLp_one_iff_integrable).mp (φ.memLp_partialDeriv i 1)).const_mul (c i))
  have hpoint : (fun x => vecDot (F x - c) (φ.grad x)) =
      fun x => vecDot (F x) (φ.grad x) - vecDot c (φ.grad x) := by
    funext x
    simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  refine ⟨⟨htest.1.flux_integrable, htest.1.source_integrable, ?_⟩, ?_⟩
  · rw [hpoint]
    exact htest.1.forcing_integrable.sub hcint
  · rw [hpoint, integral_sub htest.1.forcing_integrable hcint,
      integral_vecDot_const_weakTestFunction_grad_eq_zero, sub_zero]
    exact htest.2

end PDE
