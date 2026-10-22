module

public import PDEFoundation.PDE.ConstantForcing
public import PDEFoundation.Sobolev.H1.VectorMeanOscillation

/-!
# Zero-boundary gradient averages

Supported smooth approximation passes the vanishing integral of each test
function derivative to every native `H10Function` on a finite-volume domain.
This is the shared zero-trace convention used in `LeanIntoHomogenization`;
no second boundary predicate is introduced.
-/

@[expose] public section

namespace PDE

open MeasureTheory Filter
open scoped ENNReal Topology

namespace H10Function

/-- Each weak-gradient coordinate of a zero-boundary function has integral zero. -/
theorem setIntegral_grad_eq_zero
    {d : ℕ} {U : Set (Vec d)} (hUtop : volume U < ∞)
    (u : H10Function U) (i : Fin d) :
    ∫ x in U, u.toH1Function.grad x i = 0 := by
  let : IsFiniteMeasure (volumeOn U) :=
    isFiniteMeasure_restrict.mpr hUtop.ne
  have hconst : MemL2On U (fun _ => (1 : ℝ)) := memLp_const 1
  have hlim := tendsto_setIntegral_mul_of_tendsto_eLpNorm hconst
    (fun n => (u.toWeakTestFunction n).memLp_partialDeriv i 2)
    (u.toH1Function.gradMemL2 i) (u.tendsto_approx_grad i)
  have hzero : ∀ n : ℕ,
      (∫ x in U, (1 : ℝ) * (u.toWeakTestFunction n).partialDeriv i x) = 0 := by
    intro n
    simpa only [one_mul] using (u.toWeakTestFunction n).integral_partialDeriv_eq_zero i
  simp only [one_mul] at hzero hlim
  simp only [hzero] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- The literal coordinatewise mean gradient vanishes on finite-volume domains. -/
theorem vectorIntegralAverage_grad_eq_zero
    {d : ℕ} {U : Set (Vec d)} (hUtop : volume U < ∞)
    (u : H10Function U) :
    vectorIntegralAverage U u.toH1Function.grad = 0 := by
  funext i
  rw [vectorIntegralAverage_apply, integralAverage, u.setIntegral_grad_eq_zero hUtop i]
  exact mul_zero _

end H10Function
end PDE
