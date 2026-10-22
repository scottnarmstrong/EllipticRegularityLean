module

public import PDEFoundation.Sobolev.Inequalities.ConvexPoincareL2

/-!
# Vanishing weak gradient

This file records the representative-level consequence of the bounded-convex
Poincaré inequality: an `H¹` function whose selected weak gradient vanishes
identically agrees almost everywhere with its integral average.

Keeping this consequence at the common bounded-convex level lets interval,
ball, and cube arguments use the same theorem.
-/

@[expose] public section

namespace PDE

open MeasureTheory

namespace H1Function

/-- An `H¹` representative with identically zero selected weak gradient on a
nonempty bounded open convex domain equals its integral average almost
everywhere. -/
theorem ae_eq_integralAverage_of_grad_eq_zero
    {d : ℕ} {U : Set (Vec d)} {D : ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hUDiameter : HasEuclideanDiameterLE U D)
    (hD : 0 ≤ D) (hUNonempty : U.Nonempty)
    (u : H1Function U) (hgrad : u.grad = 0) :
    u.toFun =ᵐ[volumeOn U] fun _ => integralAverage U u := by
  let : IsFiniteMeasure (volumeOn U) :=
    hU.isFiniteMeasure_volumeOn
  have hPoincare :=
    centeredPoincare_sq_on_boundedConvexDomain
      hU hUDiameter hD hUNonempty u
  have hnonpos :
      ∫ x in U, (u x - integralAverage U u) ^ 2 ≤ 0 := by
    calc
      ∫ x in U, (u x - integralAverage U u) ^ 2 ≤
          ((2 : ℝ) ^ d * D) ^ 2 *
            ∫ x in U, vecNormSq (u.grad x) :=
        hPoincare
      _ = 0 := by simp [hgrad, vecNormSq, vecDot]
  have hzero :
      ∫ x in U, (u x - integralAverage U u) ^ 2 = 0 :=
    le_antisymm hnonpos (integral_nonneg fun _ => sq_nonneg _)
  have hvalueIntegrable :
      Integrable (fun x => (u x - integralAverage U u) ^ 2)
        (volumeOn U) := by
    simpa only [H1Function.subAverage_apply, pow_two] using!
      integrableOn_mul_of_memL2On
        u.subAverage.memL2 u.subAverage.memL2
  have hsqZero :
      ∀ᵐ x ∂volumeOn U, (u x - integralAverage U u) ^ 2 = 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun x => sq_nonneg (u x - integralAverage U u))
      hvalueIntegrable).mp hzero
  filter_upwards [hsqZero] with x hx
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)

/-- Two `H¹` representatives with the same selected weak gradient differ
almost everywhere by the integral average of their difference. -/
theorem ae_eq_add_integralAverage_sub_of_grad_eq
    {d : ℕ} {U : Set (Vec d)} {D : ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hUDiameter : HasEuclideanDiameterLE U D)
    (hD : 0 ≤ D) (hUNonempty : U.Nonempty)
    (u v : H1Function U) (hgrad : u.grad = v.grad) :
    u.toFun =ᵐ[volumeOn U]
      fun x => v x + integralAverage U (u - v).toFun := by
  let w : H1Function U := u - v
  have hwgrad : w.grad = 0 := by
    funext x
    simp only [w, H1Function.sub_grad, hgrad, sub_self, Pi.zero_apply]
  have hw :=
    w.ae_eq_integralAverage_of_grad_eq_zero
      hU hUDiameter hD hUNonempty hwgrad
  filter_upwards [hw] with x hx
  change u x - v x = integralAverage U w at hx
  change u x - v x = integralAverage U (u - v).toFun at hx
  linarith

end H1Function

end PDE
