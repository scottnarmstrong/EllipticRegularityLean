module

public import EllipticRegularity.Parabolic.Cauchy.Duality.PairDataLinear

@[expose] public section

namespace PDE.Parabolic.Duality

open MeasureTheory Set
open PDE.Parabolic.Energy

/-- Negate all solution and flux fields of an abstract energy datum. -/
noncomputable def energyDataNeg {d : ℕ} (D : Energy.Data d) : Energy.Data d := by
  refine {
    K := D.K
    hK := D.hK
    δ0 := D.δ0
    hδ0 := D.hδ0
    hδ1 := D.hδ1
    s := D.s
    t := D.t
    hst := D.hst
    u := fun z => -D.u z
    Du := fun z => -D.Du z
    G := fun z => -D.G z
    φ := D.φ
    hφ := D.hφ
    hφK := D.hφK
    hDum := fun i => (D.hDum i).neg
    hGm := fun i => (D.hGm i).neg
    hu2 := D.hu2.neg
    hDu2 := fun i => (D.hDu2 i).neg
    hG2 := fun i => (D.hG2 i).neg
    hus := by
      intro τ hτ
      exact (D.hus τ hτ).neg
    hwg := by
      filter_upwards [D.hwg] with τ hτ a ha haδ x hx i
      have h := hτ a ha haδ x hx i
      calc
        ∫ y in D.K1, fderiv ℝ (kern a) (x - y) (basisVec i) * (-D.u (y, τ)) =
            -(∫ y in D.K1, fderiv ℝ (kern a) (x - y) (basisVec i) * D.u (y, τ)) := by
          rw [show (fun y => fderiv ℝ (kern a) (x - y) (basisVec i) * (-D.u (y, τ))) =
              fun y => -(fderiv ℝ (kern a) (x - y) (basisVec i) * D.u (y, τ)) by
            funext y
            ring, integral_neg]
        _ = -(∫ y in D.K1, kern a (x - y) * D.Du (y, τ) i) := congrArg Neg.neg h
        _ = ∫ y in D.K1, kern a (x - y) * (-D.Du (y, τ)) i := by
          rw [show (fun y => kern a (x - y) * (-D.Du (y, τ)) i) =
              fun y => -(kern a (x - y) * D.Du (y, τ) i) by
            funext y
            simp only [Pi.neg_apply]
            ring, integral_neg]
    hslice := by
      intro a ha haδ x hx τ1 τ2 h1 h12 h2
      have h := D.hslice a ha haδ x hx τ1 τ2 h1 h12 h2
      have hval2 : ∫ y in D.K1, kern a (x - y) * (-D.u (y, τ2)) =
          -(∫ y in D.K1, kern a (x - y) * D.u (y, τ2)) := by
        rw [show (fun y => kern a (x - y) * (-D.u (y, τ2))) =
            fun y => -(kern a (x - y) * D.u (y, τ2)) by funext y; ring, integral_neg]
      have hval1 : ∫ y in D.K1, kern a (x - y) * (-D.u (y, τ1)) =
          -(∫ y in D.K1, kern a (x - y) * D.u (y, τ1)) := by
        rw [show (fun y => kern a (x - y) * (-D.u (y, τ1))) =
            fun y => -(kern a (x - y) * D.u (y, τ1)) by funext y; ring, integral_neg]
      calc
        (∫ y in D.K1, kern a (x - y) * (-D.u (y, τ2))) -
            ∫ y in D.K1, kern a (x - y) * (-D.u (y, τ1)) =
          -((∫ y in D.K1, kern a (x - y) * D.u (y, τ2)) -
            ∫ y in D.K1, kern a (x - y) * D.u (y, τ1)) := by rw [hval2, hval1]; ring
        _ = -(∫ z in D.K1 ×ˢ Ioc τ1 τ2,
            ∑ i, D.G z i * fderiv ℝ (kern a) (x - z.1) (basisVec i)) := congrArg Neg.neg h
        _ = ∫ z in D.K1 ×ˢ Ioc τ1 τ2,
            ∑ i, (-D.G z i) * fderiv ℝ (kern a) (x - z.1) (basisVec i) := by
          rw [← integral_neg]
          congr 1
          funext z
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
  }

theorem energyDataNeg_fields {d : ℕ} (D : Energy.Data d) (z : Vec d × ℝ) :
    (energyDataNeg D).u z = -D.u z ∧
      (energyDataNeg D).Du z = -D.Du z ∧
      (energyDataNeg D).G z = -D.G z := by
  simp [energyDataNeg]

end PDE.Parabolic.Duality
