module

public import PDEFoundation.Sobolev.W1p.Graph
public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.ClassicalGradient
public import PDEFoundation.Measure.VecAppendLp
public import PDEFoundation.Sobolev.WeakDerivative.ProductSlice
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Product lifting of weakly divergence-free fields -/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

/-- A weakly divergence-free field remains divergence-free after adjoining
unused finite-volume coordinates. -/
theorem integral_vecDot_classicalGradient_eq_zero_productLift
    {m n : ℕ} {U : Set (Vec m)} {V : Set (Vec n)}
    (hU : IsOpen U) (hV : IsOpen V) (hVfinite : volume V < ⊤)
    {J : Vec m → Vec m}
    (hJ : ∀ i, MemLp (fun x => J x i) 2 (volume.restrict U))
    (hdiv : ∀ ψ : WeakTestFunction U,
      ∫ x in U, vecDot (J x) (classicalGradient ψ x) = 0) :
    ∀ φ : WeakTestFunction (vecAppendEquiv m n ⁻¹' (U ×ˢ V)),
      ∫ z in vecAppendEquiv m n ⁻¹' (U ×ˢ V),
        vecDot ((vecAppendEquiv m n).symm
          (J (vecAppendEquiv m n z).1, 0)) (classicalGradient φ z) = 0 := by
  let E := vecAppendEquiv m n ⁻¹' (U ×ˢ V)
  let μE := volume.restrict E
  let μU := volume.restrict U
  let μV := volume.restrict V
  let liftJ : Vec (m + n) → Vec (m + n) := fun z =>
    (vecAppendEquiv m n).symm (J (vecAppendEquiv m n z).1, 0)
  let e : Vec (m + n) ≃ᵐ (Vec m × Vec n) :=
    (vecAppendEquiv m n).toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e μE (μU.prod μV) := by
    simpa only [E, μE, μU, μV, e] using!
      measurePreserving_vecAppendEquiv_restrict m n hU.measurableSet hV.measurableSet
  have hLiftCoord (k : Fin (m + n)) :
      MemLp (fun z => liftJ z k) 2 μE := by
    refine Fin.addCases (motive := fun k : Fin (m + n) =>
      MemLp (fun z => liftJ z k) 2 μE) ?_ ?_ k
    · intro i
      simpa only [liftJ, vecAppendEquiv_symm_apply_castAdd, μE, E] using
        memLp_comp_fst_vecAppendEquiv m n hU.measurableSet hV.measurableSet
          hVfinite (hJ i)
    · intro j
      simpa only [liftJ, vecAppendEquiv_symm_apply_natAdd] using!
        (MemLp.zero : MemLp (0 : Vec (m + n) → ℝ) 2 μE)
  intro φ
  let A : Vec m × Vec n → ℝ := fun p =>
    vecDot (J p.1) (fun i => (φ.sliceRight p.2).partialDeriv i p.1)
  have hOrig : Integrable
      (fun z => vecDot (liftJ z) (classicalGradient φ z)) μE := by
    simp only [vecDot, classicalGradient_apply]
    apply integrable_finsetSum
    intro k hk
    exact (hLiftCoord k).integrable_mul (φ.memLp_partialDeriv k 2)
  have hEq (p : Vec m × Vec n) :
      vecDot (liftJ (e.symm p)) (classicalGradient φ (e.symm p)) = A p := by
    have hep : vecAppendEquiv m n (e.symm p) = p := e.apply_symm_apply p
    rw [show liftJ (e.symm p) = (vecAppendEquiv m n).symm (J p.1, 0) by
      simp only [liftJ, hep]]
    simp only [vecDot, Fin.sum_univ_add,
      vecAppendEquiv_symm_apply_castAdd, vecAppendEquiv_symm_apply_natAdd,
      Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, A]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    exact (φ.sliceRight_partialDeriv p.2 i p.1).symm
  have hA : Integrable A (μU.prod μV) := by
    have h := (MeasurePreserving.symm e he).integrable_comp_of_integrable hOrig
    exact h.congr (ae_of_all _ hEq)
  have hFiber (y : Vec n) : ∫ x, A (x, y) ∂μU = 0 := by
    simpa only [A, μU, vecDot, WeakTestFunction.partialDeriv, classicalGradient_apply] using
      hdiv (φ.sliceRight y)
  calc
    (∫ z in E, vecDot (liftJ z) (classicalGradient φ z) ∂volume) =
        ∫ p, A p ∂(μU.prod μV) := by
      have hChange := he.integral_comp' A
      calc
        _ = ∫ z, A (e z) ∂μE := by
          apply integral_congr_ae
          filter_upwards with z
          have hz := hEq (e z)
          simpa only [MeasurableEquiv.symm_apply_apply] using hz
        _ = _ := hChange
    _ = ∫ y, ∫ x, A (x, y) ∂μU ∂μV := integral_prod_symm A hA
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards with y
      exact hFiber y

end
end PDE
