module

public import PDEFoundation.Analysis.CompactSupportLocalIBP
public import PDEFoundation.Measure.VecAppendLp
public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.WeakDerivative.ProductSlice
public import PDEFoundation.Sobolev.W1p.Graph
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Lifting representative `H¹` functions across finite-volume products

A representative `H¹` function can be made independent of a finite-volume
unused coordinate factor.  Its lifted gradient is the original gradient in the
first coordinates and zero in the remaining coordinates.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE
namespace H1Function

def appendLiftValue {m n : ℕ} (u : Vec m → ℝ) : Vec (m + n) → ℝ :=
  fun z => u (vecAppendEquiv m n z).1

def appendLiftGradient {m n : ℕ} (Du : Vec m → Vec m) :
    Vec (m + n) → Vec (m + n) :=
  fun z => (vecAppendEquiv m n).symm (Du (vecAppendEquiv m n z).1, 0)

private theorem appendLiftGradient_apply_castAdd {m n : ℕ}
    (Du : Vec m → Vec m) (z : Vec (m + n)) (i : Fin m) :
    appendLiftGradient Du z (Fin.castAdd n i) = Du (vecAppendEquiv m n z).1 i := by
  simp [appendLiftGradient]

private theorem appendLiftGradient_apply_natAdd {m n : ℕ}
    (Du : Vec m → Vec m) (z : Vec (m + n)) (j : Fin n) :
    appendLiftGradient Du z (Fin.natAdd m j) = 0 := by
  simp [appendLiftGradient]

theorem appendLift_hasWeakGradient {m n : ℕ}
    {U : Set (Vec m)} {V : Set (Vec n)} (hU : IsOpen U) (hV : IsOpen V)
    (hVfinite : volume V < ⊤) (u : H1Function U) :
    HasWeakGradientOn (vecAppendEquiv m n ⁻¹' (U ×ˢ V))
      (appendLiftValue u.toFun) (appendLiftGradient u.grad) := by
  let E : Set (Vec (m + n)) := vecAppendEquiv m n ⁻¹' (U ×ˢ V)
  let μE := volume.restrict E
  let μU := volume.restrict U
  let μV := volume.restrict V
  let e : Vec (m + n) ≃ᵐ (Vec m × Vec n) :=
    (vecAppendEquiv m n).toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e μE (μU.prod μV) := by
    exact measurePreserving_vecAppendEquiv_restrict m n hU.measurableSet hV.measurableSet
  have he_apply (z : Vec (m + n)) : e z = vecAppendEquiv m n z := rfl
  have he_symm_apply (p : Vec m × Vec n) : e.symm p = (vecAppendEquiv m n).symm p := rfl
  have hfL2 : MemLp (appendLiftValue u.toFun) 2 μE := by
    exact memLp_comp_fst_vecAppendEquiv m n
      hU.measurableSet hV.measurableSet hVfinite u.memL2
  intro k
  rw [hasWeakPartialDerivOn_iff_forall_testFunction]
  intro φ
  refine Fin.addCases (motive := fun k : Fin (m + n) =>
    (∫ z in E, appendLiftValue u.toFun z * φ.partialDeriv k z ∂volume) =
      -∫ z in E, appendLiftGradient u.grad z k * φ z ∂volume) ?_ ?_ k
  · intro i
    let A : Vec m × Vec n → ℝ := fun p =>
      u p.1 * φ.partialDeriv (Fin.castAdd n i) ((vecAppendEquiv m n).symm p)
    let B : Vec m × Vec n → ℝ := fun p =>
      u.grad p.1 i * φ ((vecAppendEquiv m n).symm p)
    have hAorig : Integrable (fun z => appendLiftValue u.toFun z *
        φ.partialDeriv (Fin.castAdd n i) z) μE :=
      hfL2.integrable_mul (φ.memLp_partialDeriv (Fin.castAdd n i) 2)
    have hGradL2 : MemLp (fun z => appendLiftGradient u.grad z (Fin.castAdd n i))
        2 μE := by
      simpa only [E, μE, appendLiftGradient_apply_castAdd] using
        memLp_comp_fst_vecAppendEquiv m n hU.measurableSet hV.measurableSet
          hVfinite (u.grad_memL2 i)
    have hBorig : Integrable (fun z => appendLiftGradient u.grad z (Fin.castAdd n i) *
        φ z) μE := hGradL2.integrable_mul (φ.memLp_toFun 2)
    have hA : Integrable A (μU.prod μV) := by
      have h := (MeasurePreserving.symm e he).integrable_comp_of_integrable hAorig
      simpa [A, e, Function.comp_def, appendLiftValue] using h
    have hB : Integrable B (μU.prod μV) := by
      have h := (MeasurePreserving.symm e he).integrable_comp_of_integrable hBorig
      simpa [B, e, Function.comp_def, appendLiftGradient] using h
    have hFiber (y : Vec n) :
        (∫ x, A (x, y) ∂μU) = -∫ x, B (x, y) ∂μU := by
      simpa only [A, B, μU, WeakTestFunction.sliceRight_apply,
        WeakTestFunction.sliceRight_partialDeriv] using
        ((hasWeakPartialDerivOn_iff_forall_testFunction.mp
          (u.hasWeakPartialDerivOn i)) (φ.sliceRight y))
    calc
      (∫ z in E, appendLiftValue u.toFun z *
          φ.partialDeriv (Fin.castAdd n i) z ∂volume) = ∫ p, A p ∂(μU.prod μV) := by
            calc
              _ = ∫ z, A (e z) ∂μE := by
                apply integral_congr_ae
                filter_upwards with z
                simp [A, e, appendLiftValue]
              _ = _ := he.integral_comp' A
      _ = ∫ y, ∫ x, A (x, y) ∂μU ∂μV := integral_prod_symm A hA
      _ = ∫ y, -(∫ x, B (x, y) ∂μU) ∂μV := by
            apply integral_congr_ae
            filter_upwards with y
            exact hFiber y
      _ = -(∫ y, ∫ x, B (x, y) ∂μU ∂μV) := integral_neg _
      _ = -(∫ p, B p ∂(μU.prod μV)) := by rw [integral_prod_symm B hB]
      _ = -∫ z in E, appendLiftGradient u.grad z (Fin.castAdd n i) * φ z ∂volume := by
            have hChange := he.integral_comp' B
            have hChange' : (∫ z in E, appendLiftGradient u.grad z
                (Fin.castAdd n i) * φ z ∂volume) = ∫ p, B p ∂(μU.prod μV) := by
              simpa [μE, E, B, e, appendLiftGradient] using hChange
            exact congrArg Neg.neg hChange'.symm
  · intro j
    let A : Vec m × Vec n → ℝ := fun p =>
      u p.1 * φ.partialDeriv (Fin.natAdd m j) ((vecAppendEquiv m n).symm p)
    have hAorig : Integrable (fun z => appendLiftValue u.toFun z *
        φ.partialDeriv (Fin.natAdd m j) z) μE :=
      hfL2.integrable_mul (φ.memLp_partialDeriv (Fin.natAdd m j) 2)
    have hA : Integrable A (μU.prod μV) := by
      have h := (MeasurePreserving.symm e he).integrable_comp_of_integrable hAorig
      simpa [A, e, Function.comp_def, appendLiftValue] using h
    have hFiber (x : Vec m) : ∫ y, A (x, y) ∂μV = 0 := by
      have hIBP := integral_mul_weakTestFunction_partialDeriv_eq_neg_integral_fderiv_mul
        hV (f := fun _ : Vec n => (1 : ℝ)) contDiffOn_const (φ.sliceLeft x) j
      have hzero : (∫ y, φ.partialDeriv (Fin.natAdd m j)
          ((vecAppendEquiv m n).symm (x, y)) ∂μV) = 0 := by
        calc
          _ = ∫ y, (φ.sliceLeft x).partialDeriv j y ∂μV := by
            apply integral_congr_ae
            filter_upwards with y
            exact (φ.sliceLeft_partialDeriv x j y).symm
          _ = 0 := by simpa [μV] using hIBP
      simp only [A, integral_const_mul, hzero, mul_zero]
    calc
      (∫ z in E, appendLiftValue u.toFun z *
          φ.partialDeriv (Fin.natAdd m j) z ∂volume) = ∫ p, A p ∂(μU.prod μV) := by
            calc
              _ = ∫ z, A (e z) ∂μE := by
                apply integral_congr_ae
                filter_upwards with z
                simp [A, e, appendLiftValue]
              _ = _ := he.integral_comp' A
      _ = ∫ x, ∫ y, A (x, y) ∂μV ∂μU := integral_prod A hA
      _ = 0 := by
            apply integral_eq_zero_of_ae
            filter_upwards with x
            exact hFiber x
      _ = -∫ z in E, appendLiftGradient u.grad z (Fin.natAdd m j) * φ z ∂volume := by
            simp only [appendLiftGradient_apply_natAdd, zero_mul, integral_zero, neg_zero]

/-- Lift a representative `H¹` function across a finite-volume unused factor. -/
def liftAppend {m n : ℕ} {U : Set (Vec m)} {V : Set (Vec n)}
    (hU : IsOpen U) (hV : IsOpen V) (hVfinite : volume V < ⊤)
    (u : H1Function U) : H1Function (vecAppendEquiv m n ⁻¹' (U ×ˢ V)) where
  toFun := appendLiftValue u.toFun
  grad := appendLiftGradient u.grad
  memL2 := memLp_comp_fst_vecAppendEquiv m n hU.measurableSet hV.measurableSet
    hVfinite u.memL2
  gradMemL2 := by
    intro k
    refine Fin.addCases (motive := fun k : Fin (m + n) => MemLp
      (fun z => appendLiftGradient u.grad z k) 2
      (volume.restrict (vecAppendEquiv m n ⁻¹' (U ×ˢ V)))) ?_ ?_ k
    · intro i
      simpa only [appendLiftGradient_apply_castAdd] using
        memLp_comp_fst_vecAppendEquiv m n hU.measurableSet hV.measurableSet
          hVfinite (u.grad_memL2 i)
    · intro j
      simpa only [appendLiftGradient_apply_natAdd] using
        (MemLp.zero' : MemLp (fun _ : Vec (m + n) => (0 : ℝ)) 2
          (volume.restrict (vecAppendEquiv m n ⁻¹' (U ×ˢ V))))
  hasWeakGradient := appendLift_hasWeakGradient hU hV hVfinite u

@[simp]
theorem liftAppend_apply {m n : ℕ} {U : Set (Vec m)} {V : Set (Vec n)}
    (hU : IsOpen U) (hV : IsOpen V) (hVfinite : volume V < ⊤)
    (u : H1Function U) (z : Vec (m + n)) :
    u.liftAppend hU hV hVfinite z = u (vecAppendEquiv m n z).1 := rfl

@[simp]
theorem liftAppend_grad {m n : ℕ} {U : Set (Vec m)} {V : Set (Vec n)}
    (hU : IsOpen U) (hV : IsOpen V) (hVfinite : volume V < ⊤)
    (u : H1Function U) (z : Vec (m + n)) :
    (u.liftAppend hU hV hVfinite).grad z =
      (vecAppendEquiv m n).symm (u.grad (vecAppendEquiv m n z).1, 0) := rfl

end H1Function
end PDE
