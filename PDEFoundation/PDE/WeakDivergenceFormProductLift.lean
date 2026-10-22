module

public import PDEFoundation.Ambient.MatAppend
public import PDEFoundation.PDE.WeakDivergenceForm
public import PDEFoundation.Sobolev.H1.ProductLift
public import PDEFoundation.Sobolev.WeakDivergenceProductLift

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal

namespace IsWeakDivergenceFormL2SolutionOn

/-- Lift a safe weak divergence-form solution across a finite-volume unused
coordinate factor, with an arbitrary coefficient block on the unused variables. -/
theorem liftAppend {m n : ℕ} {U : Set (Vec m)} {V : Set (Vec n)}
    (hU : IsOpen U) (hV : IsOpen V) (hVfinite : volume V < ⊤)
    {a : CoeffField m} (B : Mat n) {u : H1Function U} {F : Vec m → Vec m}
    (hsol : IsWeakDivergenceFormL2SolutionOn a U u (fun _ => 0) F) :
    IsWeakDivergenceFormL2SolutionOn
      (fun z => matAppend (a (vecAppendEquiv m n z).1) B)
      (vecAppendEquiv m n ⁻¹' (U ×ˢ V))
      (u.liftAppend hU hV hVfinite) (fun _ => 0)
      (fun z => (vecAppendEquiv m n).symm (F (vecAppendEquiv m n z).1, 0)) := by
  let E : Set (Vec (m + n)) := vecAppendEquiv m n ⁻¹' (U ×ˢ V)
  let flux : Vec m → Vec m := fun x => matVecMul (a x) (u.grad x)
  let J : Vec m → Vec m := fun x => flux x + F x
  let liftFlux : Vec (m + n) → Vec (m + n) := fun z =>
    (vecAppendEquiv m n).symm (flux (vecAppendEquiv m n z).1, 0)
  let liftF : Vec (m + n) → Vec (m + n) := fun z =>
    (vecAppendEquiv m n).symm (F (vecAppendEquiv m n z).1, 0)
  have hLiftFlux : MemVectorL2On E liftFlux := by
    intro k
    refine Fin.addCases (motive := fun k : Fin (m + n) =>
      MemLp (fun z => liftFlux z k) 2 (volume.restrict E)) ?_ ?_ k
    · intro i
      simpa only [liftFlux, E, vecAppendEquiv_symm_apply_castAdd] using
        memLp_comp_fst_vecAppendEquiv m n hU.measurableSet hV.measurableSet
          hVfinite (hsol.flux_memL2 i)
    · intro j
      simpa only [liftFlux, vecAppendEquiv_symm_apply_natAdd] using!
        (MemLp.zero : MemLp (0 : Vec (m + n) → ℝ) 2 (volume.restrict E))
  have hLiftF : MemVectorL2On E liftF := by
    intro k
    refine Fin.addCases (motive := fun k : Fin (m + n) =>
      MemLp (fun z => liftF z k) 2 (volume.restrict E)) ?_ ?_ k
    · intro i
      simpa only [liftF, E, vecAppendEquiv_symm_apply_castAdd] using
        memLp_comp_fst_vecAppendEquiv m n hU.measurableSet hV.measurableSet
          hVfinite (hsol.forcing_memL2 i)
    · intro j
      simpa only [liftF, vecAppendEquiv_symm_apply_natAdd] using!
        (MemLp.zero : MemLp (0 : Vec (m + n) → ℝ) 2 (volume.restrict E))
  have hFluxEq (z : Vec (m + n)) :
      matVecMul (matAppend (a (vecAppendEquiv m n z).1) B)
          ((u.liftAppend hU hV hVfinite).grad z) = liftFlux z := by
    rw [H1Function.liftAppend_grad]
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp [matVecMul, matAppend, Fin.sum_univ_add, liftFlux, flux]
    · simp [matVecMul, matAppend, Fin.sum_univ_add, liftFlux]

  have hdata : DivergenceFormL2DataOn
      (fun z => matAppend (a (vecAppendEquiv m n z).1) B) E
      (u.liftAppend hU hV hVfinite) (fun _ => 0) liftF := {
    flux_memL2 := fun k => (hLiftFlux k).ae_eq <|
      Filter.Eventually.of_forall fun z => congrArg (fun w : Vec (m + n) => w k) (hFluxEq z).symm
    source_memL2 := MemLp.zero
    forcing_memL2 := hLiftF
  }
  have hJ : MemVectorL2On U J := by
    intro i
    exact (hsol.flux_memL2 i).add (hsol.forcing_memL2 i)
  have hdiv : ∀ ψ : WeakTestFunction U,
      ∫ x in U, vecDot (J x) (classicalGradient ψ x) = 0 := by
    intro ψ
    have ht := hsol.toDivergenceFormL2DataOn.testable ψ
    have hsplit :
        (∫ x in U, vecDot (J x) (classicalGradient ψ x)) =
          (∫ x in U, vecDot (flux x) (ψ.grad x)) +
            ∫ x in U, vecDot (F x) (ψ.grad x) := by
      rw [← MeasureTheory.integral_add ht.flux_integrable ht.forcing_integrable]
      apply integral_congr_ae
      filter_upwards with x
      simp only [J, flux, vecDot, Pi.add_apply, add_mul,
        Finset.sum_add_distrib, WeakTestFunction.grad_apply,
        WeakTestFunction.partialDeriv, classicalGradient_apply]
    rw [hsplit, hsol.identity ψ]
    simp
  have hLiftDiv := integral_vecDot_classicalGradient_eq_zero_productLift
    hU hV hVfinite hJ hdiv
  refine { hdata with identity := ?_ }
  intro φ
  have hzero := hLiftDiv φ
  change (∫ z in E, vecDot
      ((vecAppendEquiv m n).symm (J (vecAppendEquiv m n z).1, 0))
      (classicalGradient φ z)) = 0 at hzero
  have hsum :
      (∫ z in E, vecDot (liftFlux z + liftF z) (φ.grad z)) = 0 := by
    calc
      _ = ∫ z in E, vecDot
          ((vecAppendEquiv m n).symm (J (vecAppendEquiv m n z).1, 0))
          (classicalGradient φ z) := by
        apply integral_congr_ae
        filter_upwards with z
        have hv : liftFlux z + liftF z =
            (vecAppendEquiv m n).symm
              (J (vecAppendEquiv m n z).1, 0) := by
          ext k
          refine Fin.addCases (fun i => ?_) (fun j => ?_) k
          · simp [J, liftFlux, liftF]
          · simp [liftFlux, liftF]
        rw [hv]
        congr 1
      _ = 0 := hzero
  have hLiftFluxInt : IntegrableOn
      (fun z => vecDot (liftFlux z) (φ.grad z)) E :=
    integrableOn_vecDot_weakTestFunction_grad hLiftFlux φ
  have hLiftFInt : IntegrableOn
      (fun z => vecDot (liftF z) (φ.grad z)) E :=
    integrableOn_vecDot_weakTestFunction_grad hLiftF φ
  have hsplit :
      (∫ z in E, vecDot (liftFlux z + liftF z) (φ.grad z)) =
        (∫ z in E, vecDot (liftFlux z) (φ.grad z)) +
          ∫ z in E, vecDot (liftF z) (φ.grad z) := by
    calc
      _ = ∫ z in E, (vecDot (liftFlux z) (φ.grad z) +
          vecDot (liftF z) (φ.grad z)) := by
        apply integral_congr_ae
        filter_upwards with z
        simp only [vecDot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      _ = _ := MeasureTheory.integral_add hLiftFluxInt hLiftFInt

  rw [hsplit] at hsum
  change (∫ z in E, vecDot
      (matVecMul (matAppend (a (vecAppendEquiv m n z).1) B)
        ((u.liftAppend hU hV hVfinite).grad z)) (φ.grad z)) =
    (∫ z in E, (0 : ℝ) * φ z) - ∫ z in E, vecDot (liftF z) (φ.grad z)
  rw [show (∫ z in E, vecDot
      (matVecMul (matAppend (a (vecAppendEquiv m n z).1) B)
        ((u.liftAppend hU hV hVfinite).grad z)) (φ.grad z)) =
      ∫ z in E, vecDot (liftFlux z) (φ.grad z) by
    apply integral_congr_ae
    filter_upwards with z
    rw [hFluxEq]]
  simp only [zero_mul, integral_zero, zero_sub]
  linarith

end IsWeakDivergenceFormL2SolutionOn
end PDE
