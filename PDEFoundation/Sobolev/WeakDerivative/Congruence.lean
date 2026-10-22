module

public import PDEFoundation.Sobolev.WeakDerivative

/-!
# Congruence for weak partial derivatives

Weak partial derivatives depend only on the almost-everywhere class of the
value representative.  The public lemmas in this file retain local
integrability hypotheses for both value representatives and for every weak
partial representative.  These hypotheses prevent the total Bochner integral
from making a formally true but analytically vacuous congruence statement.
-/

@[expose] public section

namespace PDE

namespace HasWeakPartialDerivOn

/-- Replacing a locally integrable value representative by an a.e.-equal one
on a measurable domain preserves a locally integrable weak partial
representative. -/
theorem congr_value_ae {d : ℕ} {U : Set (Vec d)} {i : Fin d}
    {u v gi : Vec d → ℝ}
    (h : HasWeakPartialDerivOn U i u gi)
    (hU : MeasurableSet U)
    (_huLoc : MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume)
    (_hvLoc : MeasureTheory.LocallyIntegrableOn v U MeasureTheory.volume)
    (_hgiLoc : MeasureTheory.LocallyIntegrableOn gi U MeasureTheory.volume)
    (huv : u =ᵐ[volumeOn U] v) :
    HasWeakPartialDerivOn U i v gi := by
  intro φ hφSmooth hφCompact hφSupport
  have huvAmbient :
      ∀ᵐ x ∂MeasureTheory.volume, x ∈ U → u x = v x :=
    (MeasureTheory.ae_restrict_iff' hU).mp huv
  calc
    ∫ x in U, v x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume =
        ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i)
          ∂MeasureTheory.volume := by
            apply MeasureTheory.setIntegral_congr_ae hU
            filter_upwards [huvAmbient] with x hx
            intro hxU
            rw [← hx hxU]
    _ = -∫ x in U, gi x * φ x ∂MeasureTheory.volume :=
      h φ hφSmooth hφCompact hφSupport

/-- Replacing a locally integrable value representative by one equal to it
pointwise on a measurable domain preserves a locally integrable weak partial
representative. -/
theorem congr_value_eqOn {d : ℕ} {U : Set (Vec d)} {i : Fin d}
    {u v gi : Vec d → ℝ}
    (h : HasWeakPartialDerivOn U i u gi)
    (hU : MeasurableSet U)
    (huLoc : MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume)
    (hvLoc : MeasureTheory.LocallyIntegrableOn v U MeasureTheory.volume)
    (hgiLoc : MeasureTheory.LocallyIntegrableOn gi U MeasureTheory.volume)
    (huv : Set.EqOn u v U) :
    HasWeakPartialDerivOn U i v gi :=
  h.congr_value_ae hU huLoc hvLoc hgiLoc
    (MeasureTheory.ae_restrict_of_forall_mem hU huv)

/-- Weak partial representatives of a.e.-equal locally integrable value
representatives agree a.e. on an open domain, provided both weak partial
representatives are locally integrable there. -/
theorem ae_eq_of_ae_eq_value {d : ℕ} {U : Set (Vec d)} {i : Fin d}
    {u v gi hi : Vec d → ℝ}
    (hU : IsOpen U)
    (huLoc : MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume)
    (hvLoc : MeasureTheory.LocallyIntegrableOn v U MeasureTheory.volume)
    (hgiLoc : MeasureTheory.LocallyIntegrableOn gi U MeasureTheory.volume)
    (hhiLoc : MeasureTheory.LocallyIntegrableOn hi U MeasureTheory.volume)
    (huv : u =ᵐ[volumeOn U] v)
    (hgi : HasWeakPartialDerivOn U i u gi)
    (hhi : HasWeakPartialDerivOn U i v hi) :
    gi =ᵐ[volumeOn U] hi := by
  have hhiForU :
      HasWeakPartialDerivOn U i u hi :=
    hhi.congr_value_ae hU.measurableSet hvLoc huLoc hhiLoc huv.symm
  exact ae_eq hU hgiLoc hhiLoc hgi hhiForU

/-- Pointwise-equal locally integrable value representatives have a.e.-equal
locally integrable weak partial representatives on an open domain. -/
theorem ae_eq_of_eqOn_value {d : ℕ} {U : Set (Vec d)} {i : Fin d}
    {u v gi hi : Vec d → ℝ}
    (hU : IsOpen U)
    (huLoc : MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume)
    (hvLoc : MeasureTheory.LocallyIntegrableOn v U MeasureTheory.volume)
    (hgiLoc : MeasureTheory.LocallyIntegrableOn gi U MeasureTheory.volume)
    (hhiLoc : MeasureTheory.LocallyIntegrableOn hi U MeasureTheory.volume)
    (huv : Set.EqOn u v U)
    (hgi : HasWeakPartialDerivOn U i u gi)
    (hhi : HasWeakPartialDerivOn U i v hi) :
    gi =ᵐ[volumeOn U] hi :=
  ae_eq_of_ae_eq_value hU huLoc hvLoc hgiLoc hhiLoc
    (MeasureTheory.ae_restrict_of_forall_mem hU.measurableSet huv) hgi hhi

end HasWeakPartialDerivOn

end PDE
