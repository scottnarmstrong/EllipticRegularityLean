module

public import PDEFoundation.PDE.HarmonicReplacement
public import PDEFoundation.PDE.PerturbationEnergy
public import PDEFoundation.PDE.ConstantForcing
public import PDEFoundation.Regularity.HolderBallBounds

/-!
# Harmonic replacement for Hölder coefficient and forcing fields

The coefficient is replaced by the identity and the constant forcing is removed
from the actual weak equation. All testability, measurability and forcing
integrability used by the energy estimate are proved here.
-/

@[expose] public section

namespace PDE

open MeasureTheory

variable {d : ℕ}

/-- Construct the harmonic replacement and bound its actual zero-boundary
error by the Hölder oscillation of the coefficient and forcing. -/
theorem exists_holderHarmonicReplacement_on_euclideanBall
    (hd : 0 < d) {z : Vec d} {R α Ka KF : ℝ}
    (hR : 0 < R) (hα : 0 < α) (hKa : 0 ≤ Ka) (hKF : 0 ≤ KF)
    {a : CoeffField d} {F : Vec d → Vec d}
    (ha : EuclideanMatrixHolderSeminormLE (euclideanBall z R) a α Ka)
    (hF : EuclideanFieldHolderSeminormLE (euclideanBall z R) F α KF)
    (ha0 : a z = 1) (u : H1Function (euclideanBall z R))
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall z R) u 0 F) :
    ∃ h : H1Function (euclideanBall z R),
      ∃ w : H10Function (euclideanBall z R),
        h.toFun = (fun x => u.toFun x - w.toH1Function.toFun x) ∧
        h.grad = (fun x => u.grad x - w.toH1Function.grad x) ∧
        (∀ φ : WeakTestFunction (euclideanBall z R),
          ∫ x in euclideanBall z R, vecDot (h.grad x) (φ.grad x) = 0) ∧
        Real.sqrt (integralAverage (euclideanBall z R)
          (fun x => vecNormSq (w.toH1Function.grad x))) ≤
            R ^ α * (Ka * Real.sqrt (integralAverage (euclideanBall z R)
              (fun x => vecNormSq (u.grad x))) + KF) := by
  obtain ⟨h, w, hvalue, hgrad, horth, _henergy⟩ :=
    exists_harmonicReplacement_on_euclideanBall hd hR u
  have hz := center_mem_euclideanBall z hR
  have hcoeffMeas (i j : Fin d) :
      AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall z R)) :=
    ((ha.coordinate i j).continuousOn hα hKa).aemeasurable
      (isOpen_euclideanBall z R).measurableSet
  have hclose : ∀ᵐ x ∂volumeOn (euclideanBall z R),
      IsMatrixPerturbationLE (Ka * R ^ α) (a x) 1 := by
    filter_upwards [ae_restrict_mem (isOpen_euclideanBall z R).measurableSet] with x hx
    simpa only [ha0] using ha.sub_center_bound hα.le hKa hR hz (Set.Subset.refl _) hx
  have hforce := hF.memVectorL2On_sub_center hα hKF hR hz (Set.Subset.refl _)
  have herror := sqrt_integralAverage_vecNormSq_replacement_error_le
    (mul_nonneg hKa (Real.rpow_nonneg hR.le α)) hcoeffMeas hclose hforce
    (hsol.sub_const_forcing (F z)) w
    (by simpa only [hgrad] using horth w)
  have hforceBound := hF.sqrt_mean_sub_center_le_of_pos
    hα hKF hR hz (Set.Subset.refl _)
  refine ⟨h, w, hvalue, hgrad, ?_, ?_⟩
  · intro φ
    let φ10 := H10Function.ofContDiff (isOpen_euclideanBall z R)
      φ.contDiff φ.hasCompactSupport φ.tsupport_subset
    simpa only [φ10, H10Function.ofContDiff_grad, WeakTestFunction.grad_apply,
      WeakTestFunction.partialDeriv] using! horth φ10
  · calc
      Real.sqrt (integralAverage (euclideanBall z R)
          (fun x => vecNormSq (w.toH1Function.grad x))) ≤
          (Ka * R ^ α) * Real.sqrt (integralAverage (euclideanBall z R)
            (fun x => vecNormSq (u.grad x))) +
              Real.sqrt (integralAverage (euclideanBall z R)
                (fun x => vecNormSq (F x - F z))) := herror
      _ ≤ (Ka * R ^ α) * Real.sqrt (integralAverage (euclideanBall z R)
            (fun x => vecNormSq (u.grad x))) + KF * R ^ α :=
        add_le_add le_rfl hforceBound
      _ = _ := by ring

end PDE
