module

public import EllipticRegularity.Parabolic.Cauchy.Weights.NashGeometry
public import EllipticRegularity.Parabolic.Moser.SliceOrderTimeSets
public import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# Restricting Cauchy solutions to a later time slab

The midpoint argument applies the first weighted estimate to the restriction
of the supplied solution. This file proves that restriction remains a Cauchy
solution with its midpoint slice as initial datum.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Weights

open MeasureTheory Set

variable {d : ℕ}

private theorem parWeakIntegrand_zero_of_notMem_tsupport
    {s T : ℝ} {a : ParCoeffField d}
    {u : ParH1Function (univ : Set (Vec d)) (Icc s T)}
    {φ : Vec d × ℝ → ℝ} {z : Vec d × ℝ}
    (hz : z ∉ tsupport φ) : parWeakIntegrand a u φ z = 0 := by
  have hderiv : fderiv ℝ φ z = 0 := fderiv_of_notMem_tsupport ℝ hz
  have hgrad : parSpaceGrad φ z = 0 := by
    ext i
    simp [parSpaceGrad, hderiv]
  simp [parWeakIntegrand, parTimeDeriv, hderiv, hgrad, vecDot]

/-- Restrict the parabolic coefficient bounds to a smaller time interval. -/
theorem parabolicCoeff_restrict_time {s m t lam Lam : ℝ}
    {a : ParCoeffField d}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s t)) (hsm : s ≤ m) :
    IsParabolicCoeff lam Lam a univ (Icc m t) := by
  have hsubset : (univ : Set (Vec d)) ×ˢ Icc m t ⊆
      (univ : Set (Vec d)) ×ˢ Icc s t :=
    prod_mono subset_rfl (Icc_subset_Icc hsm le_rfl)
  have hle : volume.restrict ((univ : Set (Vec d)) ×ˢ Icc m t) ≤
      volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s t) :=
    Measure.restrict_mono hsubset le_rfl
  exact ⟨fun i j => (ha.measurable i j).mono_measure hle,
    (ae_mono hle ha.elliptic)⟩

/-- Restrict the parabolic coefficient bounds to an arbitrary closed
subinterval. -/
theorem parabolicCoeff_restrict_closedInterval {s t a b lam Lam : ℝ}
    {coeff : ParCoeffField d} (ha : IsParabolicCoeff lam Lam coeff univ (Icc s t))
    (hsub : Icc a b ⊆ Icc s t) :
    IsParabolicCoeff lam Lam coeff univ (Icc a b) := by
  have hset : (univ : Set (Vec d)) ×ˢ Icc a b ⊆
      (univ : Set (Vec d)) ×ˢ Icc s t := prod_mono subset_rfl hsub
  have hle : volume.restrict ((univ : Set (Vec d)) ×ˢ Icc a b) ≤
      volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s t) :=
    Measure.restrict_mono hset le_rfl
  exact ⟨fun i j => (ha.measurable i j).mono_measure hle,
    (ae_mono hle ha.elliptic)⟩

/-- Restrict a Cauchy solution to any closed subinterval, using its
slice at the new left endpoint as the restricted initial datum. -/
theorem cauchy_solution_restrict_closedInterval
    {s T a b : ℝ} (hsub : Icc a b ⊆ Icc s T)
    {coeff : ParCoeffField d} {f : Vec d → ℝ}
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution coeff s T f u) :
    IsCauchySolution coeff a b (fun x => u.toFun (x, a))
      (PDE.Parabolic.Moser.restrictParH1TimeSet u hsub) := by
  let v := PDE.Parabolic.Moser.restrictParH1TimeSet u hsub
  have hweak : IsParabolicWeakSolution coeff univ (Icc a b) v := by
    intro φ
    let ψ : ParTestFunction (univ : Set (Vec d)) (interior (Icc s T)) := {
      toFun := φ.toFun
      contDiff := φ.contDiff
      hasCompactSupport := φ.hasCompactSupport
      tsupport_subset := φ.tsupport_subset.trans <|
        prod_mono subset_rfl (interior_mono hsub)
    }
    have hψ := hu.1 ψ
    have hzero : ∀ z ∈ ((univ : Set (Vec d)) ×ˢ Icc s T) \
        ((univ : Set (Vec d)) ×ˢ Icc a b), parWeakIntegrand coeff u φ.toFun z = 0 := by
      intro z hz
      have hznot : z ∉ tsupport φ.toFun := by
        intro hzin
        have hzt := φ.tsupport_subset hzin
        have hzab : z.2 ∈ Icc a b := interior_subset hzt.2
        exact hz.2 ⟨mem_univ z.1, hzab⟩
      exact parWeakIntegrand_zero_of_notMem_tsupport hznot
    have hset : (univ : Set (Vec d)) ×ˢ Icc a b ⊆
        (univ : Set (Vec d)) ×ˢ Icc s T := prod_mono subset_rfl hsub
    have hintegrals :
        ∫ z in univ ×ˢ Icc s T, parWeakIntegrand coeff u φ.toFun z =
          ∫ z in univ ×ˢ Icc a b, parWeakIntegrand coeff u φ.toFun z :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        (MeasurableSet.prod MeasurableSet.univ measurableSet_Icc) hset hzero
    constructor
    · exact hψ.1.mono_set hset
    · have hψzero :
          ∫ z in univ ×ˢ Icc s T, parWeakIntegrand coeff u φ.toFun z = 0 := by
        simpa [ψ] using hψ.2
      change ∫ z in (univ : Set (Vec d)) ×ˢ Icc a b,
        parWeakIntegrand coeff u φ.toFun z = 0
      rw [← hintegrals]
      exact hψzero
  refine ⟨hweak, ?_⟩
  change ∀ᵐ x : Vec d, u.toFun (x, a) = u.toFun (x, a)
  exact Filter.Eventually.of_forall fun _ => rfl

end PDE.Parabolic.Cauchy.Weights
