module

public import EllipticRegularity.Meyers.Assembly
public import EllipticRegularity.Meyers.EnergyBounds
public import EllipticRegularity.Meyers.RHFinalCutoff
public import EllipticRegularity.Meyers.RHFinalID
public import EllipticRegularity.Meyers.RHFinalSP
public import PDEFoundation.PDE.CoefficientModification
public import PDEFoundation.Measure.ForcingScale

/-!
# The boundary reverse Hölder interface, instantiated

`MeyersAssembly.MeyersRHBoundary d` follows from `PDE.MeyersRH.boundary_reverse_holder`: the
cutoff hypothesis is the smooth cube cutoff (`Kη = 32 d`), the identity hypothesis is
`cutoff_energy_le_admissible` (for a measurable elliptic representative of the coefficients), the
energy bounds are those of `EnergyBounds.lean`, and the Sobolev--Poincaré hypothesis is
`sp_zeroExtension`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory MeyersRH

/-- The boundary reverse Hölder inequality (Lemma 4.5(ii)) with no interface hypotheses. -/
theorem meyers_rh_boundary_final (d : ℕ) (hd : 2 ≤ d) : MeyersAssembly.MeyersRHBoundary d := by
  obtain ⟨S, hS, hSPz⟩ := sp_zeroExtension (d := d) hd
  refine ⟨boundaryConstant d S (32 * (d : ℝ)), ?_, ?_⟩
  · unfold boundaryConstant
    have : 0 ≤ 24 * (32 * (d : ℝ)) * (1 + 2 ^ (d - 1)) * S * 4 ^ d := by positivity
    linarith
  intro Λ a ha hell f hfc hf2 u hsol z r hr
  have hball := isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) one_pos
  have hΛ : 1 ≤ Λ := MeyersAssembly.one_le_of_elliptic hell
  obtain ⟨b, hEllB, hab, hsolB⟩ :=
    exists_isEllipticFieldOn_and_weakSolutionOn_coeffAEEqOn hball.measurableSet ha hell hsol
  have hfL2 : MemVectorL2On (euclideanBall (0 : Vec d) 1) f :=
    memVectorL2On_euclideanBall_of_memLp_vecEuclideanNorm (p := 2) le_rfl (0 : Vec d) one_pos
      subset_rfl (by simpa using hf2) hfc
  have hE : ∀ x ∈ euclideanBall (0 : Vec d) 1,
      vecEuclideanNorm (u.grad x) ≤ wField a u x ∧
      vecEuclideanNorm (matVecMul (a x) (u.grad x)) ≤ Real.sqrt Λ * wField a u x ∧
      wField a u x ≤ Real.sqrt Λ * vecEuclideanNorm (u.grad x) := fun x hx =>
    ⟨vecEuclideanNorm_le_energyRoot (hell x hx) _,
      vecEuclideanNorm_matVecMul_le_energyRoot (hell x hx) _,
      energyRoot_le_sqrt_mul_vecEuclideanNorm (hell x hx) _⟩
  have hID : ∀ (η : Vec d → ℝ) (c : ℝ), ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      (∀ x, 0 ≤ η x) →
      (∃ v : H10Function (euclideanBall (0 : Vec d) 1), v.toFun = fun x => η x * (u.toFun x - c)) →
      ∫ x in euclideanBall (0 : Vec d) 1, η x * wField a u x ^ 2 ≤
        2 * |∫ x in euclideanBall (0 : Vec d) 1, (u.toFun x - c) *
            vecDot (matVecMul (a x) (u.grad x) + f x) (classicalGradient η x)| +
          ∫ x in euclideanBall (0 : Vec d) 1, η x * vecEuclideanNorm (f x) ^ 2 := by
    intro η c hη hηc hη0 hadm
    have key := cutoff_energy_le_admissible (c := c) hball hEllB u.toH1Function f hfL2 hsolB η
      hη hηc hη0 hadm
    have hmem : ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)),
        x ∈ euclideanBall (0 : Vec d) 1 := ae_restrict_mem hball.measurableSet
    have e1 : ∫ x in euclideanBall (0 : Vec d) 1, η x * wField a u x ^ 2 =
        ∫ x in euclideanBall (0 : Vec d) 1,
          η x * vecDot (u.grad x) (matVecMul (b x) (u.grad x)) := by
      refine integral_congr_ae ?_
      filter_upwards [hab, hmem] with x hx hxm
      have hnn : 0 ≤ vecDot (u.grad x) (matVecMul (a x) (u.grad x)) := by
        have h1 := (hell x hxm).coercive (u.grad x)
        have := vecNormSq_nonneg (u.grad x)
        simp only [one_mul] at h1
        linarith
      unfold wField
      rw [Real.sq_sqrt hnn, hx]
    have e2 : ∫ x in euclideanBall (0 : Vec d) 1, (u.toFun x - c) *
            vecDot (matVecMul (a x) (u.grad x) + f x) (classicalGradient η x) =
        ∫ x in euclideanBall (0 : Vec d) 1, (u.toFun x - c) *
            vecDot (matVecMul (b x) (u.grad x) + f x) (classicalGradient η x) := by
      refine integral_congr_ae ?_
      filter_upwards [hab] with x hx
      rw [hx]
    have e3 : ∫ x in euclideanBall (0 : Vec d) 1, η x * vecEuclideanNorm (f x) ^ 2 =
        ∫ x in euclideanBall (0 : Vec d) 1, η x * vecNormSq (f x) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [vecEuclideanNorm_sq]
    rw [e1, e2, e3]
    exact key
  exact boundary_reverse_holder hd S (32 * (d : ℝ)) hS.le (exists_boundary_cutoff d) Λ hΛ a ha f
    hf2 u hE (hSPz u) hID z r hr

end PDE
