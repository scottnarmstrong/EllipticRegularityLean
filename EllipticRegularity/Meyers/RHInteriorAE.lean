module

public import EllipticRegularity.Meyers.RHInterior
public import PDEFoundation.PDE.CoefficientModification
public import PDEFoundation.Measure.ForcingScale

/-!
# The interior reverse Hölder inequality for almost-everywhere measurable coefficients

The form of `rh_interior` with exactly the hypotheses on the coefficient field and forcing of the
Meyers statement: entrywise almost-everywhere measurable coefficients, elliptic on the
ball, and a forcing with measurable coordinates and `L²` Euclidean magnitude.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.MeyersRH

open MeasureTheory

/-- **Interior reverse Hölder inequality** for entrywise a.e. measurable coefficients. -/
theorem rh_interior_of_aemeasurable (d : ℕ) (hd : 2 ≤ d) (hSP : ConvexSobolevPoincareHyp d) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧
      ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ (f : Vec d → Vec d),
      (∀ i : Fin d, AEStronglyMeasurable (fun x => f x i)
        (volumeOn (euclideanBall (0 : Vec d) 1))) →
      MemLp (fun x => vecEuclideanNorm (f x)) 2 (volumeOn (euclideanBall (0 : Vec d) 1)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) f →
      ∀ (z : Vec d) (r : ℝ), 0 < r →
        centeredAxisCube z (2 * r) ⊆ euclideanBall (0 : Vec d) 1 →
          ∫ x in centeredAxisCube z r,
              Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x))) ^ 2 ≤
            (C0 * Real.sqrt Λ) * (volume (centeredAxisCube z r)).toReal *
                (integralAverage (centeredAxisCube z (2 * r))
                  (fun x => (Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x))) ^ 2) ^
                    ((d : ℝ) / ((d : ℝ) + 1)))) ^ (((d : ℝ) + 1) / (d : ℝ)) +
              C0 * ∫ x in centeredAxisCube z (2 * r), vecEuclideanNorm (f x) ^ 2 := by
  obtain ⟨C0, hC0, hmain⟩ := rh_interior d hd hSP
  refine ⟨C0, hC0, ?_⟩
  intro Λ a ha hell f hfc hf2 u hsol z r hr hsub
  have hBmeas : MeasurableSet (euclideanBall (0 : Vec d) 1) :=
    (isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) one_pos).measurableSet
  obtain ⟨b, hEllB, hab, hsolB⟩ :=
    exists_isEllipticFieldOn_and_weakSolutionOn_coeffAEEqOn hBmeas ha hell hsol
  have hf : MemVectorL2On (euclideanBall (0 : Vec d) 1) f :=
    memVectorL2On_euclideanBall_of_memLp_vecEuclideanNorm (p := 2) le_rfl (0 : Vec d) one_pos
      subset_rfl (by simpa using hf2) hfc
  have h := hmain Λ b hEllB f hf u hsolB z r hr hsub
  have hQB : centeredAxisCube z r ⊆ euclideanBall (0 : Vec d) 1 := by
    refine Set.Subset.trans ?_ hsub
    intro x hx i _
    have := hx i (Set.mem_univ i)
    simp only [Set.mem_Ioo] at this ⊢
    constructor <;> linarith [this.1, this.2]
  have hEn : ∀ S : Set (Vec d), S ⊆ euclideanBall (0 : Vec d) 1 →
      (fun x => Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x)))) =ᵐ[volumeOn S]
        fun x => Real.sqrt (vecDot (u.grad x) (matVecMul (b x) (u.grad x))) := by
    intro S hS
    have habS : a =ᵐ[volumeOn S] b := ae_restrict_of_ae_restrict_of_subset hS hab
    filter_upwards [habS] with x hx
    simp only [hx]
  have h1 : ∫ x in centeredAxisCube z r,
      Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x))) ^ 2 =
        ∫ x in centeredAxisCube z r,
      Real.sqrt (vecDot (u.grad x) (matVecMul (b x) (u.grad x))) ^ 2 :=
    integral_congr_ae ((hEn _ hQB).mono fun x hx => by simp only [hx])
  have h2 : integralAverage (centeredAxisCube z (2 * r))
      (fun x => (Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x))) ^ 2) ^
        ((d : ℝ) / ((d : ℝ) + 1))) =
      integralAverage (centeredAxisCube z (2 * r))
      (fun x => (Real.sqrt (vecDot (u.grad x) (matVecMul (b x) (u.grad x))) ^ 2) ^
        ((d : ℝ) / ((d : ℝ) + 1))) := by
    unfold integralAverage
    congr 1
    exact integral_congr_ae ((hEn _ hsub).mono fun x hx => by simp only [hx])
  rw [h1, h2]
  exact h

end PDE.MeyersRH
