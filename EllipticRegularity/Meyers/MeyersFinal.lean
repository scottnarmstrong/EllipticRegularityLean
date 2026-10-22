module

public import EllipticRegularity.Meyers.AssemblyDirichlet
public import EllipticRegularity.Meyers.Duality
public import EllipticRegularity.Meyers.RHFinal
public import EllipticRegularity.Meyers.RHFinalBoundary

/-!
# Final assembly of Theorem 4.4

The Meyers estimate, from the Gehring lemma, the reverse Holder inequalities,
the high-exponent assembly and the duality argument for `p < 2`.
-/

@[expose] public section

namespace PDE.MeyersFinal

open MeasureTheory

/-- The Meyers estimate with the range of exponents `2 + c / sqrt Lambda`. -/
theorem meyers_final
    (d : ℕ) (hd : 2 ≤ d) (hG : MeyersAssembly.GehringConclusion d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d,
        AEMeasurable (fun x => a x i j)
          (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      (∀ (p : ℝ), 2 ≤ p → p ≤ 2 + c / Real.sqrt Λ →
        ∀ (f : Vec d → Vec d),
        (∀ i : Fin d,
          AEStronglyMeasurable (fun x => f x i)
            (volumeOn (euclideanBall (0 : Vec d) 1))) →
        MemLp (fun x => vecEuclideanNorm (f x)) (ENNReal.ofReal p)
          (volumeOn (euclideanBall (0 : Vec d) 1)) →
        ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
        IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u
            (0 : Vec d → ℝ) f →
          eLpMeanNormOn (euclideanBall (0 : Vec d) (1 / 2)) (ENNReal.ofReal p)
              (fun x => Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x)))) ≤
            ENNReal.ofReal C *
              (eLpMeanNormOn (euclideanBall (0 : Vec d) 1) 2
                  (fun x => Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x)))) +
                euclideanFieldELpMeanNormOn (euclideanBall (0 : Vec d) 1)
                  (ENNReal.ofReal p) f)) ∧
      (∀ (p : ℝ), (2 + c / Real.sqrt Λ) / (1 + c / Real.sqrt Λ) ≤ p →
        p ≤ 2 + c / Real.sqrt Λ →
        ∀ (f : Vec d → Vec d),
        (∀ i : Fin d,
          AEStronglyMeasurable (fun x => f x i)
            (volumeOn (euclideanBall (0 : Vec d) 1))) →
        MemLp (fun x => vecEuclideanNorm (f x)) 2
          (volumeOn (euclideanBall (0 : Vec d) 1)) →
        MemLp (fun x => vecEuclideanNorm (f x)) (ENNReal.ofReal p)
          (volumeOn (euclideanBall (0 : Vec d) 1)) →
        ∀ u : H10Function (euclideanBall (0 : Vec d) 1),
        IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1)
            u.toH1Function (0 : Vec d → ℝ) f →
          eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
              (volumeOn (euclideanBall (0 : Vec d) 1)) ≤
            ENNReal.ofReal C *
              eLpNorm (fun x => vecEuclideanNorm (f x)) (ENNReal.ofReal p)
                (volumeOn (euclideanBall (0 : Vec d) 1))) := by
  obtain ⟨c, C, hc, hC, H⟩ := MeyersAssembly.meyers_interior_and_dirichlet_high d
    hG (meyers_rh_interior_final d hd) (meyers_rh_boundary_final d hd)
  refine ⟨c, C, hc, hC, fun Λ a ha hell => ⟨fun p hp hpΛ => (H Λ a ha hell).1 p hp hpΛ, ?_⟩⟩
  intro p hp1 hp2
  rcases le_total 2 p with h2 | h2
  · exact (H Λ a ha hell).2 p h2 hp2
  · intro f hfm hf2 hfp u hu
    refine MeyersDuality.dirichlet_low_of_high (by omega) c C hc ?_ Λ a ha hell p hp1 h2 f hfm hf2 hfp u hu
    intro Λ' b hb hellb p' hp' hp'Λ F hF hF2 hFp v hv
    exact (H Λ' b hb hellb).2 p' hp' hp'Λ F hF hF2 hFp v hv

end PDE.MeyersFinal
