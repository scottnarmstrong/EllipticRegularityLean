module

public import EllipticRegularity.Ch4.GreenFunction.Uniqueness
public import EllipticRegularity.Ch4.GreenFunction.Stampacchia
public import EllipticRegularity.Ch4.GreenFunction.Continuity
public import EllipticRegularity.Ch4.GreenFunction.Flux

/-!
# Existence and basic properties of the Green function (Proposition 4.40)

`greenExists_full` has, after the binders `(d) (hd)` and the two explicit interface hypotheses
`hDir : GreenDirichletConcl d` and `hMax : GreenMaxPrincipleConcl d` (the bodies of the
statements `greenDirichlet` and `greenMaxPrinciple`), exactly the type of the statement
`PDE.greenExists`.
-/

@[expose] public section

open scoped Topology ENNReal

namespace PDE.Ch4Green

open MeasureTheory PDE Filter

/-- **Proposition 4.40** (Green function: existence, uniqueness, nonnegativity,
Stampacchia bound with `C₀ = C₀(d)`, `H¹` and `a`-harmonic away from the pole with a continuous
representative, and the flux identity). -/
theorem greenExists_full (d : ℕ) (hd : 3 ≤ d) (hDir : GreenDirichletConcl d)
    (hMax : GreenMaxPrincipleConcl d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (Λ R : ℝ), 0 < R → ∀ a : CoeffField d,
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) R))) →
      (∀ x ∈ euclideanBall (0 : Vec d) R, IsEllipticMatrix 1 Λ (a x)) →
      (∃ G : Vec d → ℝ, IsGreenFunction a R G) ∧
      (∀ G G' : Vec d → ℝ, IsGreenFunction a R G → IsGreenFunction a R G' →
        G =ᵐ[volumeOn (euclideanBall (0 : Vec d) R)] G') ∧
      ∀ G : Vec d → ℝ, IsGreenFunction a R G →
        (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), 0 ≤ G x) ∧
        (IntegrableOn G (euclideanBall (0 : Vec d) R) ∧
          ∀ E : Set (Vec d), MeasurableSet E → E ⊆ euclideanBall (0 : Vec d) R →
            ∫⁻ x in E, ENNReal.ofReal (G x) ≤
              ENNReal.ofReal (C₀ * (volume E).toReal ^ ((2 : ℝ) / d))) ∧
        (∀ t : ℝ, 0 < t →
          volume {x ∈ euclideanBall (0 : Vec d) R | t < G x} ≤
            ENNReal.ofReal ((C₀ / t) ^ ((d : ℝ) / ((d : ℝ) - 2)))) ∧
        (∃ Gc : Vec d → ℝ,
          ContinuousOn Gc (euclideanBall (0 : Vec d) R \ {0}) ∧
          Gc =ᵐ[volumeOn (euclideanBall (0 : Vec d) R)] G ∧
          ∀ ε : ℝ, 0 < ε → ε < R →
            ∃ H : H1Function (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) ε),
              H.toFun =ᵐ[volumeOn (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) ε)] G ∧
              IsWeakDivergenceFormSolutionOn a
                (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) ε) H
                (0 : Vec d → ℝ) (0 : Vec d → Vec d)) ∧
        (∀ ε : ℝ, 0 < ε → ε < R →
          ∀ H : H1Function (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (ε / 2)),
          H.toFun =ᵐ[volumeOn (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (ε / 2))] G →
          ∀ φ : Vec d → ℝ, (∃ K : NNReal, LipschitzWith K φ) → HasCompactSupport φ →
            tsupport φ ⊆ euclideanBall (0 : Vec d) R →
            (∃ c : ℝ, ∀ x ∈ euclideanBall (0 : Vec d) ε, φ x = c) →
            ∫ x in euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε,
                vecDot (fun i => fderiv ℝ φ x (basisVec i)) (matVecMul (a x) (H.grad x)) = φ 0) := by
  obtain ⟨C₀, hC₀, hstamp⟩ := stampacchia_approx (d := d) hd
  refine ⟨C₀, hC₀, ?_⟩
  intro Λ R hR a hmeas hell
  obtain ⟨S⟩ := ApproxSetting.nonempty_ofDirichlet hDir hR hmeas hell
  have hGnn : ∀ n, ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)),
      0 ≤ (S.G n).toH1Function.toFun x := fun n =>
    (hMax Λ R hR a hmeas hell a (Or.inl rfl)).2 _ (memL2On_approxSource hR.le _)
      (Eventually.of_forall fun x => approxSource_nonneg _ x) (S.G n) (S.solG n)
  refine ⟨S.exists_isGreenFunction hd,
    fun G G' hG hG' => green_unique_of_solvable (by omega) hR S.existsAdj hG hG', ?_⟩
  intro G hG
  have hbound := S.isGreen_lintegral_le hd hGnn hC₀.le (hstamp S) hG
  have hnonneg := S.isGreen_nonneg hd hGnn hG
  have hBm : MeasurableSet (euclideanBall (0 : Vec d) R) := measurableSet_euclideanBall _ _
  have hBfin : volume (euclideanBall (0 : Vec d) R) ≠ ⊤ := volume_euclideanBall_ne_top _ hR.le
  refine ⟨hnonneg, ⟨?_, hbound⟩, fun t ht => ?_, ?_, fun ε hε hεR H hHG φ hφL hφc hφB hφc' =>
    S.isGreen_flux hd hG hε hεR H hHG φ hφL hφc hφB hφc'⟩
  · exact integrableOn_of_lintegral_ofReal_lt_top hG.1 hnonneg
      ((hbound _ hBm subset_rfl).trans_lt ENNReal.ofReal_lt_top)
  · exact volume_lt_le_of_lintegral hd hBm hBfin hG.1 hC₀.le hbound ht
  · obtain ⟨Gc, hGc, hGcae⟩ := S.exists_continuous_rep hd hG
    refine ⟨Gc, hGc, hGcae, fun ε hε hεR => ?_⟩
    obtain ⟨H, hHG, hHsol, -⟩ := S.exists_harmonic hd hG hε hεR
    exact ⟨H, by rw [hHG], hHsol⟩

end PDE.Ch4Green
