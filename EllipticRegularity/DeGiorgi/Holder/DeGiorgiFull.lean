module

public import EllipticRegularity.DeGiorgi.Holder.Full
public import PDEFoundation.PDE.DGNM.ClassAlgebra

/-!
# The De Giorgi Hölder statement, with affine stability discharged

Solutions are stable under `u ↦ s * u + t` by the class-algebra facts of
`PDEFoundation.PDE.DGNM.ClassAlgebra`.  The remaining interface hypotheses are the
expansion-of-positivity statement and stability under rescaling of balls.
-/

@[expose] public section

namespace PDE.DGNMHolder

open PDE MeasureTheory

/-- Solutions are stable under `u ↦ s * u + t`. -/
theorem affineStability (d : ℕ) : AffineStability d := by
  intro Λ a _ _ u hsol s t
  have hU := isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) one_pos
  have : IsFiniteMeasure (volumeOn (euclideanBall (0 : Vec d) 1)) := hU.isFiniteMeasure_volumeOn
  refine ⟨(s • u).addConst t,
    DGNM.solutionOn_addConst (DGNM.solutionOn_smul hsol s) t, ?_⟩
  filter_upwards with x
  simp

/-- **De Giorgi's interior Hölder estimate** (Theorem 4.8): the
statement, from expansion of positivity (`hEoP`) and stability of solutions under
rescaling of balls (`hScale`). -/
theorem exists_deGiorgi_holder_constant_full (d : ℕ) (hd : 3 ≤ d)
    (hEoP : ∃ C : ℝ, 0 < C ∧ EoPStatement d C)
    (hScale : ScaleStability d) :
    ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
      Real.exp (-(C * Λ ^ (((d : ℝ) + 2) / 4))) ≤ α ∧
      ∀ (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) 0 →
        ∃ (v : Vec d → ℝ) (M₀ M₁ : ℝ), v =ᵐ[volumeOn (euclideanBall (0 : Vec d) (1 / 2))] u.toFun ∧
          0 ≤ M₀ ∧ 0 ≤ M₁ ∧ (∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), |v x| ≤ M₀) ∧
          EuclideanHolderSeminormLE (euclideanBall (0 : Vec d) (1 / 2)) v α M₁ ∧
          ENNReal.ofReal (M₀ + M₁) ≤ ENNReal.ofReal (C * Λ ^ ((d : ℝ) / 4)) *
            eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1)) :=
  exists_deGiorgi_holder_constant_of_stability d hd hEoP (affineStability d) hScale

end PDE.DGNMHolder
