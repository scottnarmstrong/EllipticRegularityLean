module

public import EllipticRegularity.DeGiorgi.LocalMax.Main
public import EllipticRegularity.DeGiorgi.Holder.Scaling
public import PDEFoundation.PDE.DGNM.Scaling
public import PDEFoundation.PDE.DGNM.ScalingMeasure
public import PDEFoundation.PDE.DGNM.ClassAlgebra
public import PDEFoundation.PDE.DGNM.PositivePart

/-!
# The local maximum principle on rescaled balls

For a subsolution `u` on an open set `U` and a ball `B_ρ(x₀) ⊆ U`,
`ess sup_{B_{ρ/2}(x₀)} u₊ ≤ C Λ^{d/4} ρ^{-d/2} ‖u‖_{L²(B_ρ(x₀))}`,
obtained from the `L^∞` estimate on `B_1` by `blowUp`.  Negation gives the
statement for supersolutions (lower bounds), and Lemma 4.10 gives it for
`(u - k)₊`.
-/

@[expose] public section

namespace PDE.DGNMScaled

open PDE MeasureTheory

variable {d : ℕ}

/-- Core scaling step, with the `B_1` constant given as a hypothesis `hC`. -/
theorem essSup_le_of_blowUp {C : ℝ}
    (hC : ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSubharmonicOn a (euclideanBall (0 : Vec d) 1) u →
        essSup (fun x => ENNReal.ofReal (u.toFun x))
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
          ENNReal.ofReal (C * Λ ^ ((d : ℝ) / 4)) *
            eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1)))
    {U : Set (Vec d)} (hUo : IsOpen U) {Λ : ℝ} {a : CoeffField d}
    (ha : ∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsub : IsWeakDivergenceFormSubharmonicOn a U u)
    {x₀ : Vec d} {ρ : ℝ} (hρ : 0 < ρ) (hball : euclideanBall x₀ ρ ⊆ U) :
    essSup (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall x₀ (ρ / 2))) ≤
      ENNReal.ofReal (C * Λ ^ ((d : ℝ) / 4)) *
        (ENNReal.ofReal ((ρ ^ d)⁻¹) ^ ((1 : ℝ) / 2) *
          eLpNorm u.toFun 2 (volumeOn (euclideanBall x₀ ρ))) := by
  have h := hC Λ (DGNM.blowUpCoeff a x₀ ρ) (DGNM.blowUpCoeff_aemeasurable ha x₀ hρ hball)
    (DGNM.blowUpCoeff_elliptic hEll x₀ hρ hball) (DGNM.blowUp u x₀ hρ hball)
    (DGNM.subharmonicOn_blowUp hUo hsub x₀ hρ hball)
  have hfun : (DGNM.blowUp u x₀ hρ hball).toFun = fun y => u.toFun (ρ • y + x₀) :=
    funext (DGNM.blowUp_toFun u x₀ hρ hball)
  rw [hfun] at h
  have hE : essSup (fun y => ENNReal.ofReal (u.toFun (ρ • y + x₀)))
      (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) =
      essSup (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall x₀ (ρ / 2))) := by
    rw [DGNM.essSup_comp_affineScale x₀ hρ _ (fun x => ENNReal.ofReal (u.toFun x)),
      DGNM.translateSet_smul_euclideanBall x₀ hρ]
    have : ρ * (1 / 2) = ρ / 2 := by ring
    rw [this]
  have hmeas : AEStronglyMeasurable u.toFun (volumeOn (euclideanBall x₀ (ρ * 1))) := by
    rw [mul_one]
    exact u.memL2.aestronglyMeasurable.mono_measure (Measure.restrict_mono hball le_rfl)
  have hN := PDE.DGNMHolder.eLpNorm_comp_affine_ball hρ x₀ 1 u.toFun hmeas
  rw [mul_one] at hN
  rw [hE, hN] at h
  exact h

/-- **Scaled local maximum principle.** There is `C(d) > 0` such that every subsolution
on an open set `U` satisfies, on every ball `B_ρ(x₀) ⊆ U`,
`ess sup_{B_{ρ/2}(x₀)} u₊ ≤ C Λ^{d/4} ρ^{-d/2} ‖u‖_{L²(B_ρ(x₀))}`
(the factor `ρ^{-d/2}` appears as `ofReal ((ρ^d)⁻¹) ^ (1/2)`). -/
theorem exists_scaled_localMax_constant (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {U : Set (Vec d)}, IsOpen U → ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn U)) →
      (∀ x ∈ U, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function U, IsWeakDivergenceFormSubharmonicOn a U u →
      ∀ (x₀ : Vec d) (ρ : ℝ), 0 < ρ → euclideanBall x₀ ρ ⊆ U →
        essSup (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall x₀ (ρ / 2))) ≤
          ENNReal.ofReal (C * Λ ^ ((d : ℝ) / 4)) *
            (ENNReal.ofReal ((ρ ^ d)⁻¹) ^ ((1 : ℝ) / 2) *
              eLpNorm u.toFun 2 (volumeOn (euclideanBall x₀ ρ))) := by
  obtain ⟨C, hC0, hC⟩ := PDE.DGNMLocalMax.exists_localMaxPrinciple_constant_full d hd
  exact ⟨C, hC0, fun hUo Λ a ha hEll u hsub x₀ ρ hρ hball =>
    essSup_le_of_blowUp hC hUo ha hEll hsub hρ hball⟩

/-- Lower-bound version for supersolutions (via `u ↦ -u`):
`ess sup_{B_{ρ/2}(x₀)} u₋ ≤ C Λ^{d/4} ρ^{-d/2} ‖u‖_{L²(B_ρ(x₀))}`. -/
theorem exists_scaled_localMin_constant (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {U : Set (Vec d)}, IsOpen U → ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn U)) →
      (∀ x ∈ U, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function U, IsWeakDivergenceFormSuperharmonicOn a U u →
      ∀ (x₀ : Vec d) (ρ : ℝ), 0 < ρ → euclideanBall x₀ ρ ⊆ U →
        essSup (fun x => ENNReal.ofReal (-u.toFun x)) (volumeOn (euclideanBall x₀ (ρ / 2))) ≤
          ENNReal.ofReal (C * Λ ^ ((d : ℝ) / 4)) *
            (ENNReal.ofReal ((ρ ^ d)⁻¹) ^ ((1 : ℝ) / 2) *
              eLpNorm u.toFun 2 (volumeOn (euclideanBall x₀ ρ))) := by
  obtain ⟨C, hC0, hC⟩ := exists_scaled_localMax_constant d hd
  refine ⟨C, hC0, fun {U} hUo Λ a ha hEll u hsup x₀ ρ hρ hball => ?_⟩
  have h := hC hUo Λ a ha hEll (-u) (DGNM.subharmonicOn_neg hsup) x₀ ρ hρ hball
  have hn : eLpNorm (-u).toFun 2 (volumeOn (euclideanBall x₀ ρ)) =
      eLpNorm u.toFun 2 (volumeOn (euclideanBall x₀ ρ)) := by
    have : (-u).toFun = -u.toFun := rfl
    rw [this, eLpNorm_neg]
  rw [hn] at h
  exact h

/-- Scaled local maximum principle for the positive part `(u - k)₊` of a subsolution
on a bounded convex domain (Lemma 4.10): the bound is in terms of the `L²` norm
of `(u - k)₊`. -/
theorem exists_scaled_localMax_positivePart_constant (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {U : Set (Vec d)}, IsOpenBoundedConvexDomain U →
      ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn U)) →
      (∀ x ∈ U, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function U, IsWeakDivergenceFormSubharmonicOn a U u → ∀ k : ℝ,
      ∀ (x₀ : Vec d) (ρ : ℝ), 0 < ρ → euclideanBall x₀ ρ ⊆ U →
        essSup (fun x => ENNReal.ofReal (max (u.toFun x - k) 0))
            (volumeOn (euclideanBall x₀ (ρ / 2))) ≤
          ENNReal.ofReal (C * Λ ^ ((d : ℝ) / 4)) *
            (ENNReal.ofReal ((ρ ^ d)⁻¹) ^ ((1 : ℝ) / 2) *
              eLpNorm (fun x => max (u.toFun x - k) 0) 2 (volumeOn (euclideanBall x₀ ρ))) := by
  obtain ⟨C, hC0, hC⟩ := exists_scaled_localMax_constant d hd
  refine ⟨C, hC0, fun {U} hU Λ a ha hEll u hsub k x₀ ρ hρ hball => ?_⟩
  exact hC hU.isOpen Λ a ha hEll _ (DGNM.subharmonicOn_positivePartSubConst hU ha hEll hsub k)
    x₀ ρ hρ hball

end PDE.DGNMScaled
