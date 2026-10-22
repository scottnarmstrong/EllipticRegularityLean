module

public import EllipticRegularity.Parabolic.Cauchy.Duality.PairReflection

@[expose] public section

namespace PDE.Parabolic.Duality

open MeasureTheory Set
open PDE.Parabolic.Energy

/-- Reverse an abstract mollified-energy datum in time. The flux changes sign because the
physical-time adjoint equation runs opposite to its forward evolution. -/
noncomputable def reverseEnergyData {d : ℕ} (D : Energy.Data d) : Energy.Data d := by
  let R : Vec d × ℝ → Vec d × ℝ := fun z => (z.1, D.s + D.t - z.2)
  let ρ : ℝ → ℝ := fun τ => D.s + D.t - τ
  have hRmeas : Measurable R :=
    measurable_fst.prodMk (measurable_const.sub measurable_snd)
  have htime : MeasurePreserving ρ (volume.restrict (Ioc D.s D.t))
      (volume.restrict (Ioc D.s D.t)) :=
    time_reflection_preserving_Ioc D.s D.t
  have hspaceTime := time_reflection_preserving_collar_Ioc D.K1 D.K1_measurable D.s D.t
  have hEmb : MeasurableEmbedding R := by
    refine ⟨?_, hRmeas, ?_⟩
    · intro z z' h
      have hfst := congrArg Prod.fst h
      have hsnd := congrArg Prod.snd h
      have hz : D.s + D.t - z.2 = D.s + D.t - z'.2 := by simpa [R] using hsnd
      have htime : z.2 = z'.2 := by linarith
      exact Prod.ext hfst htime
    · intro S hS
      have himage : R '' S = R ⁻¹' S := by
        ext z
        constructor
        · rintro ⟨y, hy, rfl⟩
          change R (R y) ∈ S
          rw [show R (R y) = y by
            ext <;> simp [R]]
          exact hy
        · intro hz
          refine ⟨R z, hz, ?_⟩
          ext <;> simp [R]
      rw [himage]
      exact hRmeas hS
  let G' : Vec d × ℝ → Vec d := fun z => -D.G (R z)
  refine {
    K := D.K
    hK := D.hK
    δ0 := D.δ0
    hδ0 := D.hδ0
    hδ1 := D.hδ1
    s := D.s
    t := D.t
    hst := D.hst
    u := fun z => D.u (R z)
    Du := fun z => D.Du (R z)
    G := G'
    φ := D.φ
    hφ := D.hφ
    hφK := D.hφK
    hDum := fun i => (D.hDum i).comp hRmeas
    hGm := fun i => ((D.hGm i).comp hRmeas).neg
    hu2 := D.hu2.comp_measurePreserving hspaceTime
    hDu2 := fun i => (D.hDu2 i).comp_measurePreserving hspaceTime
    hG2 := fun i => ((D.hG2 i).comp_measurePreserving hspaceTime).neg
    hus := by
      intro τ hτ
      apply D.hus (D.s + D.t - τ)
      constructor
      · linarith [hτ.2]
      · linarith [hτ.1]
    hwg := by
      have hweakAE := htime.quasiMeasurePreserving.ae D.hwg
      filter_upwards [hweakAE] with τ hτ a' ha' haδ x hx i
      exact hτ a' ha' haδ x hx i
    hslice := by
      intro a' ha' haδ x hx τ1 τ2 h1 h12 h2
      let r1 : ℝ := D.s + D.t - τ1
      let r2 : ℝ := D.s + D.t - τ2
      have hr2 : D.s ≤ r2 := by dsimp [r2]; linarith [h2]
      have hr21 : r2 ≤ r1 := by dsimp [r2, r1]; linarith [h12]
      have hr1 : r1 ≤ D.t := by dsimp [r1]; linarith [h1]
      have hforward := D.hslice a' ha' haδ x hx r2 r1 hr2 hr21 hr1
      have hshift := time_reflection_preserving_collar_Ioc_shift D.K1
        D.K1_measurable (D.s + D.t) r2 r1
      let F : Vec d × ℝ → ℝ := fun z =>
        ∑ i, D.G z i * fderiv ℝ (kern a') (x - z.1) (basisVec i)
      let F' : Vec d × ℝ → ℝ := fun z =>
        ∑ i, G' z i * fderiv ℝ (kern a') (x - z.1) (basisVec i)
      have hchange :
          (∫ z in D.K1 ×ˢ Ioc τ1 τ2, F' z) =
            -∫ z in D.K1 ×ˢ Ioc r2 r1, F z := by
        have hcomp := hshift.integral_comp hEmb F'
        have hcompeq : (fun z => F' (R z)) = fun z => -F z := by
          funext z
          simp [F', F, G', R]
        rw [hcompeq] at hcomp
        rw [integral_neg] at hcomp
        have hτ1 : D.s + D.t - r1 = τ1 := by dsimp [r1]; ring
        have hτ2 : D.s + D.t - r2 = τ2 := by dsimp [r2]; ring
        rw [hτ1, hτ2] at hcomp
        exact hcomp.symm
      have hleft :
          (∫ y in D.K1, kern a' (x - y) * D.u (R (y, τ2))) -
            ∫ y in D.K1, kern a' (x - y) * D.u (R (y, τ1)) =
          -((∫ y in D.K1, kern a' (x - y) * D.u (y, r1)) -
            ∫ y in D.K1, kern a' (x - y) * D.u (y, r2)) := by
        simp only [R, r1, r2]
        ring
      rw [hleft, hforward, hchange]
  }

theorem reverseEnergyData_fields {d : ℕ} (D : Energy.Data d) (z : Vec d × ℝ) :
    (reverseEnergyData D).u z = D.u (z.1, D.s + D.t - z.2) ∧
    (reverseEnergyData D).Du z = D.Du (z.1, D.s + D.t - z.2) ∧
    (reverseEnergyData D).G z = -D.G (z.1, D.s + D.t - z.2) := by
  simp [reverseEnergyData]

end PDE.Parabolic.Duality
