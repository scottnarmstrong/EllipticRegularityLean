module

public import EllipticRegularity.Parabolic.Cauchy.Lions.WeakFormTransfer
public import EllipticRegularity.Parabolic.Cauchy.LionsBound.GlobalSliceBound

/-! # Conditional final assembly of the whole-space Cauchy solution -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.Lions

/-- The uniform global spatial `L²` slice bound supplied by the Lions bound. -/
abbrev CauchyGlobalSliceBound {d : ℕ} {s T : ℝ} {a : ParCoeffField d}
    (f : Vec d → ℝ) (u : CauchyX d s T) : Prop :=
  ∀ᵐ t ∂(volume.restrict (Icc s T)),
    MemLp (fun x : Vec d => cauchyEnergyValue u (x, t)) 2
        (volume : Measure (Vec d)) ∧
      eLpNorm (fun x : Vec d => cauchyEnergyValue u (x, t)) 2 volume ≤
        ENNReal.ofReal (Real.sqrt
          (PDE.Parabolic.LionsRep.cauchySliceEnergyBound (a := a) f u))

/-- The Lions construction and global slice bound yield a Cauchy energy solution provided the
representative step supplies a `ParH1Function` agreeing almost everywhere with both raw energy
fields. This isolates the sole remaining representative-construction input. -/
theorem exists_cauchy_energy_solution_of_representative_hypothesis
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 (volume : Measure (Vec d)))
    (hBuildRepresentative :
      ∀ (u : CauchyX d s T) {u₀ : CauchyY d},
      ∀ (_hclose : WithLp.toLp 2 (u, u₀) ∈
          (LinearMap.range (initialTraceMap (cauchyJ (d := d) (s := s) (T := T))
            (cauchyGamma (d := d) (s := s) (T := T)))).topologicalClosure),
      ∀ (_hrep : ∀ φ : CauchyTestSpace d s T,
          inner ℝ u (cauchyT (c := 1) ha φ) =
            inner ℝ (hf.toLp f) (cauchyGamma φ)),
      ∀ (_hglobalSliceBound : CauchyGlobalSliceBound (a := a) f u),
        ∃ W : ParH1Function (univ : Set (Vec d)) (Icc s T),
          W.toFun =ᵐ[slabMeasure d s T] cauchyEnergyValue u ∧
          ∀ i : Fin d, (fun z => W.grad z i) =ᵐ[slabMeasure d s T]
            (fun z => cauchyEnergyGradient u z i)) :
    ∃ W : ParH1Function (univ : Set (Vec d)) (Icc s T),
      IsCauchySolution a s T f W := by
  obtain ⟨u, u₀, hclose, hrep, _, _, _, _⟩ :=
    exists_cauchy_lions_energyFields hsT ha f hf
  have hglobalSliceBound : CauchyGlobalSliceBound (a := a) f u :=
    cauchyEnergyValue_ae_slice_norm_bound hsT ha f hf u hclose hrep
  obtain ⟨W, hWae, hGae⟩ :=
    hBuildRepresentative u hclose hrep hglobalSliceBound
  exact ⟨W, cauchyEnergyRepresentative_isCauchySolution
    hsT ha f hf u hclose hrep W hWae hGae⟩

end PDE.Parabolic.Lions
