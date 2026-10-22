module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.Lions.PairingTrace
public import EllipticRegularity.Parabolic.Cauchy.Lions.ScalarPairingSliceBound

/-! # Algebra of continuous scalar traces -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.LionsRep

/-- The chosen continuous scalar representative attached to a smooth compactly supported test. -/
noncomputable def cauchyScalarTrace
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (ψ : Vec d → ℝ) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) : ℝ → ℝ :=
  Classical.choose (PDE.Parabolic.Lions.exists_cauchy_scalar_pairing_representative
    hsT ha f hf u hrep ψ hψ hψc)

/-- The chosen trace retains continuity, the almost-everywhere pairing identity, and the initial
value prescribed by the Lions formulation. -/
theorem cauchyScalarTrace_spec
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (ψ : Vec d → ℝ) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    ContinuousOn (cauchyScalarTrace hsT ha f hf u hrep ψ hψ hψc) (Icc s T) ∧
      PDE.Parabolic.Lions.cauchyValuePairing u ψ =ᵐ[volume.restrict (Icc s T)]
        cauchyScalarTrace hsT ha f hf u hrep ψ hψ hψc ∧
      cauchyScalarTrace hsT ha f hf u hrep ψ hψ hψc s = ∫ x, f x * ψ x := by
  rcases Classical.choose_spec
      (PDE.Parabolic.Lions.exists_cauchy_scalar_pairing_representative
        hsT ha f hf u hrep ψ hψ hψc) with ⟨hcont, hae, hinit, _⟩
  exact ⟨hcont, hae, hinit⟩

/-- Continuous scalar traces preserve addition of smooth compactly supported spatial tests. -/
theorem cauchyScalarTrace_add
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (ψ χ : Vec d → ℝ) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) :
    ∀ t ∈ Icc s T,
      cauchyScalarTrace hsT ha f hf u hrep (ψ + χ) (hψ.add hχ) (hψc.add hχc) t =
        cauchyScalarTrace hsT ha f hf u hrep ψ hψ hψc t +
          cauchyScalarTrace hsT ha f hf u hrep χ hχ hχc t := by
  have hsumSpec := cauchyScalarTrace_spec hsT ha f hf u hrep
    (ψ + χ) (hψ.add hχ) (hψc.add hχc)
  have hψSpec := cauchyScalarTrace_spec hsT ha f hf u hrep ψ hψ hψc
  have hχSpec := cauchyScalarTrace_spec hsT ha f hf u hrep χ hχ hχc
  have hψLp : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
  have hχLp : MemLp χ 2 volume := hχ.continuous.memLp_of_hasCompactSupport hχc
  have hrawAdd : PDE.Parabolic.Lions.cauchyValuePairing u (ψ + χ) =ᵐ[
      volume.restrict (Icc s T)] fun t =>
        PDE.Parabolic.Lions.cauchyValuePairing u ψ t +
          PDE.Parabolic.Lions.cauchyValuePairing u χ t := by
    filter_upwards [PDE.Parabolic.Lions.cauchyEnergyValue_ae_sliceMemLp u] with t ht
    have hψInt : Integrable
        (fun x : Vec d => PDE.Parabolic.Lions.cauchyEnergyValue u (x, t) * ψ x) volume :=
      ht.integrable_mul hψLp
    have hχInt : Integrable
        (fun x : Vec d => PDE.Parabolic.Lions.cauchyEnergyValue u (x, t) * χ x) volume :=
      ht.integrable_mul hχLp
    rw [PDE.Parabolic.Lions.cauchyValuePairing,
      PDE.Parabolic.Lions.cauchyValuePairing,
      PDE.Parabolic.Lions.cauchyValuePairing]
    calc
      (∫ x, PDE.Parabolic.Lions.cauchyEnergyValue u (x, t) * (ψ + χ) x) =
          ∫ x, (PDE.Parabolic.Lions.cauchyEnergyValue u (x, t) * ψ x) +
            (PDE.Parabolic.Lions.cauchyEnergyValue u (x, t) * χ x) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          simp only [Pi.add_apply]
          ring
      _ = (∫ x, PDE.Parabolic.Lions.cauchyEnergyValue u (x, t) * ψ x) +
            ∫ x, PDE.Parabolic.Lions.cauchyEnergyValue u (x, t) * χ x :=
        integral_add hψInt hχInt
  have htraceAe :
      (cauchyScalarTrace hsT ha f hf u hrep (ψ + χ) (hψ.add hχ) (hψc.add hχc)) =ᵐ[
        volume.restrict (Icc s T)]
        fun t => cauchyScalarTrace hsT ha f hf u hrep ψ hψ hψc t +
          cauchyScalarTrace hsT ha f hf u hrep χ hχ hχc t := by
    filter_upwards [hrawAdd, hsumSpec.2.1, hψSpec.2.1, hχSpec.2.1] with t hraw hs hψt hχt
    rw [← hs, hraw, hψt, hχt]
  have hleftCont := hsumSpec.1
  have hrightCont : ContinuousOn
      (fun t => cauchyScalarTrace hsT ha f hf u hrep ψ hψ hψc t +
        cauchyScalarTrace hsT ha f hf u hrep χ hχ hχc t) (Icc s T) :=
    hψSpec.1.add hχSpec.1
  have hEq := Measure.eqOn_Icc_of_ae_eq (volume : Measure ℝ) hsT.ne htraceAe
    hleftCont hrightCont
  intro t ht
  exact hEq ht

/-- Continuous scalar traces preserve real scalar multiplication of smooth compactly supported
spatial tests. -/
theorem cauchyScalarTrace_smul
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (c : ℝ) (ψ : Vec d → ℝ) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    ∀ t ∈ Icc s T,
      cauchyScalarTrace hsT ha f hf u hrep (c • ψ)
        (hψ.const_smul c) hψc.smul_left t =
      c * cauchyScalarTrace hsT ha f hf u hrep ψ hψ hψc t := by
  have hscaledSpec := cauchyScalarTrace_spec hsT ha f hf u hrep
    (c • ψ) (hψ.const_smul c) hψc.smul_left
  have hψSpec := cauchyScalarTrace_spec hsT ha f hf u hrep ψ hψ hψc
  have hrawSmul : PDE.Parabolic.Lions.cauchyValuePairing u (c • ψ) =ᵐ[
      volume.restrict (Icc s T)] fun t =>
        c * PDE.Parabolic.Lions.cauchyValuePairing u ψ t := by
    filter_upwards [PDE.Parabolic.Lions.cauchyEnergyValue_ae_sliceMemLp u] with t ht
    rw [PDE.Parabolic.Lions.cauchyValuePairing,
      PDE.Parabolic.Lions.cauchyValuePairing]
    calc
      (∫ x, PDE.Parabolic.Lions.cauchyEnergyValue u (x, t) * (c • ψ) x) =
          ∫ x, c * (PDE.Parabolic.Lions.cauchyEnergyValue u (x, t) * ψ x) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
      _ = c * ∫ x, PDE.Parabolic.Lions.cauchyEnergyValue u (x, t) * ψ x := by
        exact integral_const_mul c _
  have htraceAe :
      (cauchyScalarTrace hsT ha f hf u hrep (c • ψ)
        (hψ.const_smul c) hψc.smul_left) =ᵐ[volume.restrict (Icc s T)]
        fun t => c * cauchyScalarTrace hsT ha f hf u hrep ψ hψ hψc t := by
    filter_upwards [hrawSmul, hscaledSpec.2.1, hψSpec.2.1] with t hraw hs hψt
    rw [← hs, hraw, hψt]
  have hleftCont := hscaledSpec.1
  have hrightCont : ContinuousOn
      (fun t => c * cauchyScalarTrace hsT ha f hf u hrep ψ hψ hψc t) (Icc s T) :=
    continuousOn_const.mul hψSpec.1
  have hEq := Measure.eqOn_Icc_of_ae_eq (volume : Measure ℝ) hsT.ne htraceAe
    hleftCont hrightCont
  intro t ht
  exact hEq ht

/-- The chosen continuous scalar trace depends only on the spatial test function. -/
theorem cauchyScalarTrace_congr
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (ψ χ : Vec d → ℝ) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) (hEq : ψ = χ) :
    ∀ t ∈ Icc s T,
      cauchyScalarTrace hsT ha f hf u hrep ψ hψ hψc t =
        cauchyScalarTrace hsT ha f hf u hrep χ hχ hχc t := by
  have hψSpec := cauchyScalarTrace_spec hsT ha f hf u hrep ψ hψ hψc
  have hχSpec := cauchyScalarTrace_spec hsT ha f hf u hrep χ hχ hχc
  have hraw : PDE.Parabolic.Lions.cauchyValuePairing u ψ =ᵐ[
      volume.restrict (Icc s T)] PDE.Parabolic.Lions.cauchyValuePairing u χ := by
    subst hEq
    exact Filter.Eventually.of_forall fun _ => rfl
  have htraces : cauchyScalarTrace hsT ha f hf u hrep ψ hψ hψc =ᵐ[
      volume.restrict (Icc s T)]
        cauchyScalarTrace hsT ha f hf u hrep χ hχ hχc := by
    filter_upwards [hraw, hψSpec.2.1, hχSpec.2.1] with t hpair hψt hχt
    rw [← hψt, hpair, hχt]
  have hEqOn := Measure.eqOn_Icc_of_ae_eq (volume : Measure ℝ) hsT.ne htraces
    hψSpec.1 hχSpec.1
  intro t ht
  exact hEqOn ht

/-- Continuous scalar traces preserve subtraction of smooth compactly supported tests. -/
theorem cauchyScalarTrace_sub
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (ψ χ : Vec d → ℝ) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) :
    ∀ t ∈ Icc s T,
      cauchyScalarTrace hsT ha f hf u hrep (ψ - χ) (hψ.sub hχ)
        (hψc.sub hχc) t =
      cauchyScalarTrace hsT ha f hf u hrep ψ hψ hψc t -
        cauchyScalarTrace hsT ha f hf u hrep χ hχ hχc t := by
  intro t ht
  have hχSmulNeg : ContDiff ℝ 1 ((-1 : ℝ) • χ) := by
    convert hχ.const_smul (-1) using 1
    funext x
    simp
  have hχcSmulNeg : HasCompactSupport ((-1 : ℝ) • χ) := by
    convert hχc.smul_left using 1
  have hAdd := cauchyScalarTrace_add hsT ha f hf u hrep ψ ((-1 : ℝ) • χ)
    hψ hψc hχSmulNeg hχcSmulNeg t ht
  have hNeg := cauchyScalarTrace_smul hsT ha f hf u hrep (-1) χ hχ hχc t ht
  have hCong := cauchyScalarTrace_congr hsT ha f hf u hrep (ψ - χ)
    (ψ + ((-1 : ℝ) • χ)) (hψ.sub hχ) (hψc.sub hχc)
    (hψ.add hχSmulNeg) (hψc.add hχcSmulNeg)
    (by funext x; simp; ring) t ht
  rw [hCong, hAdd, hNeg]
  ring

/-- The chosen scalar trace inherits the scale-independent global spatial slice bound. The only
input for this bound is the almost-every-time estimate for the unmollified Lions field. -/
theorem cauchyScalarTrace_norm_bound
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (ψ : Vec d → ℝ) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    ∀ t ∈ Icc s T,
      |cauchyScalarTrace hsT ha f hf u hrep ψ hψ hψc t| ≤
        Real.sqrt (PDE.Parabolic.LionsRep.cauchySliceEnergyBound (a := a) f u) *
          (eLpNorm ψ 2 volume).toReal := by
  obtain ⟨v, hvcont, hvae, _hvinit, hbound⟩ :=
    PDE.Parabolic.Lions.exists_cauchy_scalar_pairing_sliceNorm_bound
      hsT ha f hf u hclose hrep ψ hψ hψc
  have hspec := cauchyScalarTrace_spec hsT ha f hf u hrep ψ hψ hψc
  have htrace : cauchyScalarTrace hsT ha f hf u hrep ψ hψ hψc =ᵐ[
      volume.restrict (Icc s T)] v := hspec.2.1.symm.trans hvae
  have hEq := Measure.eqOn_Icc_of_ae_eq (volume : Measure ℝ) hsT.ne htrace
    hspec.1 hvcont
  intro t ht
  rw [hEq ht]
  exact hbound t ht

end PDE.Parabolic.LionsRep
