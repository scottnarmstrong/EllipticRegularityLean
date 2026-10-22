module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.LionsRep.ScalarTraceExtension
public import EllipticRegularity.Parabolic.Cauchy.Lions.PairingLp

/-! # Identify the completed scalar trace with the raw spatial pairing -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology
open scoped ENNReal

namespace PDE.Parabolic.LionsRep

/-- The continuous trace obtained by completing smooth spatial tests agrees almost everywhere
with the raw Lions pairing for the original `L²` test. -/
theorem exists_cauchy_scalarTrace_L2_extension_pairing
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (ψ : Vec d → ℝ) (hψ : MemLp ψ 2 volume) :
    ∃ v : Icc s T → ℝ, Continuous v ∧
      (∀ t : Icc s T,
        Tendsto (fun n => cauchyScalarTrace hsT ha f hf u hrep
          (smoothTestApprox ψ hψ n)
          ((smoothTestApprox_spec ψ hψ n).2.1.of_le (by norm_num))
          (smoothTestApprox_spec ψ hψ n).1 t) atTop (𝓝 (v t))) ∧
      PDE.Parabolic.Lions.cauchyValuePairing u ψ =ᵐ[
        volume.restrict (Icc s T)] (fun t =>
          if ht : t ∈ Icc s T then v ⟨t, ht⟩ else 0) := by
  obtain ⟨v, hvcont, hvlim⟩ := exists_cauchy_scalarTrace_L2_extension
    hsT ha f hf u hclose hrep ψ hψ
  let vfun : ℝ → ℝ := fun t => if ht : t ∈ Icc s T then v ⟨t, ht⟩ else 0
  let φ : ℕ → Vec d → ℝ := smoothTestApprox ψ hψ
  let hφc : ∀ n, HasCompactSupport (φ n) := fun n => (smoothTestApprox_spec ψ hψ n).1
  let hφ : ∀ n, ContDiff ℝ 1 (φ n) := fun n =>
    ((smoothTestApprox_spec ψ hψ n).2.1.of_le (by norm_num))
  let hφLp : ∀ n, MemLp (φ n) 2 volume := fun n =>
    (hφ n).continuous.memLp_of_hasCompactSupport (hφc n)
  have hErr : Tendsto (fun n => eLpNorm (φ n - ψ) 2 volume) atTop (𝓝 0) := by
    have hsmall : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1)))
        atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsmall
      (fun _ => bot_le) ?_
    intro n
    change eLpNorm (φ n - ψ) 2 volume ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1))
    rw [eLpNorm_sub_comm]
    exact (smoothTestApprox_spec ψ hψ n).2.2
  have hLpTendsto : Tendsto (fun n => (hφLp n).toLp (φ n)) atTop
      (𝓝 (hψ.toLp ψ)) := by
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (p := 2) φ hφLp ψ hψ).2 hErr
  let rawPair : ℕ → ℝ → ℝ := fun n t =>
    cauchyScalarTrace hsT ha f hf u hrep (φ n) (hφ n) (hφc n) t
  have hrawAE : ∀ n,
      PDE.Parabolic.Lions.cauchyValuePairing u (φ n) =ᵐ[
        volume.restrict (Icc s T)] fun t => rawPair n t := by
    intro n
    exact (cauchyScalarTrace_spec hsT ha f hf u hrep (φ n) (hφ n) (hφc n)).2.1
  have hrawAll : ∀ᵐ t ∂(volume.restrict (Icc s T)),
      ∀ n, PDE.Parabolic.Lions.cauchyValuePairing u (φ n) t = rawPair n t := by
    exact ae_all_iff.2 hrawAE
  have hslice := PDE.Parabolic.Lions.cauchyEnergyValue_ae_sliceMemLp u
  have hmain : ∀ᵐ t ∂(volume.restrict (Icc s T)),
      PDE.Parabolic.Lions.cauchyValuePairing u ψ t = vfun t := by
    filter_upwards [hslice, hrawAll, ae_restrict_mem measurableSet_Icc] with t hslice hraw htI
    let g : Vec d → ℝ := fun x => PDE.Parabolic.Lions.cauchyEnergyValue u (x, t)
    let gLp : Lp ℝ 2 volume := hslice.toLp g
    have hpair (χ : Vec d → ℝ) (hχ : MemLp χ 2 volume) :
        PDE.Parabolic.Lions.cauchyValuePairing u χ t = inner ℝ gLp (hχ.toLp χ) := by
      rw [PDE.Parabolic.Lions.cauchyValuePairing, MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hχ.coeFn_toLp, hslice.coeFn_toLp] with x hχx hgx
      rw [hχx, hgx]
      change g x * χ x = χ x * g x
      ring
    have hLcont : Continuous (fun q : Lp ℝ 2 volume => inner ℝ gLp q) := by
      exact (innerSL ℝ gLp).continuous
    have hpairTendsto : Tendsto
        (fun n => PDE.Parabolic.Lions.cauchyValuePairing u (φ n) t) atTop
        (𝓝 (PDE.Parabolic.Lions.cauchyValuePairing u ψ t)) := by
      have hEval : Tendsto (fun n => inner ℝ gLp ((hφLp n).toLp (φ n))) atTop
          (𝓝 (inner ℝ gLp (hψ.toLp ψ))) :=
        hLcont.continuousAt.tendsto.comp hLpTendsto
      have hEq : (fun n => PDE.Parabolic.Lions.cauchyValuePairing u (φ n) t) =
          fun n => inner ℝ gLp ((hφLp n).toLp (φ n)) := by
        funext n
        exact hpair (φ n) (hφLp n)
      have hEq' : (fun n => inner ℝ gLp ((hφLp n).toLp (φ n))) =ᶠ[atTop]
          fun n => PDE.Parabolic.Lions.cauchyValuePairing u (φ n) t :=
        Filter.Eventually.of_forall fun n => (congrFun hEq n).symm
      have hpairTendsto' := hEval.congr' hEq'
      simpa [hpair ψ hψ] using hpairTendsto'
    have htraceTendsto : Tendsto (fun n => rawPair n t) atTop
        (𝓝 (v ⟨t, htI⟩)) := by
      simpa [rawPair] using hvlim ⟨t, htI⟩
    have hEqSeq : (fun n => PDE.Parabolic.Lions.cauchyValuePairing u (φ n) t) =ᶠ[atTop]
        fun n => rawPair n t := by
      filter_upwards [Filter.Eventually.of_forall hraw] with n hn
      exact hn
    have hpairTendsto' := hpairTendsto.congr' hEqSeq
    have hval := tendsto_nhds_unique hpairTendsto' htraceTendsto
    have hfun : vfun t = v ⟨t, htI⟩ := by
      dsimp [vfun]
      exact dite_eq_left htI
    rw [hfun]
    exact hval
  refine ⟨v, hvcont, hvlim, ?_⟩
  filter_upwards [hmain, ae_restrict_mem measurableSet_Icc] with t ht htI
  rw [dite_eq_left htI]
  have hfun : vfun t = v ⟨t, htI⟩ := by
    dsimp [vfun]
    exact dite_eq_left htI
  rw [← hfun]
  exact ht

/-- The completed trace for an arbitrary spatial `L²` test has the datum as its initial pairing.
Together with `exists_cauchy_scalarTrace_L2_extension_pairing`, this gives both raw-pairing
identification almost everywhere and the prescribed endpoint value. -/
theorem exists_cauchy_scalarTrace_L2_extension_initial
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (ψ : Vec d → ℝ) (hψ : MemLp ψ 2 volume) :
    ∃ v : Icc s T → ℝ, Continuous v ∧
      PDE.Parabolic.Lions.cauchyValuePairing u ψ =ᵐ[
        volume.restrict (Icc s T)]
          (fun t => if ht : t ∈ Icc s T then v ⟨t, ht⟩ else 0) ∧
      v ⟨s, ⟨le_rfl, hsT.le⟩⟩ = ∫ x, f x * ψ x := by
  obtain ⟨v, hvcont, hvlim, hpairAE⟩ :=
    exists_cauchy_scalarTrace_L2_extension_pairing hsT ha f hf u hclose hrep ψ hψ
  let φ : ℕ → Vec d → ℝ := smoothTestApprox ψ hψ
  let hφc : ∀ n, HasCompactSupport (φ n) := fun n => (smoothTestApprox_spec ψ hψ n).1
  let hφ : ∀ n, ContDiff ℝ 1 (φ n) := fun n =>
    ((smoothTestApprox_spec ψ hψ n).2.1.of_le (by norm_num))
  let hφLp : ∀ n, MemLp (φ n) 2 volume := fun n =>
    (hφ n).continuous.memLp_of_hasCompactSupport (hφc n)
  have hErr : Tendsto (fun n => eLpNorm (φ n - ψ) 2 volume) atTop (𝓝 0) := by
    have hsmall : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1)))
        atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsmall
      (fun _ => bot_le) ?_
    intro n
    change eLpNorm (φ n - ψ) 2 volume ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1))
    rw [eLpNorm_sub_comm]
    exact (smoothTestApprox_spec ψ hψ n).2.2
  have hLpTendsto : Tendsto (fun n => (hφLp n).toLp (φ n)) atTop
      (𝓝 (hψ.toLp ψ)) := by
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (p := 2) φ hφLp ψ hψ).2 hErr
  let fLp : Lp ℝ 2 volume := hf.toLp f
  have hLcont : Continuous (fun q : Lp ℝ 2 volume => inner ℝ fLp q) := by
    exact (innerSL ℝ fLp).continuous
  have hpair (χ : Vec d → ℝ) (hχ : MemLp χ 2 volume) :
      (∫ x, f x * χ x) = inner ℝ fLp (hχ.toLp χ) := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hχ.coeFn_toLp] with x hfx hχx
    rw [hfx, hχx]
    simp only [Real.inner_apply]
  have hinitTendsto : Tendsto (fun n => ∫ x, f x * (φ n) x) atTop
      (𝓝 (∫ x, f x * ψ x)) := by
    have hEval : Tendsto (fun n => inner ℝ fLp ((hφLp n).toLp (φ n))) atTop
        (𝓝 (inner ℝ fLp (hψ.toLp ψ))) :=
      hLcont.continuousAt.tendsto.comp hLpTendsto
    have hEq : (fun n => inner ℝ fLp ((hφLp n).toLp (φ n))) =ᶠ[atTop]
        fun n => ∫ x, f x * (φ n) x :=
      Filter.Eventually.of_forall fun n => (hpair (φ n) (hφLp n)).symm
    have hEval' := hEval.congr' hEq
    simpa [hpair ψ hψ] using hEval'
  let ts : Icc s T := ⟨s, ⟨le_rfl, hsT.le⟩⟩
  have htraceTendsto : Tendsto (fun n => cauchyScalarTrace hsT ha f hf u hrep
      (φ n) (hφ n) (hφc n) s) atTop (𝓝 (v ts)) := by
    simpa [ts, φ, hφ, hφc] using hvlim ts
  have htraceEq : (fun n => cauchyScalarTrace hsT ha f hf u hrep
      (φ n) (hφ n) (hφc n) s) =ᶠ[atTop] fun n => ∫ x, f x * (φ n) x :=
    Filter.Eventually.of_forall fun n =>
      (cauchyScalarTrace_spec hsT ha f hf u hrep (φ n) (hφ n) (hφc n)).2.2
  have htraceTendsto' := htraceTendsto.congr' htraceEq
  have hinit := tendsto_nhds_unique htraceTendsto' hinitTendsto
  refine ⟨v, hvcont, hpairAE, ?_⟩
  simpa [ts] using hinit

end PDE.Parabolic.LionsRep
