module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.LionsRep.TimeSlice

/-! # Weak continuity of the all-time `L²` slices -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace PDE.Parabolic.LionsRep

noncomputable def smoothApproxSubmodule {d : ℕ} (ψ : Vec d → ℝ)
    (hψ : MemLp ψ 2 volume) (n : ℕ) : smoothCompactSubmodule d :=
  ⟨smoothTestApprox ψ hψ n, (smoothTestApprox_spec ψ hψ n).1,
    ((smoothTestApprox_spec ψ hψ n).2.1.of_le (by norm_num))⟩

private theorem smoothApproxSubmodule_memLp {d : ℕ} (ψ : Vec d → ℝ)
    (hψ : MemLp ψ 2 volume) (n : ℕ) :
    MemLp (smoothTestApprox ψ hψ n) 2 (volume : Measure (Vec d)) := by
  have hspec : HasCompactSupport (smoothTestApprox ψ hψ n) ∧
      ContDiff ℝ 1 (smoothTestApprox ψ hψ n) :=
    ⟨(smoothTestApprox_spec ψ hψ n).1,
      (smoothTestApprox_spec ψ hψ n).2.1.of_le (by norm_num)⟩
  exact hspec.2.continuous.memLp_of_hasCompactSupport hspec.1

private theorem smoothApprox_Lp_tendsto {d : ℕ} (ψ : Vec d → ℝ)
    (hψ : MemLp ψ 2 volume) :
    Tendsto (fun n => smoothCompactEmbedding d (smoothApproxSubmodule ψ hψ n)) atTop
      (𝓝 (hψ.toLp ψ)) := by
  let φ : ℕ → Vec d → ℝ := smoothTestApprox ψ hψ
  let hφLp : ∀ n, MemLp (φ n) 2 volume := fun n =>
    smoothApproxSubmodule_memLp ψ hψ n
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
  have hTendsto :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (p := 2) φ hφLp ψ hψ).2 hErr
  convert hTendsto using 1; rfl

/-- Every whole-space `L²` test has a continuous pairing with the Riesz time slices; at the
initial endpoint this pairing is the datum pairing. -/
theorem exists_cauchyL2TimeSlice_pairing_continuous_initial
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (ψ : Vec d → ℝ) (hψ : MemLp ψ 2 volume) :
    ∃ v : Icc s T → ℝ, Continuous v ∧
      (∀ t : Icc s T,
        inner ℝ (cauchyL2TimeSlice hsT ha f hf u hclose hrep t) (hψ.toLp ψ) = v t) ∧
      v ⟨s, ⟨le_rfl, hsT.le⟩⟩ = ∫ x, f x * ψ x ∧
      PDE.Parabolic.Lions.cauchyValuePairing u ψ =ᵐ[
        volume.restrict (Icc s T)] (fun t =>
          if ht : t ∈ Icc s T then v ⟨t, ht⟩ else 0) := by
  obtain ⟨v, hvcont, hvlim, hraw⟩ :=
    exists_cauchy_scalarTrace_L2_extension_pairing hsT ha f hf u hclose hrep ψ hψ
  have hLpTendsto := smoothApprox_Lp_tendsto ψ hψ
  let φ : ℕ → Vec d → ℝ := smoothTestApprox ψ hψ
  let hφc : ∀ n, HasCompactSupport (φ n) := fun n =>
    (smoothTestApprox_spec ψ hψ n).1
  let hφ : ∀ n, ContDiff ℝ 1 (φ n) := fun n =>
    ((smoothTestApprox_spec ψ hψ n).2.1.of_le (by norm_num))
  let hφLp : ∀ n, MemLp (φ n) 2 volume := fun n =>
    smoothApproxSubmodule_memLp ψ hψ n
  have hPairingContinuous (t : Icc s T) :
      Continuous (fun q : Lp ℝ 2 volume =>
        inner ℝ (cauchyL2TimeSlice hsT ha f hf u hclose hrep t) q) := by
    exact (innerSL ℝ (cauchyL2TimeSlice hsT ha f hf u hclose hrep t)).continuous
  have hPairingLimit (t : Icc s T) :
      Tendsto (fun n => inner ℝ
        (cauchyL2TimeSlice hsT ha f hf u hclose hrep t)
        (smoothCompactEmbedding d (smoothApproxSubmodule ψ hψ n))) atTop
        (𝓝 (inner ℝ (cauchyL2TimeSlice hsT ha f hf u hclose hrep t)
          (hψ.toLp ψ))) := by
    exact (hPairingContinuous t).continuousAt.tendsto.comp hLpTendsto
  have hTracePairing (t : Icc s T) (n : ℕ) :
      inner ℝ (cauchyL2TimeSlice hsT ha f hf u hclose hrep t)
        (smoothCompactEmbedding d (smoothApproxSubmodule ψ hψ n)) =
      cauchyScalarTrace hsT ha f hf u hrep (φ n) (hφ n) (hφc n) t := by
    exact cauchyL2TimeSlice_pairing_smooth hsT ha f hf u hclose hrep t
      (smoothApproxSubmodule ψ hψ n)
  have hTraceAtInitial : Tendsto
      (fun n => cauchyScalarTrace hsT ha f hf u hrep (φ n) (hφ n) (hφc n) s)
      atTop (𝓝 (∫ x, f x * ψ x)) := by
    let fLp : Lp ℝ 2 volume := hf.toLp f
    have hIntegralContinuous : Continuous (fun q : Lp ℝ 2 volume => inner ℝ fLp q) :=
      (innerSL ℝ fLp).continuous
    have hIntegralPair (χ : Vec d → ℝ) (hχ : MemLp χ 2 volume) :
        (∫ x, f x * χ x) = inner ℝ fLp (hχ.toLp χ) := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp, hχ.coeFn_toLp] with x hfx hχx
      rw [hfx, hχx]
      simp only [Real.inner_apply]
    have hIntegralApprox : Tendsto
        (fun n => ∫ x, f x * (φ n) x) atTop (𝓝 (∫ x, f x * ψ x)) := by
      have hEval : Tendsto
          (fun n => inner ℝ fLp ((hφLp n).toLp (φ n))) atTop
          (𝓝 (inner ℝ fLp (hψ.toLp ψ))) :=
        hIntegralContinuous.continuousAt.tendsto.comp hLpTendsto
      have hEq : (fun n => inner ℝ fLp ((hφLp n).toLp (φ n))) =ᶠ[atTop]
          fun n => ∫ x, f x * (φ n) x :=
        Filter.Eventually.of_forall fun n => (hIntegralPair (φ n) (hφLp n)).symm
      have hEval' := hEval.congr' hEq
      simpa [hIntegralPair ψ hψ] using hEval'
    have hEq : (fun n => cauchyScalarTrace hsT ha f hf u hrep
        (φ n) (hφ n) (hφc n) s) =ᶠ[atTop]
        fun n => ∫ x, f x * (φ n) x := by
      filter_upwards [Filter.Eventually.of_forall fun n =>
        (cauchyScalarTrace_spec hsT ha f hf u hrep (φ n) (hφ n) (hφc n)).2.2] with n hn
      exact hn
    exact hIntegralApprox.congr' hEq.symm
  have hAllT (t : Icc s T) :
      inner ℝ (cauchyL2TimeSlice hsT ha f hf u hclose hrep t) (hψ.toLp ψ) = v t := by
    have hleft := hPairingLimit t
    have hright := hvlim t
    have hEqSeq : (fun n => inner ℝ
        (cauchyL2TimeSlice hsT ha f hf u hclose hrep t)
        (smoothCompactEmbedding d (smoothApproxSubmodule ψ hψ n))) =ᶠ[atTop]
        fun n => cauchyScalarTrace hsT ha f hf u hrep (φ n) (hφ n) (hφc n) t :=
      Filter.Eventually.of_forall fun n => hTracePairing t n
    have hleft' := hleft.congr' hEqSeq
    exact tendsto_nhds_unique hleft' hright
  let ts : Icc s T := ⟨s, ⟨le_rfl, hsT.le⟩⟩
  have hinit : v ts = ∫ x, f x * ψ x := by
    have hleft := hvlim ts
    have hright := hTraceAtInitial
    simpa [ts, φ, hφ, hφc] using tendsto_nhds_unique hleft hright
  exact ⟨v, hvcont, hAllT, hinit, hraw⟩

end PDE.Parabolic.LionsRep
