module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.LionsRep.ScalarTraceAlgebra
public import EllipticRegularity.Parabolic.Cauchy.LionsRep.SmoothTestDensity
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-! # Continuous traces for arbitrary whole-space `L²` tests -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set Filter Topology

namespace PDE.Parabolic.LionsRep

noncomputable def smoothTestApprox {d : ℕ} (ψ : Vec d → ℝ)
    (hψ : MemLp ψ 2 volume) (n : ℕ) : Vec d → ℝ :=
  Classical.choose (exists_smooth_compact_test_approximation ψ hψ
    (show 0 < 1 / ((n : ℝ) + 1) by positivity))

theorem smoothTestApprox_spec {d : ℕ} (ψ : Vec d → ℝ)
    (hψ : MemLp ψ 2 volume) (n : ℕ) :
    HasCompactSupport (smoothTestApprox ψ hψ n) ∧
      ContDiff ℝ (⊤ : ℕ∞) (smoothTestApprox ψ hψ n) ∧
      eLpNorm (ψ - smoothTestApprox ψ hψ n) 2 volume ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
  Classical.choose_spec (exists_smooth_compact_test_approximation ψ hψ
    (show 0 < 1 / ((n : ℝ) + 1) by positivity))

/-- Any spatial `L²` test has a continuous scalar time trace, obtained by completing the traces
of smooth compactly supported approximants. -/
theorem exists_cauchy_scalarTrace_L2_extension
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
          (smoothTestApprox_spec ψ hψ n).1 t) atTop (𝓝 (v t))) := by
  let φ : ℕ → Vec d → ℝ := smoothTestApprox ψ hψ
  let hφc : ∀ n, HasCompactSupport (φ n) := fun n => (smoothTestApprox_spec ψ hψ n).1
  let hφ : ∀ n, ContDiff ℝ 1 (φ n) := fun n =>
    ((smoothTestApprox_spec ψ hψ n).2.1.of_le (by norm_num))
  let : CompactSpace (Icc s T) := isCompact_iff_compactSpace.mp isCompact_Icc
  let tr : ℕ → BoundedContinuousFunction (Icc s T) ℝ := fun n =>
    BoundedContinuousFunction.mkOfCompact
      (⟨fun t => cauchyScalarTrace hsT ha f hf u hrep (φ n) (hφ n) (hφc n) t,
        (cauchyScalarTrace_spec hsT ha f hf u hrep (φ n) (hφ n) (hφc n)).1.domRestrict⟩)
  let C : ℝ := Real.sqrt (cauchySliceEnergyBound (a := a) f u)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have htrDiff : ∀ n m (t : Icc s T),
      dist (tr n t) (tr m t) ≤ C * (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) := by
    intro n m t
    have ht : (t : ℝ) ∈ Icc s T := t.property
    change dist
      (cauchyScalarTrace hsT ha f hf u hrep (φ n) (hφ n) (hφc n) t)
      (cauchyScalarTrace hsT ha f hf u hrep (φ m) (hφ m) (hφc m) t) ≤ _
    have hsub := cauchyScalarTrace_sub hsT ha f hf u hrep (φ n) (φ m)
      (hφ n) (hφc n) (hφ m) (hφc m) t ht
    rw [Real.dist_eq, ← hsub]
    have hbound := cauchyScalarTrace_norm_bound hsT ha f hf u hclose hrep
      (φ n - φ m) ((hφ n).sub (hφ m)) ((hφc n).sub (hφc m)) t ht
    have hdiff : eLpNorm (φ n - φ m) 2 volume ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) +
          ENNReal.ofReal (1 / ((m : ℝ) + 1)) := by
      have hfun : (φ n - φ m) = (φ n - ψ) + (ψ - φ m) := by
        funext x
        simp only [Pi.sub_apply, Pi.add_apply]
        ring
      rw [hfun]
      calc
        eLpNorm ((φ n - ψ) + (ψ - φ m)) 2 volume ≤
            eLpNorm (φ n - ψ) 2 volume + eLpNorm (ψ - φ m) 2 volume :=
          eLpNorm_add_le (by norm_num)
        _ ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) +
              ENNReal.ofReal (1 / ((m : ℝ) + 1)) := by
          apply add_le_add
          · rw [eLpNorm_sub_comm]
            exact (smoothTestApprox_spec ψ hψ n).2.2
          · exact (smoothTestApprox_spec ψ hψ m).2.2
    have hdiffReal : (eLpNorm (φ n - φ m) 2 volume).toReal ≤
        1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1) := by
      have hsum : ENNReal.ofReal (1 / ((n : ℝ) + 1)) +
          ENNReal.ofReal (1 / ((m : ℝ) + 1)) =
          ENNReal.ofReal (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      have htop : eLpNorm (φ n - φ m) 2 volume ≤
          ENNReal.ofReal (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) := by
        exact hdiff.trans (by rw [hsum])
      have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top htop
      have hnonneg : 0 ≤ 1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1) := by positivity
      simpa only [ENNReal.toReal_ofReal hnonneg] using hreal
    calc
      |cauchyScalarTrace hsT ha f hf u hrep (φ n - φ m)
          ((hφ n).sub (hφ m)) ((hφc n).sub (hφc m)) t| ≤
          C * (eLpNorm (φ n - φ m) 2 volume).toReal := hbound
      _ ≤ C * (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hdiffReal hC
  have htrCauchy : CauchySeq tr := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    let δ : ℝ := ε / (2 * (C + 1))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hseq : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    rcases (eventually_atTop.1 (hseq.eventually (Iio_mem_nhds hδ))) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hsmalln : 1 / ((n : ℝ) + 1) < δ := hN n hn
    have hsmallN : 1 / ((N : ℝ) + 1) < δ := hN N le_rfl
    have hsum : 1 / ((n : ℝ) + 1) + 1 / ((N : ℝ) + 1) < 2 * δ := by linarith
    have hglobal : dist (tr n) (tr N) ≤ C *
        (1 / ((n : ℝ) + 1) + 1 / ((N : ℝ) + 1)) :=
      (BoundedContinuousFunction.dist_le (mul_nonneg hC (by positivity))).2
        (htrDiff n N)
    calc
      dist (tr n) (tr N) ≤ C *
          (1 / ((n : ℝ) + 1) + 1 / ((N : ℝ) + 1)) := hglobal
      _ < ε := by
        calc
          C * (1 / ((n : ℝ) + 1) + 1 / ((N : ℝ) + 1)) ≤ C * (2 * δ) :=
            mul_le_mul_of_nonneg_left hsum.le hC
          _ = ε * (C / (C + 1)) := by dsimp [δ]; field_simp
          _ < ε := by
            have hCden : 0 < C + 1 := by linarith
            have hfrac : C / (C + 1) < 1 := by
              rw [div_lt_one hCden]
              linarith
            calc
              ε * (C / (C + 1)) < ε * 1 := mul_lt_mul_of_pos_left hfrac hε
              _ = ε := by ring
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete htrCauchy
  refine ⟨v, v.continuous, ?_⟩
  intro t
  have hEval : Continuous (fun q : BoundedContinuousFunction (Icc s T) ℝ => q t) :=
    (BoundedContinuousFunction.lipschitz_eval_const t).continuous
  have hpoint : Tendsto (fun n => tr n t) atTop (𝓝 (v t)) :=
    hEval.continuousAt.tendsto.comp hv
  change Tendsto (fun n => cauchyScalarTrace hsT ha f hf u hrep
    (φ n) (hφ n) (hφc n) t) atTop (𝓝 (v t))
  exact hpoint

end PDE.Parabolic.LionsRep
