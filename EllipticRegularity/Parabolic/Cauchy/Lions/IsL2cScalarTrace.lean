/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.Lions.ScalarPairingSliceBound
public import PDEFoundation.Sobolev.Inequalities.SobolevWholeSpaceMollify
public import Mathlib.Topology.ContinuousMap.Compact

/-! # Scalar traces for compactly supported `L²` tests -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set Filter
open Convolution
open scoped ENNReal Topology Convolution

namespace PDE.Parabolic.Lions

/-- Every compactly supported spatial `L²` test has a continuous scalar pairing trace on the
closed time interval. The trace agrees almost everywhere with the raw Lions pairing and has the
initial value prescribed by the datum. The proof approximates the test by spatial mollifications;
the uniform-in-time estimate comes from the global slice bound. -/
theorem exists_cauchy_scalar_pairing_representative_of_isL2c
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 (volume : Measure (Vec d)))
    (u : CauchyX d s T) {u₀ : CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (ψ : Vec d → ℝ) (hψ : IsL2c (univ : Set (Vec d)) ψ) :
    ∃ v : ℝ → ℝ, ContinuousOn v (Icc s T) ∧
      cauchyValuePairing u ψ =ᵐ[volume.restrict (Icc s T)] v ∧
      v s = ∫ x, f x * ψ x := by
  rcases hψ with ⟨hψL2, K, hK, _hKU, hψ0⟩
  have hψLp : MemLp ψ 2 (volume : Measure (Vec d)) := by
    simpa [PDE.MemL2On, PDE.MemLpOn, PDE.volumeOn, Measure.restrict_univ] using hψL2
  have hψcompact : HasCompactSupport ψ := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    intro x hx
    by_contra hxK
    have hxne : ψ x ≠ 0 := by simpa [Function.mem_support] using hx
    exact hxne (hψ0 x hxK)
  let ε : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  let ψε : ℕ → Vec d → ℝ := fun n => PDE.wholeSpaceMollify (ε n) ψ
  have hεpos : ∀ n, 0 < ε n := by
    intro n
    dsimp [ε]
    positivity
  have hεle : ∀ n, ε n ≤ 1 := by
    intro n
    dsimp [ε]
    apply (inv_le_one₀ (by positivity)).2
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith
  have hεtendsto : Tendsto ε atTop (𝓝 0) := by
    simpa [ε, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hψεcont : ∀ n, ContDiff ℝ 1 (ψε n) := by
    intro n
    dsimp [ψε]
    have hψloc : LocallyIntegrable ψ (volume : Measure (Vec d)) :=
      hψLp.locallyIntegrable (by norm_num)
    exact (PDE.Parabolic.Energy.moll_contDiff (hεpos n) hψloc).of_le
      (by exact_mod_cast le_top)
  have hψεcompact : ∀ n, HasCompactSupport (ψε n) := by
    intro n
    dsimp [ψε]
    change HasCompactSupport
      (PDE.Parabolic.Energy.kern (ε n) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        (volume : Measure (Vec d))] ψ)
    exact (PDE.Parabolic.Energy.kern_hasCompactSupport (hεpos n)).convolution
      (ContinuousLinearMap.lsmul ℝ ℝ) hψcompact
  have hψεLp : ∀ n, MemLp (ψε n) 2 (volume : Measure (Vec d)) := by
    intro n
    exact (hψεcont n).continuous.memLp_of_hasCompactSupport (hψεcompact n)
  have hεconv : Tendsto
      (fun n => eLpNorm (ψε n - ψ) 2 (volume : Measure (Vec d))) atTop (𝓝 0) := by
    simpa only [ψε] using
      PDE.tendsto_eLpNorm_wholeSpaceMollify_sub (p := 2) (by norm_num) (by norm_num)
        hψLp (a := ε) hεpos hεle hεtendsto
  have hεfinite : ∀ n, eLpNorm (ψε n - ψ) 2 (volume : Measure (Vec d)) ≠ ∞ := by
    intro n
    exact ((hψεLp n).sub hψLp).eLpNorm_ne_top
  have hεreal : Tendsto
      (fun n => (eLpNorm (ψε n - ψ) 2 (volume : Measure (Vec d))).toReal)
      atTop (𝓝 0) := (ENNReal.tendsto_toReal_zero_iff hεfinite).2 hεconv
  let hψεtoLp : ∀ n, Lp ℝ 2 (volume : Measure (Vec d)) := fun n =>
    (hψεLp n).toLp (ψε n)
  let hψtoLp : Lp ℝ 2 (volume : Measure (Vec d)) := hψLp.toLp ψ
  let trace : ℕ → ℝ → ℝ := fun n =>
    Classical.choose (PDE.Parabolic.Lions.exists_cauchy_scalar_pairing_representative
      hsT ha f hf u hrep (ψε n) (hψεcont n) (hψεcompact n))
  have htraceCont : ∀ n, ContinuousOn (trace n) (Icc s T) := by
    intro n
    exact (Classical.choose_spec (PDE.Parabolic.Lions.exists_cauchy_scalar_pairing_representative
      hsT ha f hf u hrep (ψε n) (hψεcont n) (hψεcompact n))).1
  have htraceAE : ∀ n,
      cauchyValuePairing u (ψε n) =ᵐ[volume.restrict (Icc s T)] trace n := by
    intro n
    exact (Classical.choose_spec (PDE.Parabolic.Lions.exists_cauchy_scalar_pairing_representative
      hsT ha f hf u hrep (ψε n) (hψεcont n) (hψεcompact n))).2.1
  let traceDiff (n m : ℕ) : ℝ → ℝ :=
    Classical.choose (exists_cauchy_scalar_pairing_sliceNorm_bound hsT ha f hf u
      hclose hrep (ψε n - ψε m) ((hψεcont n).sub (hψεcont m))
      ((hψεcompact n).sub (hψεcompact m)))
  have htraceDiffSpec (n m : ℕ) :
      ContinuousOn (traceDiff n m) (Icc s T) ∧
        cauchyValuePairing u (ψε n - ψε m) =ᵐ[volume.restrict (Icc s T)]
          traceDiff n m ∧
        traceDiff n m s = ∫ x, f x * (ψε n - ψε m) x ∧
        ∀ t ∈ Icc s T,
          |traceDiff n m t| ≤ Real.sqrt
            (PDE.Parabolic.LionsRep.cauchySliceEnergyBound (a := a) f u) *
              (eLpNorm (ψε n - ψε m) 2 volume).toReal :=
    Classical.choose_spec (exists_cauchy_scalar_pairing_sliceNorm_bound hsT ha f hf u
      hclose hrep (ψε n - ψε m) ((hψεcont n).sub (hψεcont m))
      ((hψεcompact n).sub (hψεcompact m)))
  have hrawSub (n m : ℕ) :
      cauchyValuePairing u (ψε n - ψε m) =ᵐ[volume.restrict (Icc s T)]
        fun t => cauchyValuePairing u (ψε n) t - cauchyValuePairing u (ψε m) t := by
    have hrawSlice := cauchyEnergyValue_ae_sliceMemLp u
    filter_upwards [hrawSlice] with t ht
    have hIn : Integrable
        (fun x : Vec d => cauchyEnergyValue u (x, t) * ψε n x) volume :=
      ht.integrable_mul (hψεLp n)
    have hIm : Integrable
        (fun x : Vec d => cauchyEnergyValue u (x, t) * ψε m x) volume :=
      ht.integrable_mul (hψεLp m)
    rw [cauchyValuePairing, cauchyValuePairing, cauchyValuePairing]
    calc
      (∫ x, cauchyEnergyValue u (x, t) * (ψε n - ψε m) x) =
          ∫ x, (cauchyEnergyValue u (x, t) * ψε n x) -
            (cauchyEnergyValue u (x, t) * ψε m x) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          simp only [Pi.sub_apply]
          ring
      _ = (∫ x, cauchyEnergyValue u (x, t) * ψε n x) -
            ∫ x, cauchyEnergyValue u (x, t) * ψε m x := integral_sub hIn hIm
  have htraceDiffEq : ∀ n m, ∀ t ∈ Icc s T,
      trace n t - trace m t = traceDiff n m t := by
    intro n m t ht
    have hae : traceDiff n m =ᵐ[volume.restrict (Icc s T)]
        fun τ => trace n τ - trace m τ := by
      filter_upwards [htraceDiffSpec n m |>.2.1, hrawSub n m,
        htraceAE n, htraceAE m] with τ hdiff hsub hn hm
      rw [← hdiff, hsub, hn, hm]
    have hdiffCont : ContinuousOn (fun τ => trace n τ - trace m τ) (Icc s T) :=
      (htraceCont n).sub (htraceCont m)
    have hEq := Measure.eqOn_Icc_of_ae_eq (volume : Measure ℝ) hsT.ne hae.symm
      hdiffCont (htraceDiffSpec n m).1
    exact hEq ht
  let F : ℕ → ContinuousMap (Icc s T) ℝ := fun n =>
    ⟨fun t => trace n t, (htraceCont n).domRestrict⟩
  let C : ℝ := Real.sqrt
    (PDE.Parabolic.LionsRep.cauchySliceEnergyBound (a := a) f u)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hF_cauchy : CauchySeq F := by
    rw [Metric.cauchySeq_iff]
    intro δ hδ
    have hδ' : 0 < δ / (2 * (C + 1)) := by positivity
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
      (hεreal.eventually (Iio_mem_nhds hδ'))
    refine ⟨N, ?_⟩
    intro n hn m hm
    have hsum :
        (eLpNorm (ψε n - ψε m) 2 (volume : Measure (Vec d))).toReal ≤
          (eLpNorm (ψε n - ψ) 2 (volume : Measure (Vec d))).toReal +
            (eLpNorm (ψε m - ψ) 2 (volume : Measure (Vec d))).toReal := by
      have hfun : ψε n - ψε m = (ψε n - ψ) - (ψε m - ψ) := by
        funext x
        simp only [Pi.sub_apply]
        ring
      rw [hfun]
      have hsub : eLpNorm ((ψε n - ψ) - (ψε m - ψ)) 2
          (volume : Measure (Vec d)) ≤
          eLpNorm (ψε n - ψ) 2 volume + eLpNorm (ψε m - ψ) 2 volume :=
        MeasureTheory.eLpNorm_sub_le (μ := volume) (p := (2 : ℝ≥0∞))
          (by norm_num : 1 ≤ (2 : ℝ≥0∞))
      have hfiniteA := hεfinite n
      have hfiniteB := hεfinite m
      have hfiniteSum :
          eLpNorm (ψε n - ψ) 2 (volume : Measure (Vec d)) +
            eLpNorm (ψε m - ψ) 2 (volume : Measure (Vec d)) ≠ ∞ :=
        ENNReal.add_ne_top.mpr ⟨hfiniteA, hfiniteB⟩
      have hreal := ENNReal.toReal_mono hfiniteSum hsub
      rwa [ENNReal.toReal_add hfiniteA hfiniteB] at hreal
    have hsumlt :
        (eLpNorm (ψε n - ψ) 2 (volume : Measure (Vec d))).toReal +
          (eLpNorm (ψε m - ψ) 2 (volume : Measure (Vec d))).toReal <
            δ / (C + 1) := by
      calc
        _ < δ / (2 * (C + 1)) + δ / (2 * (C + 1)) :=
          add_lt_add (hN n hn) (hN m hm)
        _ = δ / (C + 1) := by field_simp; ring
    have hprodlt : C *
        ((eLpNorm (ψε n - ψ) 2 (volume : Measure (Vec d))).toReal +
          (eLpNorm (ψε m - ψ) 2 (volume : Measure (Vec d))).toReal) < δ := by
      by_cases hC0 : C = 0
      · simpa [hC0] using hδ
      · calc
          _ < C * (δ / (C + 1)) :=
            mul_lt_mul_of_pos_left hsumlt (lt_of_le_of_ne hC (Ne.symm hC0))
          _ = δ * (C / (C + 1)) := by ring
          _ ≤ δ * 1 := mul_le_mul_of_nonneg_left
            ((div_le_one (by positivity)).2 (by linarith)) hδ.le
          _ = δ := by ring
    have hdist : dist (F n) (F m) ≤ C *
        ((eLpNorm (ψε n - ψ) 2 (volume : Measure (Vec d))).toReal +
          (eLpNorm (ψε m - ψ) 2 (volume : Measure (Vec d))).toReal) := by
      have hboundnonneg : 0 ≤ C *
          ((eLpNorm (ψε n - ψ) 2 (volume : Measure (Vec d))).toReal +
            (eLpNorm (ψε m - ψ) 2 (volume : Measure (Vec d))).toReal) :=
        mul_nonneg hC (by positivity)
      rw [ContinuousMap.dist_le hboundnonneg]
      intro t
      change dist (trace n t.1) (trace m t.1) ≤ _
      rw [Real.dist_eq]
      calc
        |trace n t.1 - trace m t.1| = |traceDiff n m t.1| := by
          rw [htraceDiffEq n m t.1 t.2]
        _ ≤ C * (eLpNorm (ψε n - ψε m) 2 volume).toReal := by
          simpa [C] using (htraceDiffSpec n m).2.2.2 t.1 t.2
        _ ≤ C * ((eLpNorm (ψε n - ψ) 2 volume).toReal +
            (eLpNorm (ψε m - ψ) 2 volume).toReal) :=
          mul_le_mul_of_nonneg_left hsum hC
    exact lt_of_le_of_lt hdist hprodlt
  obtain ⟨Flim, hF_tendsto⟩ := cauchySeq_tendsto_of_complete hF_cauchy
  let v : ℝ → ℝ := fun t => if ht : t ∈ Icc s T then Flim ⟨t, ht⟩ else 0
  have hvcont : ContinuousOn v (Icc s T) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun t : Icc s T => v (t : ℝ))
    have hrestrict : (fun t : Icc s T => v (t : ℝ)) = fun t => Flim t := by
      funext t
      change (if ht : (t : ℝ) ∈ Icc s T then Flim ⟨(t : ℝ), ht⟩ else 0) = Flim t
      rw [dite_eq_left t.2]
    rw [hrestrict]
    exact Flim.continuous
  have htrace_tendsto (t : ℝ) (ht : t ∈ Icc s T) :
      Tendsto (fun n => trace n t) atTop (𝓝 (v t)) := by
    have hmapDist : Tendsto (fun n => dist (F n) Flim) atTop (𝓝 0) :=
      (tendsto_iff_dist_tendsto_zero).1 hF_tendsto
    have hpointDist : Tendsto
        (fun n => dist (trace n t) (Flim ⟨t, ht⟩)) atTop (𝓝 0) := by
      let tI : Icc s T := ⟨t, ht⟩
      apply squeeze_zero (fun n => dist_nonneg)
        (fun n => by
          have hle := ContinuousMap.dist_apply_le_dist
            (f := F n) (g := Flim) tI
          change dist (trace n t) (Flim ⟨t, ht⟩) ≤ dist (F n) Flim
          exact hle)
        hmapDist
    have hvEq : v t = Flim ⟨t, ht⟩ := by
      change (if h : t ∈ Icc s T then Flim ⟨t, h⟩ else 0) = Flim ⟨t, ht⟩
      rw [dite_eq_left ht]
    rw [hvEq]
    exact (tendsto_iff_dist_tendsto_zero).2 hpointDist
  have htraceAet : ∀ᵐ t ∂(volume.restrict (Icc s T)), ∀ n,
      cauchyValuePairing u (ψε n) t = trace n t := ae_all_iff.2 htraceAE
  have hrawSlice : ∀ᵐ t ∂(volume.restrict (Icc s T)),
      MemLp (fun x : Vec d => cauchyEnergyValue u (x, t)) 2
        (volume : Measure (Vec d)) := cauchyEnergyValue_ae_sliceMemLp u
  have hrawEq : cauchyValuePairing u ψ =ᵐ[volume.restrict (Icc s T)] v := by
    filter_upwards [htraceAet, hrawSlice,
      ae_restrict_mem (measurableSet_Icc : MeasurableSet (Icc s T))]
      with t htraceAll hslice ht
    let sliceLp : Lp ℝ 2 (volume : Measure (Vec d)) :=
      hslice.toLp (fun x => cauchyEnergyValue u (x, t))
    have hpairEq (g : Vec d → ℝ) (hg : MemLp g 2 (volume : Measure (Vec d))) :
        cauchyValuePairing u g t =
          inner ℝ sliceLp (hg.toLp g) := by
      rw [cauchyValuePairing, MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hslice.coeFn_toLp, hg.coeFn_toLp] with x hx hgx
      rw [hx, hgx]
      change cauchyEnergyValue u (x, t) * g x = g x * cauchyEnergyValue u (x, t)
      ring
    have htests_tendsto : Tendsto (fun n => hψεtoLp n) atTop (𝓝 hψtoLp) := by
      apply (tendsto_iff_dist_tendsto_zero).2
      have hdist (n : ℕ) : dist (hψεtoLp n) hψtoLp =
          (eLpNorm (ψε n - ψ) 2 (volume : Measure (Vec d))).toReal := by
        rw [Lp.dist_edist, Lp.edist_toLp_toLp]
      simpa only [hdist] using hεreal
    have hinner_tendsto :
        Tendsto (fun n => inner ℝ sliceLp (hψεtoLp n)) atTop
          (𝓝 (inner ℝ sliceLp hψtoLp)) :=
      (continuous_const.inner continuous_id).continuousAt.tendsto.comp htests_tendsto
    have hpair_tendsto :
        Tendsto (fun n => cauchyValuePairing u (ψε n) t) atTop
          (𝓝 (cauchyValuePairing u ψ t)) := by
      have hseq := hinner_tendsto.congr'
        (Eventually.of_forall fun n => (hpairEq (ψε n) (hψεLp n)).symm)
      rw [← hpairEq ψ hψLp] at hseq
      exact hseq
    have htrace_tendsto' : Tendsto (fun n => cauchyValuePairing u (ψε n) t)
        atTop (𝓝 (v t)) := by
      have hpoint : Tendsto (fun n => trace n t) atTop (𝓝 (v t)) := htrace_tendsto t ht
      exact hpoint.congr' (Filter.Eventually.of_forall fun n => (htraceAll n).symm)
    have hEq := tendsto_nhds_unique hpair_tendsto htrace_tendsto'
    exact hEq
  have hinitial_tendsto : Tendsto
      (fun n => ∫ x, f x * ψε n x) atTop (𝓝 (∫ x, f x * ψ x)) := by
    have htests_tendsto : Tendsto (fun n => hψεtoLp n) atTop (𝓝 hψtoLp) := by
      apply (tendsto_iff_dist_tendsto_zero).2
      have hdist (n : ℕ) : dist (hψεtoLp n) hψtoLp =
          (eLpNorm (ψε n - ψ) 2 (volume : Measure (Vec d))).toReal := by
        rw [Lp.dist_edist, Lp.edist_toLp_toLp]
      simpa only [hdist] using hεreal
    have hinner_tendsto : Tendsto
        (fun n => inner ℝ (hf.toLp f) (hψεtoLp n)) atTop
          (𝓝 (inner ℝ (hf.toLp f) hψtoLp)) :=
      (continuous_const.inner continuous_id).continuousAt.tendsto.comp htests_tendsto
    have hintegralEq (g : Vec d → ℝ) (hg : MemLp g 2 (volume : Measure (Vec d))) :
        (∫ x, f x * g x) = inner ℝ (hf.toLp f) (hg.toLp g) := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
      rw [hfx, hgx]
      change f x * g x = g x * f x
      ring
    have htmp := hinner_tendsto.congr'
      (Filter.Eventually.of_forall fun n =>
        (hintegralEq (ψε n) (hψεLp n)).symm)
    rw [← hintegralEq ψ hψLp] at htmp
    exact htmp
  have htraceInit (n : ℕ) : trace n s = ∫ x, f x * ψε n x :=
    by
      simpa only [trace] using
        (Classical.choose_spec (PDE.Parabolic.Lions.exists_cauchy_scalar_pairing_representative
          hsT ha f hf u hrep (ψε n) (hψεcont n) (hψεcompact n))).2.2.1
  have htraceInit_tendsto : Tendsto (fun n => trace n s) atTop
      (𝓝 (∫ x, f x * ψ x)) := hinitial_tendsto.congr'
        (Filter.Eventually.of_forall fun n => (htraceInit n).symm)
  have hvInit : v s = ∫ x, f x * ψ x := by
    have hsI : s ∈ Icc s T := ⟨le_rfl, hsT.le⟩
    exact tendsto_nhds_unique (htrace_tendsto s hsI) htraceInit_tendsto
  exact ⟨v, hvcont, hrawEq, hvInit⟩

end PDE.Parabolic.Lions
