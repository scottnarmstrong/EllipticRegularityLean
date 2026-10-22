module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.LionsRep.InitialSlice
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! # Ball averages of the all-time Riesz slices -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE.Parabolic.LionsRep

private noncomputable def cauchySliceBallTest {d : ℕ} (n : ℕ) (x : Vec d) :
    Vec d → ℝ :=
  (Metric.closedBall x (1 / ((n : ℝ) + 1))).indicator (fun _ => (1 : ℝ))

private noncomputable def cauchySliceBallTestLp {d : ℕ} (n : ℕ) (x : Vec d) :
    Lp ℝ 2 (volume : Measure (Vec d)) :=
  MeasureTheory.indicatorConstLp 2
    measurableSet_closedBall
    (isCompact_closedBall x (1 / ((n : ℝ) + 1))).measure_ne_top 1

private theorem cauchySliceBallTestLp_memLp {d : ℕ} (n : ℕ) (x : Vec d) :
    MemLp (cauchySliceBallTest n x) 2 (volume : Measure (Vec d)) := by
  exact memLp_indicator_const 2 measurableSet_closedBall
    1 (Or.inr (isCompact_closedBall x (1 / ((n : ℝ) + 1))).measure_ne_top)

noncomputable def cauchySliceBallAverage
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (n : ℕ) (x : Vec d) (t : Icc s T) : ℝ :=
  ⨍ y in Metric.closedBall x (1 / ((n : ℝ) + 1)),
    (cauchyL2TimeSlice hsT ha f hf u hclose hrep t : Vec d → ℝ) y

private theorem cauchySliceBallAverage_continuous
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (n : ℕ) (x : Vec d) :
    Continuous (fun t : Icc s T => cauchySliceBallAverage hsT ha f hf u hclose hrep n x t) := by
  let ψ := cauchySliceBallTest n x
  let hψ : MemLp ψ 2 (volume : Measure (Vec d)) :=
    cauchySliceBallTestLp_memLp n x
  obtain ⟨v, hv, hpair, _⟩ :=
    exists_cauchyL2TimeSlice_pairing_continuous_initial
      hsT ha f hf u hclose hrep ψ hψ
  have hvol : ∀ t : Icc s T,
      (∫ y in Metric.closedBall x (1 / ((n : ℝ) + 1)),
        (cauchyL2TimeSlice hsT ha f hf u hclose hrep t : Vec d → ℝ) y) =
      inner ℝ (cauchyL2TimeSlice hsT ha f hf u hclose hrep t) (hψ.toLp ψ) := by
    intro t
    let K := Metric.closedBall x (1 / ((n : ℝ) + 1))
    let q := cauchyL2TimeSlice hsT ha f hf u hclose hrep t
    let g : Vec d → ℝ := (Lp.aestronglyMeasurable q).mk q
    have hq : g =ᵐ[volume] q := (Lp.aestronglyMeasurable q).ae_eq_mk.symm
    have hp : (hψ.toLp ψ : Vec d → ℝ) =ᵐ[volume] ψ := hψ.coeFn_toLp
    have hqK : g =ᵐ[volume.restrict K] q := by
      apply (ae_restrict_iff' (measurableSet_closedBall : MeasurableSet K)).2
      filter_upwards [hq] with y hy
      exact fun _ => hy
    have hpK : (hψ.toLp ψ : Vec d → ℝ) =ᵐ[volume.restrict K] ψ := by
      apply (ae_restrict_iff' (measurableSet_closedBall : MeasurableSet K)).2
      filter_upwards [hp] with y hy
      exact fun _ => hy
    have hmemK : ∀ᵐ y ∂(volume.restrict K), y ∈ K :=
      ae_restrict_mem (measurableSet_closedBall : MeasurableSet K)
    have hset : (∫ y in K, q y) = ∫ y in K, q y * (hψ.toLp ψ) y := by
      apply integral_congr_ae
      filter_upwards [hpK, hmemK] with y hy hypK
      rw [hy]
      have hψone : ψ y = 1 := by
        dsimp [ψ, cauchySliceBallTest]
        exact Set.indicator_of_mem hypK _
      rw [hψone]
      ring
    have hprodK : (fun y => q y * (hψ.toLp ψ) y) =ᵐ[volume.restrict K]
        (fun y => g y * ψ y) := by
      filter_upwards [hqK, hpK] with y hyq hyp
      rw [hyq, hyp]
    have hprod : (fun y => q y * (hψ.toLp ψ) y) =ᵐ[volume]
        (fun y => g y * ψ y) := by
      filter_upwards [hq, hp] with y hyq hyp
      rw [hyq, hyp]
    have hwhole : (∫ y, q y * (hψ.toLp ψ) y) = ∫ y, g y * ψ y := by
      apply integral_congr_ae
      exact hprod
    have hindicator : (∫ y in K, g y * ψ y) = ∫ y, g y * ψ y := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hψzero : ψ y = 0 := by
        change (Metric.closedBall x (1 / ((n : ℝ) + 1))).indicator
          (fun _ => (1 : ℝ)) y = 0
        exact Set.indicator_of_notMem (s := Metric.closedBall x (1 / ((n : ℝ) + 1)))
          (by simpa [K] using hy) (fun _ => (1 : ℝ))
      simp [hψzero]
    have hinner : inner ℝ q (hψ.toLp ψ) = ∫ y, q y * (hψ.toLp ψ) y := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [Real.inner_apply]
    calc
      (∫ y in K, q y) = ∫ y in K, q y * (hψ.toLp ψ) y := hset
      _ = ∫ y in K, g y * ψ y := by
        apply integral_congr_ae
        exact hprodK
      _ = ∫ y, g y * ψ y := hindicator
      _ = ∫ y, q y * (hψ.toLp ψ) y := hwhole.symm
      _ = inner ℝ q (hψ.toLp ψ) := hinner.symm
  have haverage (t : Icc s T) :
      cauchySliceBallAverage hsT ha f hf u hclose hrep n x t =
        (volume.real (Metric.closedBall x (1 / ((n : ℝ) + 1))))⁻¹ * v t := by
    rw [cauchySliceBallAverage, MeasureTheory.setAverage_eq, smul_eq_mul, hvol t, hpair t]
  have hv' : Continuous (fun t : Icc s T =>
      (volume.real (Metric.closedBall x (1 / ((n : ℝ) + 1))))⁻¹ * v t) :=
    continuous_const.mul hv
  exact hv'.congr fun t => (haverage t).symm

private theorem cauchySliceBallAverage_measurable_spatial
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (n : ℕ) (t : Icc s T) :
    Measurable (fun x => cauchySliceBallAverage hsT ha f hf u hclose hrep n x t) := by
  let r : ℝ := 1 / ((n : ℝ) + 1)
  let q : Lp ℝ 2 (volume : Measure (Vec d)) :=
    cauchyL2TimeSlice hsT ha f hf u hclose hrep t
  let g : Vec d → ℝ := (Lp.aestronglyMeasurable q).mk q
  have hg : StronglyMeasurable g := by
    exact (Lp.aestronglyMeasurable q).stronglyMeasurable_mk
  have hq : g =ᵐ[volume] q := (Lp.aestronglyMeasurable q).ae_eq_mk.symm
  let F : Vec d × Vec d → ℝ := fun z =>
    if dist z.1 z.2 ≤ r then g z.2 else 0
  have hF : Measurable F := by
    apply Measurable.ite
    · exact measurableSet_le continuous_dist.measurable measurable_const
    · exact hg.measurable.comp measurable_snd
    · exact measurable_const
  have hFsm : StronglyMeasurable F := hF.stronglyMeasurable
  have hIntMeas : StronglyMeasurable (fun x => ∫ y, F (x, y)) :=
    hFsm.integral_prod_right'
  have hvol (x : Vec d) : volume.real (Metric.closedBall x r) =
      volume.real (Metric.closedBall (0 : Vec d) r) := by
    change ENNReal.toReal (volume (Metric.closedBall x r)) =
      ENNReal.toReal (volume (Metric.closedBall (0 : Vec d) r))
    rw [Real.volume_pi_closedBall x (by positivity),
      Real.volume_pi_closedBall (0 : Vec d) (by positivity)]
  have hset (x : Vec d) :
      (∫ y in Metric.closedBall x r, q y) = ∫ y, F (x, y) := by
    calc
      (∫ y in Metric.closedBall x r, q y) =
          ∫ y in Metric.closedBall x r, g y := by
        apply integral_congr_ae
        have hqK : g =ᵐ[volume.restrict (Metric.closedBall x r)] q := by
          apply (ae_restrict_iff' measurableSet_closedBall).2
          filter_upwards [hq] with y hy
          exact fun _ => hy
        exact hqK.symm
      _ = ∫ y, F (x, y) := by
        rw [← integral_indicator measurableSet_closedBall]
        apply integral_congr_ae
        filter_upwards [] with y
        by_cases hy : y ∈ Metric.closedBall x r
        · have hy' : dist x y ≤ r := by
            simpa [Metric.mem_closedBall, dist_comm] using hy
          rw [Set.indicator_of_mem hy]
          simp [F, hy']
        · have hy' : ¬ dist x y ≤ r := by
            intro hy'
            apply hy
            simpa [Metric.mem_closedBall, dist_comm] using hy'
          rw [Set.indicator_of_notMem hy]
          simp [F, hy']
  have heq (x : Vec d) :
      (∫ y in Metric.closedBall x r, q y) = ∫ y, F (x, y) := hset x
  have hc : Measurable fun x : Vec d =>
      (volume.real (Metric.closedBall x r))⁻¹ := by
    have : (fun x : Vec d => (volume.real (Metric.closedBall x r))⁻¹) =
        fun _ => (volume.real (Metric.closedBall (0 : Vec d) r))⁻¹ := by
      funext x
      rw [hvol x]
    rw [this]
    exact measurable_const
  have hresult : Measurable fun x : Vec d =>
      (volume.real (Metric.closedBall x r))⁻¹ * ∫ y, F (x, y) :=
    hc.mul hIntMeas.measurable
  have havg (x : Vec d) :
      cauchySliceBallAverage hsT ha f hf u hclose hrep n x t =
        (volume.real (Metric.closedBall x r))⁻¹ *
          ∫ y in Metric.closedBall x r, q y := by
    rw [cauchySliceBallAverage, MeasureTheory.setAverage_eq, smul_eq_mul]
  have havgF (x : Vec d) :
      cauchySliceBallAverage hsT ha f hf u hclose hrep n x t =
        (volume.real (Metric.closedBall x r))⁻¹ * ∫ y, F (x, y) := by
    rw [havg x, heq x]
  have hfun : (fun x : Vec d => cauchySliceBallAverage
      hsT ha f hf u hclose hrep n x t) =
      fun x => (volume.real (Metric.closedBall x r))⁻¹ * ∫ y, F (x, y) :=
    funext havgF
  rw [hfun]
  exact hresult

private theorem cauchySliceBallAverage_measurable_joint
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (n : ℕ) : Measurable (fun z : Vec d × Icc s T =>
      cauchySliceBallAverage hsT ha f hf u hclose hrep n z.1 z.2) := by
  have hcar : Measurable (Function.uncurry fun (t : Icc s T) (x : Vec d) =>
      cauchySliceBallAverage hsT ha f hf u hclose hrep n x t) := by
    apply measurable_uncurry_of_continuous_of_measurable
    · intro x
      exact cauchySliceBallAverage_continuous hsT ha f hf u hclose hrep n x
    · intro t
      exact cauchySliceBallAverage_measurable_spatial hsT ha f hf u hclose hrep n t
  have hswap : Measurable (Function.uncurry fun (x : Vec d) (t : Icc s T) =>
      cauchySliceBallAverage hsT ha f hf u hclose hrep n x t) := by
    convert hcar.comp measurable_swap using 1
    funext z
    rfl
  convert hswap using 1
  funext z
  rfl

/-- The representative obtained as the pointwise limit of ball averages of the Riesz slices on
the closed time interval. -/
noncomputable def cauchyRieszSliceRepresentativeOn
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (z : Vec d × Icc s T) : ℝ :=
  limUnder atTop (fun n => cauchySliceBallAverage hsT ha f hf u hclose hrep n z.1 z.2)

theorem cauchyRieszSliceRepresentativeOn_measurable
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u) :
    Measurable (cauchyRieszSliceRepresentativeOn hsT ha f hf u hclose hrep) := by
  have havg (n : ℕ) : Measurable (Function.uncurry fun (x : Vec d) (t : Icc s T) =>
      cauchySliceBallAverage hsT ha f hf u hclose hrep n x t) :=
    cauchySliceBallAverage_measurable_joint hsT ha f hf u hclose hrep n
  have hseq (n : ℕ) : StronglyMeasurable fun z : Vec d × Icc s T =>
      cauchySliceBallAverage hsT ha f hf u hclose hrep n z.1 z.2 := by
    have hmeas := havg n
    convert hmeas.stronglyMeasurable using 1
    funext z
    rfl
  have hlim : StronglyMeasurable
      (fun z : Vec d × Icc s T =>
        limUnder atTop (fun n => cauchySliceBallAverage hsT ha f hf u hclose hrep n z.1 z.2)) :=
    StronglyMeasurable.limUnder hseq
  exact hlim.measurable

theorem cauchyRieszSliceRepresentativeOn_ae_eq_slice
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (t : Icc s T) :
    (fun x => cauchyRieszSliceRepresentativeOn hsT ha f hf u hclose hrep (x, t)) =ᵐ[volume]
      (cauchyL2TimeSlice hsT ha f hf u hclose hrep t : Vec d → ℝ) := by
  let q : Lp ℝ 2 (volume : Measure (Vec d)) :=
    cauchyL2TimeSlice hsT ha f hf u hclose hrep t
  have hqLoc : LocallyIntegrable (q : Vec d → ℝ) :=
    (Lp.memLp q).locallyIntegrable (by norm_num)
  have hdiff := IsUnifLocDoublingMeasure.ae_tendsto_average
    (volume : Measure (Vec d)) hqLoc 1
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδ : Tendsto δ atTop (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa [δ, one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · filter_upwards [] with n
      simp only [Set.mem_Ioi]
      dsimp [δ]
      positivity
  filter_upwards [hdiff] with x hx
  have hxmem : ∀ᶠ n : ℕ in atTop, x ∈ Metric.closedBall x (1 * δ n) := by
    filter_upwards [] with n
    simp [Metric.mem_closedBall]
    positivity
  have hconv : Tendsto
      (fun n => ⨍ y in Metric.closedBall x (δ n), (q : Vec d → ℝ) y)
      atTop (𝓝 ((q : Vec d → ℝ) x)) :=
    hx (fun _ => x) δ hδ hxmem
  have hlim := hconv.limUnder_eq
  change limUnder atTop
      (fun n => cauchySliceBallAverage hsT ha f hf u hclose hrep n x t) =
        (q : Vec d → ℝ) x
  simpa [cauchyRieszSliceRepresentativeOn, cauchySliceBallAverage, q, δ] using hlim

noncomputable def cauchyTimeClamp {s T : ℝ} (hsT : s < T) (t : ℝ) : Icc s T :=
  ⟨max s (min t T), le_max_left _ _, max_le hsT.le (min_le_right _ _)⟩

private theorem cauchyTimeClamp_eq {s T : ℝ} (hsT : s < T) (t : Icc s T) :
    cauchyTimeClamp hsT t = t := by
  apply Subtype.ext
  simp [cauchyTimeClamp, t.2.1, t.2.2]

/-- The ball-average representative extended to all real times by clamping outside the slab. -/
noncomputable def cauchyRieszSliceRepresentative
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u) : Vec d × ℝ → ℝ :=
  fun z => cauchyRieszSliceRepresentativeOn hsT ha f hf u hclose hrep
    (z.1, cauchyTimeClamp hsT z.2)

theorem cauchyRieszSliceRepresentative_measurable
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u) :
    Measurable (cauchyRieszSliceRepresentative hsT ha f hf u hclose hrep) := by
  have hclamp : Measurable (cauchyTimeClamp hsT) := by
    have hc : Continuous fun t : ℝ => max s (min t T) :=
      continuous_const.max (continuous_id.min continuous_const)
    exact (hc.subtype_mk _).measurable
  have hmap : Measurable (fun z : Vec d × ℝ => (z.1, cauchyTimeClamp hsT z.2)) := by
    exact measurable_fst.prodMk (hclamp.comp measurable_snd)
  exact (cauchyRieszSliceRepresentativeOn_measurable hsT ha f hf u hclose hrep).comp hmap

theorem cauchyRieszSliceRepresentative_ae_eq_slice
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (t : Icc s T) :
    (fun x => cauchyRieszSliceRepresentative hsT ha f hf u hclose hrep (x, t)) =ᵐ[volume]
      (cauchyL2TimeSlice hsT ha f hf u hclose hrep t : Vec d → ℝ) := by
  have hslice := cauchyRieszSliceRepresentativeOn_ae_eq_slice hsT ha f hf u hclose hrep t
  have hclamp := cauchyTimeClamp_eq hsT t
  simpa [cauchyRieszSliceRepresentative, hclamp] using hslice

theorem cauchyRieszSliceRepresentative_initial_ae_eq_data
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u) :
    (fun x => cauchyRieszSliceRepresentative hsT ha f hf u hclose hrep (x, s)) =ᵐ[volume] f := by
  let ts : Icc s T := ⟨s, ⟨le_rfl, hsT.le⟩⟩
  have hslice := cauchyRieszSliceRepresentative_ae_eq_slice
    hsT ha f hf u hclose hrep ts
  have hinit := cauchyL2TimeSlice_initial_eq hsT ha f hf u hclose hrep
  have hclassFn :
      (cauchyL2TimeSlice hsT ha f hf u hclose hrep ts : Vec d → ℝ) =
        (hf.toLp f : Vec d → ℝ) :=
    congrArg (fun q : Lp ℝ 2 (volume : Measure (Vec d)) => (q : Vec d → ℝ)) hinit
  have hinitFn :
      (cauchyL2TimeSlice hsT ha f hf u hclose hrep ts : Vec d → ℝ) =ᵐ[volume] f := by
    filter_upwards [hf.coeFn_toLp] with x hx
    exact (congrFun hclassFn x).trans hx
  simpa [ts] using hslice.trans hinitFn

end PDE.Parabolic.LionsRep
