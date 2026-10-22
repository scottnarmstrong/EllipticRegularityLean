module

public import PDEFoundation.Sobolev.Cutoff.PuncturedTest
public import PDEFoundation.Sobolev.WeakGradientPointRemoval
public import PDEFoundation.Sobolev.W1p.Graph
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Removal of one point from a weak gradient identity -/

@[expose] public section

namespace PDE

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

private theorem tendsto_integral_mul_one_sub_pointRemovalCutoff
    {d : ℕ} (hd : 0 < d) {U : Set (Vec d)}
    {h : Vec d → ℝ} (hh : Integrable h (volume.restrict U))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in U, h x * (1 - pointRemovalCutoff (ε n) x))
      atTop (𝓝 (∫ x in U, h x)) := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  let μ : Measure (Vec d) := volume.restrict U
  let q : ℕ → Vec d → ℝ := fun n x => h x * (1 - pointRemovalCutoff (ε n) x)
  have hmeas (n : ℕ) : AEStronglyMeasurable (q n) μ := by
    have hs := canonicalBallCutoff_smooth (0 : Vec d) (hε n).le
      (by linarith [hε n] : ε n < 2 * ε n)
    exact hh.aestronglyMeasurable.mul
      (continuous_const.sub hs.continuous).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ x ∂μ, ‖q n x‖ ≤ ‖h x‖ := by
    filter_upwards with x
    have hη0 := canonicalBallCutoff_nonneg (0 : Vec d) (ε n) (2 * ε n) x
    have hη1 := canonicalBallCutoff_le_one (0 : Vec d) (ε n) (2 * ε n) x
    dsimp only [q]
    rw [norm_mul, Real.norm_eq_abs]
    change |h x| * |1 - canonicalBallCutoff 0 (ε n) (2 * ε n) x| ≤ _
    rw [abs_of_nonneg (sub_nonneg.mpr hη1)]
    exact mul_le_of_le_one_right (abs_nonneg _) (by linarith)
  have hne : ∀ᵐ x ∂μ, x ≠ (0 : Vec d) := by
    rw [ae_iff]
    have hm : μ {(0 : Vec d)} = 0 := le_zero_iff.mp <| calc
      μ {(0 : Vec d)} ≤ volume {(0 : Vec d)} :=
        (Measure.restrict_le_self : μ ≤ volume) {(0 : Vec d)}
      _ = 0 := measure_singleton (0 : Vec d)
    simpa only [not_ne_iff] using! hm
  have hpoint : ∀ᵐ x ∂μ, Tendsto (fun n => q n x) atTop (𝓝 (h x)) := by
    filter_upwards [hne] with x hx
    have hcut := tendsto_pointRemovalCutoff_zero_of_ne_zero ε hε hε0 hx
    simpa only [q, sub_zero, mul_one] using
      (hcut.const_sub (1 : ℝ)).const_mul (h x)
  exact tendsto_integral_of_dominated_convergence (fun x => ‖h x‖)
    hmeas hh.norm hbound hpoint

/-- In dimension at least two, deleting the origin does not change an actual
`L²` weak gradient identity. -/
theorem hasWeakGradientOn_of_diff_singleton_zero
    {d : ℕ} (hd : 2 ≤ d) {U : Set (Vec d)} (hU : IsOpen U)
    {f : Vec d → ℝ} {G : Vec d → Vec d}
    (hf : MemLp f 2 (volume.restrict U))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict U))
    (hpunctured : HasWeakGradientOn (U \ {(0 : Vec d)}) f G) :
    HasWeakGradientOn U f G := by
  have _hUmeas : MeasurableSet U := hU.measurableSet
  let : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hd)⟩
  let ε : ℕ → ℝ := fun n => 1 / (n + 1)
  have hε : ∀ n, 0 < ε n := by
    intro n
    dsimp only [ε]
    positivity
  have hε1 : ∀ n, ε n ≤ 1 := by
    intro n
    dsimp only [ε]
    rw [div_le_one (by positivity)]
    norm_num
  have hε0 : Tendsto ε atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hset : U \ ({0} : Set (Vec d)) =ᵐ[volume] U := by
    have hne : ∀ᵐ x ∂volume, x ≠ (0 : Vec d) := by
      rw [ae_iff]
      simpa only [not_ne_iff] using! (measure_singleton (0 : Vec d))
    filter_upwards [hne] with x hx
    apply propext
    constructor
    · exact And.left
    · intro hxU
      exact ⟨hxU, hx⟩
  have hμ : volume.restrict (U \ ({0} : Set (Vec d))) = volume.restrict U :=
    MeasureTheory.Measure.restrict_congr_set hset
  intro i
  rw [hasWeakPartialDerivOn_iff_forall_testFunction]
  intro φ
  have hφ2 := φ.memLp_toFun 2
  have hdφ2 := φ.memLp_partialDeriv i 2
  have hfdφ : Integrable (fun x => f x * φ.partialDeriv i x)
      (volume.restrict U) := hf.integrable_mul hdφ2
  have hGφ : Integrable (fun x => G x i * φ x)
      (volume.restrict U) := (hG i).integrable_mul hφ2
  have hA := tendsto_integral_mul_one_sub_pointRemovalCutoff
    (lt_of_lt_of_le (by norm_num) hd) hfdφ ε hε hε0
  have hB := tendsto_integral_mul_one_sub_pointRemovalCutoff
    (lt_of_lt_of_le (by norm_num) hd) hGφ ε hε hε0
  have hE := tendsto_integral_weakTestFunction_mul_pointRemovalGradient_zero
    hd hf φ i ε hε hε1 hε0
  have hid (n : ℕ) :
      (∫ x in U, (f x * φ.partialDeriv i x) *
          (1 - pointRemovalCutoff (ε n) x)) -
        (∫ x in U, f x * φ x *
          classicalGradient (pointRemovalCutoff (ε n)) x i) =
      -(∫ x in U, (G x i * φ x) *
          (1 - pointRemovalCutoff (ε n) x)) := by
    have hp := (hasWeakPartialDerivOn_iff_forall_testFunction.mp
      (hpunctured i)) (φ.punctured (ε n) (hε n))
    change (
      ∫ x, f x * (φ.punctured (ε n) (hε n)).partialDeriv i x
        ∂(volume.restrict (U \ {(0 : Vec d)}))) =
      -∫ x, G x i * (φ.punctured (ε n) (hε n)) x
        ∂(volume.restrict (U \ {(0 : Vec d)})) at hp
    rw [hμ] at hp
    simp only [WeakTestFunction.punctured_partialDeriv,
      WeakTestFunction.punctured_apply] at hp
    have hfirst : Integrable (fun x =>
        (f x * φ.partialDeriv i x) *
          (1 - pointRemovalCutoff (ε n) x)) (volume.restrict U) := by
      exact hfdφ.mul_bdd
        (continuous_const.sub
          (canonicalBallCutoff_smooth (0 : Vec d) (hε n).le
            (by linarith [hε n])).continuous).aestronglyMeasurable
        (by
          filter_upwards with x
          have h0 := canonicalBallCutoff_nonneg (0 : Vec d) (ε n) (2 * ε n) x
          have h1 := canonicalBallCutoff_le_one (0 : Vec d) (ε n) (2 * ε n) x
          rw [Real.norm_eq_abs]
          change |1 - canonicalBallCutoff 0 (ε n) (2 * ε n) x| ≤ (1 : ℝ)
          rw [abs_of_nonneg (sub_nonneg.mpr h1)]
          linarith)
    have herr : Integrable (fun x => f x * φ x *
        classicalGradient (pointRemovalCutoff (ε n)) x i)
        (volume.restrict U) := by
      have hgrad := (pointRemovalCutoff_euclideanGradient_memLp_two
        (d := d) (hε n)).mono_measure
        (Measure.restrict_le_self : volume.restrict U ≤ volume)
      have hcoord : MemLp (fun x =>
          classicalGradient (pointRemovalCutoff (ε n)) x i) 2
          (volume.restrict U) := hgrad.mono
        ((continuous_apply i).comp
          (PDE.ContDiff.continuous_classicalGradient
            ((canonicalBallCutoff_smooth (0 : Vec d) (hε n).le
              (show ε n < 2 * ε n by linarith [hε n])).of_le
                (by simp)))).aestronglyMeasurable
        (ae_of_all _ fun x => by
          simpa only [Real.norm_eq_abs,
            abs_of_nonneg (vecEuclideanNorm_nonneg _)] using
              abs_apply_le_vecEuclideanNorm
                (classicalGradient (pointRemovalCutoff (ε n)) x) i)
      obtain ⟨C, hC⟩ := φ.contDiff.continuous.bounded_above_of_compact_support
        φ.hasCompactSupport
      have ht := (hf.integrable_mul hcoord).bdd_mul
        φ.contDiff.continuous.aestronglyMeasurable (ae_of_all _ hC)
      exact ht.congr (ae_of_all _ fun x => by
        simp only [Pi.mul_apply]
        ring)
    rw [show (fun x => f x *
        (φ.partialDeriv i x * (1 - pointRemovalCutoff (ε n) x) -
          φ x * classicalGradient (pointRemovalCutoff (ε n)) x i)) =
        fun x => (f x * φ.partialDeriv i x) *
          (1 - pointRemovalCutoff (ε n) x) -
          f x * φ x * classicalGradient (pointRemovalCutoff (ε n)) x i by
        funext x; ring,
      integral_sub hfirst herr] at hp
    simpa only [mul_assoc] using hp
  have hleft : Tendsto (fun n =>
      (∫ x in U, (f x * φ.partialDeriv i x) *
        (1 - pointRemovalCutoff (ε n) x)) -
      (∫ x in U, f x * φ x *
        classicalGradient (pointRemovalCutoff (ε n)) x i))
      atTop (nhds (∫ x in U, f x * φ.partialDeriv i x)) := by
    simpa only [sub_zero] using hA.sub hE
  have hright := hB.neg
  exact tendsto_nhds_unique hleft
    (hright.congr' (Filter.Eventually.of_forall fun n => (hid n).symm))

end

end PDE
