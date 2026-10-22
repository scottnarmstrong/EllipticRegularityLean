module

public import PDEFoundation.Sobolev.WeakGradientRemovablePoint

/-! # Removal of one point from a weak divergence identity -/

@[expose] public section

namespace PDE

open Filter MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

private theorem tendsto_integral_mul_cutoffComplement_div
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
      (show ε n < 2 * ε n by linarith [hε n])
    exact hh.aestronglyMeasurable.mul
      (continuous_const.sub hs.continuous).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ x ∂μ, ‖q n x‖ ≤ ‖h x‖ := by
    filter_upwards with x
    have h0 := canonicalBallCutoff_nonneg (0 : Vec d) (ε n) (2 * ε n) x
    have h1 := canonicalBallCutoff_le_one (0 : Vec d) (ε n) (2 * ε n) x
    rw [norm_mul, Real.norm_eq_abs]
    change |h x| * |1 - canonicalBallCutoff 0 (ε n) (2 * ε n) x| ≤ |h x|
    rw [abs_of_nonneg (sub_nonneg.mpr h1)]
    exact mul_le_of_le_one_right (abs_nonneg _) (by linarith)
  have hne : ∀ᵐ x ∂μ, x ≠ (0 : Vec d) := by
    rw [ae_iff]
    have hm : μ {(0 : Vec d)} = 0 := le_zero_iff.mp <| calc
      μ {(0 : Vec d)} ≤ volume {(0 : Vec d)} :=
        (Measure.restrict_le_self : μ ≤ volume) {(0 : Vec d)}
      _ = 0 := measure_singleton _
    simpa only [not_ne_iff] using! hm
  have hpoint : ∀ᵐ x ∂μ, Tendsto (fun n => q n x) atTop (𝓝 (h x)) := by
    filter_upwards [hne] with x hx
    have hc := tendsto_pointRemovalCutoff_zero_of_ne_zero ε hε hε0 hx
    simpa only [q, sub_zero, mul_one] using (hc.const_sub (1 : ℝ)).const_mul (h x)
  exact tendsto_integral_of_dominated_convergence (fun x => ‖h x‖)
    hmeas hh.norm hbound hpoint

/-- An `L²` vector field whose divergence vanishes weakly off the origin has
zero weak divergence across the origin in dimension at least two. -/
theorem integral_vecDot_classicalGradient_eq_zero_of_diff_singleton_zero
    {d : ℕ} (hd : 2 ≤ d) {U : Set (Vec d)} (hU : IsOpen U)
    {J : Vec d → Vec d}
    (hJ : ∀ i, MemLp (fun x => J x i) 2 (volume.restrict U))
    (hpunctured : ∀ φ : WeakTestFunction (U \ {(0 : Vec d)}),
      ∫ x in U \ {(0 : Vec d)},
        vecDot (J x) (classicalGradient φ x) = 0) :
    ∀ φ : WeakTestFunction U,
      ∫ x in U, vecDot (J x) (classicalGradient φ x) = 0 := by
  have _hUmeas : MeasurableSet U := hU.measurableSet
  let : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hd)⟩
  let ε : ℕ → ℝ := fun n => 1 / (n + 1)
  have hε : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  have hε1 : ∀ n, ε n ≤ 1 := fun n => by
    dsimp [ε]; rw [div_le_one (by positivity)]; norm_num
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hset : U \ ({0} : Set (Vec d)) =ᵐ[volume] U := by
    have hn : ∀ᵐ x ∂volume, x ≠ (0 : Vec d) := by
      rw [ae_iff]
      simpa only [not_ne_iff] using! (measure_singleton (0 : Vec d))
    filter_upwards [hn] with x hx
    apply propext
    constructor
    · exact And.left
    · intro hxU; exact ⟨hxU, hx⟩
  have hμ : volume.restrict (U \ ({0} : Set (Vec d))) = volume.restrict U :=
    MeasureTheory.Measure.restrict_congr_set hset
  intro φ
  have hOrd (i : Fin d) : Integrable (fun x => J x i * φ.partialDeriv i x)
      (volume.restrict U) := (hJ i).integrable_mul (φ.memLp_partialDeriv i 2)
  have hA (i : Fin d) := tendsto_integral_mul_cutoffComplement_div
    (lt_of_lt_of_le (by norm_num) hd) (hOrd i) ε hε hε0
  have hE (i : Fin d) :=
    tendsto_integral_weakTestFunction_mul_pointRemovalGradient_zero
      hd (hJ i) φ i ε hε hε1 hε0
  have hid (n : ℕ) :
      (∑ i : Fin d, ∫ x in U, (J x i * φ.partialDeriv i x) *
          (1 - pointRemovalCutoff (ε n) x)) -
        (∑ i : Fin d, ∫ x in U, J x i * φ x *
          classicalGradient (pointRemovalCutoff (ε n)) x i) = 0 := by
    have hp := hpunctured (φ.punctured (ε n) (hε n))
    rw [show (∫ x in U \ {(0 : Vec d)},
        vecDot (J x) (classicalGradient (φ.punctured (ε n) (hε n)) x)) =
        ∑ i : Fin d, ∫ x in U \ {(0 : Vec d)},
          J x i * (φ.punctured (ε n) (hε n)).partialDeriv i x by
      simp only [vecDot, WeakTestFunction.partialDeriv, classicalGradient_apply]
      rw [integral_finsetSum]
      · intro i _
        exact ((hJ i).mono_measure (by
          rw [hμ])).integrable_mul
            ((φ.punctured (ε n) (hε n)).memLp_partialDeriv i 2)] at hp
    rw [hμ] at hp
    have hsplit (i : Fin d) :
        (∫ x in U, J x i * (φ.punctured (ε n) (hε n)).partialDeriv i x) =
          (∫ x in U, (J x i * φ.partialDeriv i x) *
            (1 - pointRemovalCutoff (ε n) x)) -
          (∫ x in U, J x i * φ x *
            classicalGradient (pointRemovalCutoff (ε n)) x i) := by
      simp only [WeakTestFunction.punctured_partialDeriv]
      have hfirst : Integrable (fun x => (J x i * φ.partialDeriv i x) *
          (1 - pointRemovalCutoff (ε n) x)) (volume.restrict U) := by
        exact (hOrd i).mul_bdd
          (continuous_const.sub
            (canonicalBallCutoff_smooth (0 : Vec d) (hε n).le
              (show ε n < 2 * ε n by linarith [hε n])).continuous).aestronglyMeasurable
          (ae_of_all _ fun x => by
            have h0 := canonicalBallCutoff_nonneg (0 : Vec d) (ε n) (2 * ε n) x
            have h1 := canonicalBallCutoff_le_one (0 : Vec d) (ε n) (2 * ε n) x
            rw [Real.norm_eq_abs]
            change |1 - canonicalBallCutoff 0 (ε n) (2 * ε n) x| ≤ (1 : ℝ)
            rw [abs_of_nonneg (sub_nonneg.mpr h1)]; linarith)
      have herr : Integrable (fun x => J x i * φ x *
          classicalGradient (pointRemovalCutoff (ε n)) x i)
          (volume.restrict U) := by
        have hg := (pointRemovalCutoff_euclideanGradient_memLp_two
          (d := d) (hε n)).mono_measure
            (Measure.restrict_le_self : volume.restrict U ≤ volume)
        have hc : MemLp (fun x => classicalGradient
            (pointRemovalCutoff (ε n)) x i) 2 (volume.restrict U) := hg.mono
          ((continuous_apply i).comp
            (PDE.ContDiff.continuous_classicalGradient
              ((canonicalBallCutoff_smooth (0 : Vec d) (hε n).le
                (show ε n < 2 * ε n by linarith [hε n])).of_le
                  (by simp)))).aestronglyMeasurable
          (ae_of_all _ fun x => by
            simpa [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _)]
              using abs_apply_le_vecEuclideanNorm
                (classicalGradient (pointRemovalCutoff (ε n)) x) i)
        obtain ⟨C, hC⟩ := φ.contDiff.continuous.bounded_above_of_compact_support
          φ.hasCompactSupport
        have ht := ((hJ i).integrable_mul hc).bdd_mul
          φ.contDiff.continuous.aestronglyMeasurable (ae_of_all _ hC)
        exact ht.congr (ae_of_all _ fun x => by
          simp only [Pi.mul_apply]
          ring)
      rw [show (fun x => J x i *
          (φ.partialDeriv i x * (1 - pointRemovalCutoff (ε n) x) -
            φ x * classicalGradient (pointRemovalCutoff (ε n)) x i)) =
          fun x => (J x i * φ.partialDeriv i x) *
            (1 - pointRemovalCutoff (ε n) x) - J x i * φ x *
              classicalGradient (pointRemovalCutoff (ε n)) x i by funext x; ring,
        integral_sub hfirst herr]
    simp_rw [hsplit] at hp
    simpa [Finset.sum_sub_distrib] using hp
  have hAsum := tendsto_finsetSum Finset.univ (fun i _ => hA i)
  have hEsum := tendsto_finsetSum Finset.univ (fun i _ => hE i)
  have hdiff : Tendsto (fun n =>
      (∑ i : Fin d, ∫ x in U, (J x i * φ.partialDeriv i x) *
        (1 - pointRemovalCutoff (ε n) x)) -
      (∑ i : Fin d, ∫ x in U, J x i * φ x *
        classicalGradient (pointRemovalCutoff (ε n)) x i))
      atTop (nhds (∑ i : Fin d, ∫ x in U, J x i * φ.partialDeriv i x)) := by
    simpa only [Finset.sum_const_zero, sub_zero] using hAsum.sub hEsum
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have hlim : (∑ i : Fin d, ∫ x in U, J x i * φ.partialDeriv i x) = 0 := by
    exact tendsto_nhds_unique hdiff
      (hzero.congr' (Filter.Eventually.of_forall fun n => (hid n).symm))
  rw [show (∫ x in U, vecDot (J x) (classicalGradient φ x)) =
      ∑ i : Fin d, ∫ x in U, J x i * φ.partialDeriv i x by
    simp only [vecDot, WeakTestFunction.partialDeriv, classicalGradient_apply]
    exact integral_finsetSum Finset.univ (fun i _ => hOrd i)]
  exact hlim

end

end PDE
