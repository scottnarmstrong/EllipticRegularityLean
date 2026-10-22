module

public import PDEFoundation.Measure.FiniteMeasureOperatorInterpolation
public import PDEFoundation.Sobolev.W1p.EuclideanGradient

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

private def coordinateInjection {d : ℕ} (μ : Measure α) (j : Fin d) :
    Lp ℝ 2 μ →L[ℝ] Lp (HilbertVec d) 2 μ :=
  (ContinuousLinearMap.toSpanSingleton ℝ (basisVec j).toHilbertVec).compLpL 2 μ

private def coordinateProjection {d : ℕ} (ν : Measure β) (i : Fin d) :
    Lp (HilbertVec d) 2 ν →L[ℝ] Lp ℝ 2 ν :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).compLpL 2 ν

private def coordinateOperator {d : ℕ} (μ : Measure α) (ν : Measure β)
    (T : Lp (HilbertVec d) 2 μ →L[ℝ] Lp (HilbertVec d) 2 ν)
    (i j : Fin d) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν :=
  (coordinateProjection ν i).comp (T.comp (coordinateInjection μ j))

private theorem coordinateInjection_ae {d : ℕ} (μ : Measure α) (j : Fin d)
    (f : Lp ℝ 2 μ) :
    ⇑(coordinateInjection μ j f) =ᵐ[μ]
      fun x => (f x • basisVec j).toHilbertVec := by
  simpa only [coordinateInjection, ContinuousLinearMap.toSpanSingleton_apply]
    using! (ContinuousLinearMap.toSpanSingleton ℝ
      (basisVec j).toHilbertVec).coeFn_compLpL f

private theorem coordinateProjection_ae {d : ℕ} (ν : Measure β) (i : Fin d)
    (f : Lp (HilbertVec d) 2 ν) :
    ⇑(coordinateProjection ν i f) =ᵐ[ν] fun x => f x i := by
  simpa only [coordinateProjection] using!
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).coeFn_compLpL f

private theorem eLpNorm_coordinateInjection {d : ℕ} (μ : Measure α)
    (j : Fin d) (f : Lp ℝ 2 μ) (q : ℝ≥0∞) :
    eLpNorm (coordinateInjection μ j f) q μ = eLpNorm f q μ := by
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [coordinateInjection_ae μ j f] with x hx
  rw [hx]
  rw [← Vec.vecEuclideanNorm_eq_norm_toHilbertVec,
    vecEuclideanNorm_smul, vecEuclideanNorm_basisVec, mul_one]
  exact (Real.norm_eq_abs _).symm

private theorem eLpNorm_coordinateProjection_le {d : ℕ} (ν : Measure β)
    (i : Fin d) (f : Lp (HilbertVec d) 2 ν) (q : ℝ≥0∞) :
    eLpNorm (coordinateProjection ν i f) q ν ≤ eLpNorm f q ν := by
  apply eLpNorm_mono_ae (Lp.aestronglyMeasurable _)
  filter_upwards [coordinateProjection_ae ν i f] with x hx
  rw [hx]
  exact PiLp.norm_apply_le (f x) i

private theorem coeFn_finset_sum {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (μ : Measure α) (p : ℝ≥0∞) (s : Finset (Fin d))
    (f : Fin d → Lp E p μ) :
    ⇑(∑ i ∈ s, f i) =ᵐ[μ] fun x => ∑ i ∈ s, (f i : α → E) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using! Lp.coeFn_zero E p μ
  | @insert a s ha ih =>
      filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x hadd hsum
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, Pi.add_apply, hsum]

private theorem memLp_finset_sum {ι : Type*} {E : Type*}
    [NormedAddCommGroup E] {μ : Measure α} {q : ℝ≥0∞}
    (s : Finset ι) (f : ι → α → E)
    (hf : ∀ i ∈ s, MemLp (f i) q μ) :
    MemLp (∑ i ∈ s, f i) q μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem sum_coordinateInjection_projection {d : ℕ} (μ : Measure α)
    (f : Lp (HilbertVec d) 2 μ) :
    ∑ j : Fin d, coordinateInjection μ j (coordinateProjection μ j f) = f := by
  apply Lp.ext
  have hsum := coeFn_finset_sum μ 2 Finset.univ
    (fun j => coordinateInjection μ j (coordinateProjection μ j f))
  have hall : ∀ᵐ x ∂μ, ∀ j : Fin d,
      coordinateInjection μ j (coordinateProjection μ j f) x =
        (f x j • basisVec j).toHilbertVec := by
    rw [ae_all_iff]
    intro j
    filter_upwards [coordinateInjection_ae μ j (coordinateProjection μ j f),
      coordinateProjection_ae μ j f] with x hx hcoord
    rw [hx, hcoord]
  filter_upwards [hall, hsum] with x hx hsumx
  rw [hsumx]
  simp only [hx]
  ext i
  rw [WithLp.ofLp_sum]
  rw [Finset.sum_apply]
  simp only [Vec.toHilbertVec_apply]
  change (∑ j : Fin d, (f x j • basisVec j) i) = f x i
  rw [Finset.sum_eq_single i]
  · simp [basisVec]
  · intro j _ hji
    simp [basisVec, hji]
  · simp

/-- Finite-dimensional Hilbert-valued operators interpolate between the
quadratic and fourth-power endpoints, with an explicit dimension-only loss. -/
theorem memLp_and_eLpNorm_hilbertVector_operator_le_of_two_four
    {d : ℕ} (hd : 0 < d) (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (T : Lp (HilbertVec d) 2 μ →L[ℝ] Lp (HilbertVec d) 2 ν)
    {p M : ℝ} (hp : 2 ≤ p) (hpFour : p ≤ 4) (hM : 1 ≤ M)
    (hTwo : ∀ f : Lp (HilbertVec d) 2 μ, MemLp f 2 μ →
      eLpNorm (T f) 2 ν ≤ ENNReal.ofReal M * eLpNorm f 2 μ)
    (hFour : ∀ f : Lp (HilbertVec d) 2 μ, MemLp f 4 μ →
      eLpNorm (T f) 4 ν ≤ ENNReal.ofReal M * eLpNorm f 4 μ)
    (f : Lp (HilbertVec d) 2 μ)
    (hfp : MemLp f (ENNReal.ofReal p) μ) :
    MemLp (T f) (ENNReal.ofReal p) ν ∧
      eLpNorm (T f) (ENNReal.ofReal p) ν ≤
        ENNReal.ofReal ((d : ℝ) ^ 2 * M) *
          eLpNorm f (ENNReal.ofReal p) μ := by
  let fj : Fin d → Lp ℝ 2 μ := fun j => coordinateProjection μ j f
  have hfj (j : Fin d) :
      MemLp (fj j) (ENNReal.ofReal p) μ := by
    apply hfp.mono (Lp.aestronglyMeasurable (fj j))
    filter_upwards [coordinateProjection_ae μ j f] with x hx
    rw [hx]
    exact PiLp.norm_apply_le (f x) j
  have hTwoS (i j : Fin d) (g : Lp ℝ 2 μ) (_hg : MemLp g 2 μ) :
      eLpNorm (coordinateOperator μ ν T i j g) 2 ν ≤
        ENNReal.ofReal M * eLpNorm g 2 μ := by
    change eLpNorm (coordinateProjection ν i
      (T (coordinateInjection μ j g))) 2 ν ≤ _
    calc
      eLpNorm (coordinateProjection ν i
          (T (coordinateInjection μ j g))) 2 ν ≤
          eLpNorm (T (coordinateInjection μ j g)) 2 ν :=
        eLpNorm_coordinateProjection_le ν i _ 2
      _ ≤ ENNReal.ofReal M *
          eLpNorm (coordinateInjection μ j g) 2 μ :=
        hTwo _ (Lp.memLp _)
      _ = ENNReal.ofReal M * eLpNorm g 2 μ := by
        rw [eLpNorm_coordinateInjection]
  have hFourS (i j : Fin d) (g : Lp ℝ 2 μ) (hg : MemLp g 4 μ) :
      eLpNorm (coordinateOperator μ ν T i j g) 4 ν ≤
        ENNReal.ofReal M * eLpNorm g 4 μ := by
    have hginj : MemLp (coordinateInjection μ j g) 4 μ := by
      rw [memLp_iff, eLpNorm_coordinateInjection]
      exact hg.eLpNorm_lt_top
    change eLpNorm (coordinateProjection ν i
      (T (coordinateInjection μ j g))) 4 ν ≤ _
    calc
      eLpNorm (coordinateProjection ν i
          (T (coordinateInjection μ j g))) 4 ν ≤
          eLpNorm (T (coordinateInjection μ j g)) 4 ν :=
        eLpNorm_coordinateProjection_le ν i _ 4
      _ ≤ ENNReal.ofReal M *
          eLpNorm (coordinateInjection μ j g) 4 μ := hFour _ hginj
      _ = ENNReal.ofReal M * eLpNorm g 4 μ := by
        rw [eLpNorm_coordinateInjection]
  have hS (i j : Fin d) :
      MemLp (coordinateOperator μ ν T i j (fj j))
          (ENNReal.ofReal p) ν ∧
        eLpNorm (coordinateOperator μ ν T i j (fj j))
            (ENNReal.ofReal p) ν ≤
          ENNReal.ofReal M * eLpNorm (fj j) (ENNReal.ofReal p) μ :=
    memLp_and_eLpNorm_operator_le_of_two_four μ ν
      (coordinateOperator μ ν T i j) hp hpFour hM
      (hTwoS i j) (hFourS i j) (fj j) (hfj j)
  have hcoordEq (i : Fin d) :
      coordinateProjection ν i (T f) =
        ∑ j : Fin d, coordinateOperator μ ν T i j (fj j) := by
    rw [← sum_coordinateInjection_projection μ f]
    simp only [map_sum, coordinateOperator, ContinuousLinearMap.comp_apply, fj]
  have hcoordMem (i : Fin d) :
      MemLp (fun x => T f x i) (ENNReal.ofReal p) ν := by
    have hsumFun : MemLp
        (∑ j : Fin d, fun x => coordinateOperator μ ν T i j (fj j) x)
        (ENNReal.ofReal p) ν :=
      memLp_finset_sum Finset.univ _ (fun j _ => (hS i j).1)
    have hproj : MemLp (coordinateProjection ν i (T f))
        (ENNReal.ofReal p) ν := by
      rw [hcoordEq i]
      apply hsumFun.ae_eq
      filter_upwards [coeFn_finset_sum ν 2 Finset.univ
        (fun j => coordinateOperator μ ν T i j (fj j))] with x hx
      simpa only [Finset.sum_apply] using hx.symm
    exact hproj.ae_eq (coordinateProjection_ae ν i (T f))
  have hout : MemLp (T f) (ENNReal.ofReal p) ν := by
    exact (memLp_piLp_iff (f := (T f : β → HilbertVec d))
      (p := ENNReal.ofReal p) (μ := ν)).mpr hcoordMem
  refine ⟨hout, ?_⟩
  have hvector :
      eLpNorm (T f) (ENNReal.ofReal p) ν ≤
        ∑ i : Fin d, eLpNorm (fun x => T f x i)
          (ENNReal.ofReal p) ν := by
    calc
      eLpNorm (T f) (ENNReal.ofReal p) ν ≤
          eLpNorm (fun x => ∑ i : Fin d, |T f x i|)
            (ENNReal.ofReal p) ν := by
        apply eLpNorm_mono_ae (Lp.aestronglyMeasurable _)
        filter_upwards with x
        rw [HilbertVec.norm_eq_vecEuclideanNorm, Real.norm_eq_abs,
          abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
        exact vecEuclideanNorm_le_sum_abs (T f x).toVec
      _ ≤ ∑ i : Fin d, eLpNorm (fun x => T f x i)
          (ENNReal.ofReal p) ν := by
        calc
          _ ≤ ∑ i : Fin d, eLpNorm (fun x => |T f x i|)
              (ENNReal.ofReal p) ν := by
            rw [← Finset.sum_fn]
            exact eLpNorm_sum_le
              (by rw [← ENNReal.ofReal_one]
                  exact ENNReal.ofReal_le_ofReal (by linarith))
          _ = _ := by
            apply Finset.sum_congr rfl
            intro i _
            simpa only [Real.norm_eq_abs] using!
              (eLpNorm_norm (fun x => T f x i)
                (p := ENNReal.ofReal p) (μ := ν) (hcoordMem i).aestronglyMeasurable)
  calc
    eLpNorm (T f) (ENNReal.ofReal p) ν ≤
        ∑ i : Fin d, eLpNorm (fun x => T f x i)
          (ENNReal.ofReal p) ν := hvector
    _ = ∑ i : Fin d, eLpNorm (coordinateProjection ν i (T f))
          (ENNReal.ofReal p) ν := by
      apply Finset.sum_congr rfl
      intro i _
      exact eLpNorm_congr_ae (coordinateProjection_ae ν i (T f) |>.symm)
    _ = ∑ i : Fin d, eLpNorm
          (∑ j : Fin d, coordinateOperator μ ν T i j (fj j))
          (ENNReal.ofReal p) ν := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hcoordEq i]
      apply eLpNorm_congr_ae
      filter_upwards [coeFn_finset_sum ν 2 Finset.univ
        (fun j => coordinateOperator μ ν T i j (fj j))] with x hx
      simpa only [Finset.sum_apply] using hx
    _ ≤ ∑ i : Fin d, ∑ j : Fin d,
          eLpNorm (coordinateOperator μ ν T i j (fj j))
            (ENNReal.ofReal p) ν := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ = eLpNorm (∑ j : Fin d, fun x =>
              coordinateOperator μ ν T i j (fj j) x)
              (ENNReal.ofReal p) ν := by
          apply eLpNorm_congr_ae
          filter_upwards [coeFn_finset_sum ν 2 Finset.univ
            (fun j => coordinateOperator μ ν T i j (fj j))] with x hx
          simp only [Finset.sum_apply] at hx ⊢
        _ ≤ _ := eLpNorm_sum_le
         
          (by rw [← ENNReal.ofReal_one]
              exact ENNReal.ofReal_le_ofReal (by linarith))
    _ ≤ ∑ i : Fin d, ∑ j : Fin d,
          (ENNReal.ofReal M * eLpNorm (fj j) (ENNReal.ofReal p) μ) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact (hS i j).2
    _ ≤ ∑ i : Fin d, ∑ j : Fin d,
          (ENNReal.ofReal M * eLpNorm f (ENNReal.ofReal p) μ) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      gcongr
      exact eLpNorm_coordinateProjection_le μ j f _
    _ = ENNReal.ofReal ((d : ℝ) ^ 2 * M) *
          eLpNorm f (ENNReal.ofReal p) μ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (d : ℝ) ^ 2)]
      norm_num
      ring

end
end PDE
