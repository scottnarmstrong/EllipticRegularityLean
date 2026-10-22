module

public import PDEFoundation.Sobolev.Inequalities.SobolevWholeSpaceCutoff
public import PDEFoundation.Sobolev.W1p.ZeroBoundary

/-!
# Smooth compactly supported density in `W^{1,p}(ℝ^d)`

For `1 ≤ p < ∞`, every representative-level `W^{1,p}(ℝ^d)` function admits a
supported smooth approximation: the approximants are the dilated cutoff times the
whole-space mollification, `ψ_n = χ_{R_n} · (K_{a_n} ⋆ u)`.  The coordinate
gradients converge in the same exponent because `∂_i (K ⋆ u) = K ⋆ g_i`.
-/

@[expose] public section

open scoped ENNReal Convolution Topology

namespace PDE

open Filter MeasureTheory

variable {d : ℕ}

private theorem wholeSpaceMollify_data {p : ℝ≥0∞} (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    {f : Vec d → ℝ} (hf : MemLp f p volume) {a : ℝ} (ha : 0 < a) :
    ContDiff ℝ (⊤ : ℕ∞) (wholeSpaceMollify a f) ∧
      eLpNorm (wholeSpaceMollify a f) p volume ≤ eLpNorm f p volume :=
  let h := contDiff_memLp_convolution_scaledConvexApproxKernel
    (isConvexApproxKernel_unitConvexApproxKernel (d := d)) ha hp hpTop hf
  ⟨h.1, h.2.2⟩

/-- Every `W^{1,p}(ℝ^d)` representative, `1 ≤ p < ∞`, has a supported smooth
approximation by cutoff mollifications. -/
theorem W1pFunction.hasSupportedSmoothApproximation_univ {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) (u : W1pFunction (Set.univ : Set (Vec d)) p) :
    u.HasSupportedSmoothApproximation := by
  have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have hu : MemLp u.toFun p volume := by
    have := u.memLp
    unfold MemLpOn volumeOn at this
    rwa [Measure.restrict_univ] at this
  have hg : ∀ i, MemLp (fun x => u.grad x i) p volume := fun i => by
    have := u.gradMemLp i
    unfold MemLpOn volumeOn at this
    rwa [Measure.restrict_univ] at this
  let a : ℕ → ℝ := unitConvexApproxScale
  let R : ℕ → ℝ := fun n => 2 * ((n : ℝ) + 1)
  have hR : ∀ n, 0 < R n := fun n => by positivity
  have hRt : Tendsto R atTop atTop :=
    tendsto_atTop_mono (fun n => by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      simp only [R]; linarith) tendsto_natCast_atTop_atTop
  have ha0 : Tendsto a atTop (𝓝 0) := tendsto_unitConvexApproxScale_zero
  let M : ℕ → Vec d → ℝ := fun n => wholeSpaceMollify (a n) u.toFun
  let G : ℕ → Fin d → Vec d → ℝ := fun n i => wholeSpaceMollify (a n) (fun x => u.grad x i)
  have hMdata := fun n => wholeSpaceMollify_data hp hpTop hu (unitConvexApproxScale_pos n)
  have hM_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (M n) := fun n => (hMdata n).1
  have hM_lp : ∀ n, eLpNorm (M n) p volume ≤ eLpNorm u.toFun p volume := fun n => (hMdata n).2
  have hGdata := fun n i => wholeSpaceMollify_data hp hpTop (hg i) (unitConvexApproxScale_pos n)
  have hG_lp : ∀ n i, eLpNorm (G n i) p volume ≤ eLpNorm (fun x => u.grad x i) p volume :=
    fun n i => (hGdata n i).2
  have hMderiv : ∀ n i, euclideanCoordDeriv i (M n) = G n i := fun n i =>
    euclideanCoordDeriv_convolution_eq_of_hasWeakPartialDerivOn
      (hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport
        (unitConvexApproxScale_pos n))
      (contDiff_scaledConvexApproxKernel hρ _) (hu.locallyIntegrable hp) (u.hasWeakGradient i)
  have hcutC : ∀ n, Continuous (wholeSpaceCutoff (R n)) := fun n =>
    (contDiff_wholeSpaceCutoff (d := d) (R n)).continuous
  have hMC : ∀ n, Continuous (M n) := fun n => (hM_smooth n).continuous
  have hGC : ∀ n i, Continuous (G n i) := fun n i => (hGdata n i).1.continuous
  have hderivC : ∀ n i, AEStronglyMeasurable
      (euclideanCoordDeriv i (wholeSpaceCutoff (R n))) volume := fun n i =>
    (((contDiff_wholeSpaceCutoff (d := d) (R n)).continuous_fderiv (by simp)).clm_apply
      continuous_const).aestronglyMeasurable
  let ψ : ℕ → Vec d → ℝ := fun n => wholeSpaceCutoff (R n) * M n
  have hψ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n) := fun n =>
    (contDiff_wholeSpaceCutoff (d := d) (R n)).mul (hM_smooth n)
  have hψ_deriv : ∀ n i x, (fderiv ℝ (ψ n) x) (basisVec i) =
      wholeSpaceCutoff (R n) x * G n i x +
        M n x * euclideanCoordDeriv i (wholeSpaceCutoff (R n)) x := by
    intro n i x
    have h1 := ((contDiff_wholeSpaceCutoff (d := d) (R n)).differentiable (by simp)) x
    have h2 := ((hM_smooth n).differentiable (by simp)) x
    have : fderiv ℝ (ψ n) x = wholeSpaceCutoff (R n) x • fderiv ℝ (M n) x +
        M n x • fderiv ℝ (wholeSpaceCutoff (R n)) x := fderiv_mul h1 h2
    rw [this]
    have hm := congrFun (hMderiv n i) x
    simp only [euclideanCoordDeriv] at hm ⊢
    simp [hm]
  obtain ⟨Mi, hMi⟩ : ∃ Mi : Fin d → ℝ, ∀ i, ∀ R : ℝ, 0 < R → ∀ x : Vec d,
      |euclideanCoordDeriv i (wholeSpaceCutoff R) x| ≤ Mi i / R := by
    choose Mi hMi using fun i : Fin d => exists_abs_coord_deriv_wholeSpaceCutoff_le (d := d) i
    exact ⟨Mi, hMi⟩
  unfold W1pFunction.HasSupportedSmoothApproximation
  refine ⟨
    { approx := ψ
      approx_smooth := hψ_smooth
      approx_hasCompactSupport := fun n =>
        (hasCompactSupport_wholeSpaceCutoff (hR n)).mul_right
      approx_tsupport_subset := fun n => Set.subset_univ _
      tendsto_value := ?_
      tendsto_grad := ?_ }⟩
  · simp only [volumeOn, Measure.restrict_univ]
    have h1 := tendsto_eLpNorm_wholeSpaceMollify_sub hp hpTop hu
      (fun n => unitConvexApproxScale_pos n) (fun n => unitConvexApproxScale_le_one n) ha0
    have h2 := tendsto_eLpNorm_wholeSpaceCutoff_sub_one_mul hp hpTop hu hR hRt
    have hsum := h1.add h2
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun n => bot_le) (fun n => ?_)
    have hpt : ψ n - u.toFun = (fun x => wholeSpaceCutoff (R n) x * (M n x - u.toFun x)) +
        (fun x => (wholeSpaceCutoff (R n) x - 1) * u.toFun x) := by
      funext x; simp only [Pi.sub_apply, Pi.add_apply, ψ, Pi.mul_apply]; ring
    rw [hpt]
    refine (eLpNorm_add_le hp).trans (add_le_add ?_ le_rfl)
    · refine eLpNorm_mono
        ((hcutC n).aestronglyMeasurable.mul
          ((hMC n).aestronglyMeasurable.sub hu.aestronglyMeasurable)) (fun x => ?_)
      simp only [norm_mul, Real.norm_eq_abs, Pi.sub_apply]
      calc |wholeSpaceCutoff (R n) x| * |M n x - u.toFun x|
          ≤ 1 * |M n x - u.toFun x| := by
            gcongr
            rw [abs_of_nonneg (wholeSpaceCutoff_nonneg _ _)]
            exact wholeSpaceCutoff_le_one _ _
        _ = _ := by rw [one_mul]
  · intro i
    simp only [volumeOn, Measure.restrict_univ]
    have h1 := tendsto_eLpNorm_wholeSpaceMollify_sub hp hpTop (hg i)
      (fun n => unitConvexApproxScale_pos n) (fun n => unitConvexApproxScale_le_one n) ha0
    have h2 := tendsto_eLpNorm_wholeSpaceCutoff_sub_one_mul hp hpTop (hg i) hR hRt
    have hc : Tendsto (fun n => Mi i / R n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hRt
    have hc' : Tendsto (fun n => ‖Mi i / R n‖ₑ) atTop (𝓝 0) := by
      simpa only [Function.comp_def, enorm_zero] using
        (continuous_enorm.tendsto (0 : ℝ)).comp hc
    have h3 : Tendsto (fun n => ‖Mi i / R n‖ₑ * eLpNorm u.toFun p volume) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.mul_const hc' (Or.inr hu.eLpNorm_ne_top)
      simpa using this
    have hsum := (h1.add h2).add h3
    simp only [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun n => bot_le) (fun n => ?_)
    have hpt : (fun x => (fderiv ℝ (ψ n) x) (basisVec i) - u.grad x i) =
        ((fun x => wholeSpaceCutoff (R n) x * (G n i x - u.grad x i)) +
          (fun x => (wholeSpaceCutoff (R n) x - 1) * u.grad x i)) +
          (fun x => M n x * euclideanCoordDeriv i (wholeSpaceCutoff (R n)) x) := by
      funext x; simp only [Pi.add_apply, hψ_deriv]; ring
    rw [hpt]
    refine (eLpNorm_add_le hp).trans (add_le_add ((eLpNorm_add_le hp).trans (add_le_add ?_ le_rfl)) ?_)
    · refine eLpNorm_mono
        ((hcutC n).aestronglyMeasurable.mul
          ((hGC n i).aestronglyMeasurable.sub (hg i).aestronglyMeasurable)) (fun x => ?_)
      simp only [norm_mul, Real.norm_eq_abs, Pi.sub_apply]
      calc |wholeSpaceCutoff (R n) x| * |G n i x - u.grad x i|
          ≤ 1 * |G n i x - u.grad x i| := by
            gcongr
            rw [abs_of_nonneg (wholeSpaceCutoff_nonneg _ _)]
            exact wholeSpaceCutoff_le_one _ _
        _ = _ := by rw [one_mul]
    · calc eLpNorm (fun x => M n x * euclideanCoordDeriv i (wholeSpaceCutoff (R n)) x) p volume
          ≤ eLpNorm ((Mi i / R n) • M n) p volume := by
            refine eLpNorm_mono
              ((hMC n).aestronglyMeasurable.mul
                (hderivC n i)) (fun x => ?_)
            simp only [norm_mul, Real.norm_eq_abs, Pi.smul_apply, smul_eq_mul]
            have hb := hMi i (R n) (hR n) x
            have hnn : 0 ≤ Mi i / R n := le_trans (abs_nonneg _) hb
            rw [abs_of_nonneg hnn]
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
        _ = ‖Mi i / R n‖ₑ * eLpNorm (M n) p volume := eLpNorm_const_smul _ _ _ _
        _ ≤ ‖Mi i / R n‖ₑ * eLpNorm u.toFun p volume := by gcongr; exact hM_lp n

end PDE
