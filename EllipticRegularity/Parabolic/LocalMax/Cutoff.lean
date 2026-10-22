module

public import EllipticRegularity.Parabolic.LocalMax.SliceSobolev
public import EllipticRegularity.Parabolic.WeakSlice.Ramp
public import PDEFoundation.Sobolev.Cutoff.Ball

/-!
# Space-time cutoffs between nested parabolic cylinders

For `0 ≤ r < ρ` and `T < T'` the product `η(x,t) = ξ(x) ϑ(t)` of the canonical round-ball cutoff
`ξ` (one on `B_r`, supported in `B_ρ`) and the time ramp
`ϑ(t) = smoothTransition((t - T - δ)/δ)`, `δ = (T'-T)/2`, is smooth, takes values in `[0,1]`,
vanishes for `t ≤ T + δ` and off a compact subset of `B_ρ`, equals one on `B_r × [T', ∞)`, and
satisfies `|∂ₜη| ≤ B/(T'-T)`, `|∇η|² ≤ 1024/(ρ-r)²` with a universal constant `B`.
-/

@[expose] public section

namespace PDE.Parabolic.LocalMax

open MeasureTheory Set

variable {d : ℕ}

/-- The time derivative of a differentiable space-time function is the derivative of its
time slice. -/
theorem fderiv_timeSlice_apply {η : Vec d × ℝ → ℝ} (hη : Differentiable ℝ η) (x : Vec d)
    (t : ℝ) : fderiv ℝ η (x, t) (0, 1) = deriv (fun s => η (x, s)) t := by
  have h1 : HasDerivAt (fun s : ℝ => (x, s)) ((0 : Vec d), (1 : ℝ)) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  exact (((hη (x, t)).hasFDerivAt.comp_hasDerivAt t h1).deriv).symm

/-- A universal bound for the derivative of the smooth transition profile. -/
theorem exists_abs_deriv_smoothTransition_le :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s, |deriv Real.smoothTransition s| ≤ B := by
  obtain ⟨B, hB0, hB⟩ := exists_abs_le_of_continuous_of_eq_zero_off
    PDE.Parabolic.WeakSlice.rampDeriv_continuous isCompact_Icc
    (fun s hs => PDE.Parabolic.WeakSlice.rampDeriv_eq_zero_of_notMem hs)
  exact ⟨B, hB0, hB⟩

/-- The time ramp `ϑ(t) = smoothTransition((t - T - δ)/δ)`. -/
noncomputable def cylTimeRamp (T δ : ℝ) (t : ℝ) : ℝ := Real.smoothTransition ((t - T - δ) / δ)

/-- The product cutoff `ξ(x) ϑ(t)`. -/
noncomputable def cylCutoff (r ρ T T' : ℝ) (z : Vec d × ℝ) : ℝ :=
  canonicalBallCutoff (0 : Vec d) r ρ z.1 * cylTimeRamp T ((T' - T) / 2) z.2

theorem cylTimeRamp_contDiff (T δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (cylTimeRamp T δ) :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

theorem cylTimeRamp_hasDerivAt (T δ t : ℝ) :
    HasDerivAt (cylTimeRamp T δ) (deriv Real.smoothTransition ((t - T - δ) / δ) * (1 / δ)) t := by
  have h1 : HasDerivAt (fun t : ℝ => (t - T - δ) / δ) (1 / δ) t := by
    simpa using (((hasDerivAt_id t).sub_const T).sub_const δ).div_const δ
  exact ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt.comp
    t h1

theorem cylCutoff_contDiff {r ρ : ℝ} (hr : 0 ≤ r) (hrρ : r < ρ) (T T' : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (cylCutoff (d := d) r ρ T T') :=
  ((canonicalBallCutoff_smooth (0 : Vec d) hr hrρ).comp contDiff_fst).mul
    ((cylTimeRamp_contDiff T _).comp contDiff_snd)

theorem cylCutoff_nonneg (r ρ T T' : ℝ) (z : Vec d × ℝ) : 0 ≤ cylCutoff r ρ T T' z :=
  mul_nonneg (canonicalBallCutoff_nonneg _ _ _ _) (Real.smoothTransition.nonneg _)

theorem cylCutoff_le_one (r ρ T T' : ℝ) (z : Vec d × ℝ) : cylCutoff r ρ T T' z ≤ 1 :=
  (mul_le_mul (canonicalBallCutoff_le_one _ _ _ _) (Real.smoothTransition.le_one _)
    (Real.smoothTransition.nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem cylCutoff_eq_zero_of_notMem {r ρ T T' : ℝ} {x : Vec d}
    (hx : x ∉ tsupport (canonicalBallCutoff (0 : Vec d) r ρ)) (t : ℝ) :
    cylCutoff r ρ T T' (x, t) = 0 := by
  simp [cylCutoff, image_eq_zero_of_notMem_tsupport hx]

theorem cylCutoff_eq_zero_of_le {r ρ T T' : ℝ} (hTT' : T < T') (x : Vec d) {t : ℝ}
    (ht : t ≤ T + (T' - T) / 2) : cylCutoff r ρ T T' (x, t) = 0 := by
  have hδ : 0 < (T' - T) / 2 := by linarith
  have : cylTimeRamp T ((T' - T) / 2) t = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  simp [cylCutoff, this]

theorem cylCutoff_eq_one {r ρ T T' : ℝ} (hr : 0 ≤ r) (hrρ : r < ρ) (hTT' : T < T') {x : Vec d}
    (hx : x ∈ euclideanBall (0 : Vec d) r) {t : ℝ} (ht : T' ≤ t) :
    cylCutoff r ρ T T' (x, t) = 1 := by
  have hδ : 0 < (T' - T) / 2 := by linarith
  have : cylTimeRamp T ((T' - T) / 2) t = 1 := by
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ hδ]
    linarith
  simp [cylCutoff, this, canonicalBallCutoff_eq_one_on_inner hr hrρ hx]

theorem parTimeDeriv_cylCutoff (r ρ T T' : ℝ) (x : Vec d) (t : ℝ) {r' : ℝ} (hr : 0 ≤ r)
    (hrρ : r < ρ) (_hr' : r' = r) :
    parTimeDeriv (cylCutoff r ρ T T') (x, t) =
      canonicalBallCutoff (0 : Vec d) r ρ x *
        (deriv Real.smoothTransition ((t - T - (T' - T) / 2) / ((T' - T) / 2)) *
          (1 / ((T' - T) / 2))) := by
  have hdiff : Differentiable ℝ (cylCutoff (d := d) r ρ T T') :=
    (cylCutoff_contDiff hr hrρ T T').differentiable (by simp)
  unfold parTimeDeriv
  rw [fderiv_timeSlice_apply hdiff]
  have h := ((cylTimeRamp_hasDerivAt T ((T' - T) / 2) t).const_mul
    (canonicalBallCutoff (0 : Vec d) r ρ x))
  exact h.deriv

theorem abs_parTimeDeriv_cylCutoff_le {B : ℝ} (hB : ∀ s, |deriv Real.smoothTransition s| ≤ B)
    {r ρ T T' : ℝ} (hr : 0 ≤ r) (hrρ : r < ρ) (hTT' : T < T') (z : Vec d × ℝ) :
    |parTimeDeriv (cylCutoff r ρ T T') z| ≤ 2 * B / (T' - T) := by
  obtain ⟨x, t⟩ := z
  have hδ : 0 < T' - T := by linarith
  rw [parTimeDeriv_cylCutoff r ρ T T' x t hr hrρ rfl]
  have hξ0 := canonicalBallCutoff_nonneg (0 : Vec d) r ρ x
  have hξ1 := canonicalBallCutoff_le_one (0 : Vec d) r ρ x
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  rw [abs_mul, abs_mul, abs_of_nonneg hξ0,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / ((T' - T) / 2))]
  calc canonicalBallCutoff (0 : Vec d) r ρ x *
        (|deriv Real.smoothTransition ((t - T - (T' - T) / 2) / ((T' - T) / 2))| *
          (1 / ((T' - T) / 2)))
      ≤ 1 * (B * (1 / ((T' - T) / 2))) := by
        gcongr
        exact hB _
    _ = 2 * B / (T' - T) := by
        field_simp

theorem parSpaceGrad_cylCutoff {r ρ : ℝ} (hr : 0 ≤ r) (hrρ : r < ρ) (T T' : ℝ) (x : Vec d)
    (t : ℝ) :
    parSpaceGrad (cylCutoff r ρ T T') (x, t) =
      cylTimeRamp T ((T' - T) / 2) t • classicalGradient (canonicalBallCutoff (0 : Vec d) r ρ) x := by
  have hdiff : Differentiable ℝ (cylCutoff (d := d) r ρ T T') :=
    (cylCutoff_contDiff hr hrρ T T').differentiable (by simp)
  have hξ : DifferentiableAt ℝ (canonicalBallCutoff (0 : Vec d) r ρ) x :=
    ((canonicalBallCutoff_smooth (0 : Vec d) hr hrρ).differentiable (by simp)) x
  funext i
  simp only [parSpaceGrad, Pi.smul_apply, smul_eq_mul, classicalGradient_apply]
  rw [← fderiv_slice_apply hdiff]
  have hfun : (fun y => cylCutoff (d := d) r ρ T T' (y, t)) =
      fun y => canonicalBallCutoff (0 : Vec d) r ρ y * cylTimeRamp T ((T' - T) / 2) t := rfl
  rw [hfun, fderiv_mul_const hξ]
  simp

theorem vecNormSq_parSpaceGrad_cylCutoff_le {r ρ : ℝ} (hr : 0 ≤ r) (hrρ : r < ρ) (T T' : ℝ)
    (z : Vec d × ℝ) :
    vecNormSq (parSpaceGrad (cylCutoff r ρ T T') z) ≤ 1024 / (ρ - r) ^ 2 := by
  obtain ⟨x, t⟩ := z
  rw [parSpaceGrad_cylCutoff hr hrρ, vecNormSq_smul]
  have hθ0 := Real.smoothTransition.nonneg ((t - T - (T' - T) / 2) / ((T' - T) / 2))
  have hθ1 := Real.smoothTransition.le_one ((t - T - (T' - T) / 2) / ((T' - T) / 2))
  have hgrad := canonicalBallCutoff_gradient_bound (x₀ := (0 : Vec d)) hr hrρ x
  have hsq : vecNormSq (classicalGradient (canonicalBallCutoff (0 : Vec d) r ρ) x) ≤
      (32 / (ρ - r)) ^ 2 := by
    rw [← vecEuclideanNorm_sq]
    exact pow_le_pow_left₀ (vecEuclideanNorm_nonneg _) hgrad 2
  have hθsq : cylTimeRamp T ((T' - T) / 2) t ^ 2 ≤ 1 := by
    unfold cylTimeRamp
    nlinarith
  calc cylTimeRamp T ((T' - T) / 2) t ^ 2 *
        vecNormSq (classicalGradient (canonicalBallCutoff (0 : Vec d) r ρ) x)
      ≤ 1 * (32 / (ρ - r)) ^ 2 :=
        mul_le_mul hθsq hsq (vecNormSq_nonneg _) zero_le_one
    _ = 1024 / (ρ - r) ^ 2 := by rw [div_pow]; ring

end PDE.Parabolic.LocalMax
