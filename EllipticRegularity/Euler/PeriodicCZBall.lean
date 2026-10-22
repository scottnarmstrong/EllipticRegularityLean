module

public import EllipticRegularity.CalderonZygmund.GeneralProof
public import PDEFoundation.Euler.PeriodicCZWeak
public import PDEFoundation.Ambient.RadialEllipticity
public import PDEFoundation.Ambient.MatrixPerturbation

/-!
# The ball CZ estimate for constant coefficients, in plain real integrals

The general-background CZ estimate (`PDE.CZGeneralProof.result`, constant linear in the
exponent) specialised to `A = 1`, `d = 2`, and converted from normalized `L^p` means to
`∫_{B_{1/2}} |∇g|^p ≤ |B_{1/2}| (C (√(avg_{B₁} |∇g|²) + p M))^p` for smooth `g` with `Δ g = -∂_k h`, `|h| ≤ M`.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory

namespace PDE

/-- From a normalized `L^p` mean bound to a plain integral bound. -/
theorem integral_rpow_le_of_lpMeanNormOn_le {U : Set (Vec 2)} (hUpos : 0 < volume U)
    (hUtop : volume U < ⊤) {p : ℝ} (hp : 1 ≤ p) {f : Vec 2 → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hf : MemLp f (ENNReal.ofReal p) (volumeOn U)) {R : ℝ}
    (h : lpMeanNormOn U (ENNReal.ofReal p) f (memLp_normalizedVolumeOn_of_memLpOn hf hUpos) ≤ R) :
    ∫ x in U, f x ^ p ≤ (volume U).toReal * R ^ p := by
  have hp0 : 0 < p := by linarith
  have hne0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hnetop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have htr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  rw [lpMeanNormOn_eq_toReal, eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn hUtop] at h
  have hE : eLpNormOn U (ENNReal.ofReal p) f =
      ENNReal.ofReal ((∫ x in U, ‖f x‖ ^ p) ^ (1 / p)) := by
    unfold eLpNormOn
    have := hf.eLpNorm_eq_integral_rpow_norm hne0 hnetop
    rw [htr] at this
    simpa only [volumeOn, one_div] using this
  rw [hE, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h
  have hvol : 0 < (volume U).toReal := ENNReal.toReal_pos hUpos.ne' hUtop.ne
  have h0 : (1 / ENNReal.ofReal p).toReal = 1 / p := by
    rw [ENNReal.toReal_div, ENNReal.toReal_one, htr]
  have hexp : ((volume U)⁻¹ ^ (1 / ENNReal.ofReal p).toReal).toReal =
      ((volume U).toReal) ^ (-(1 / p)) := by
    rw [h0, ← ENNReal.toReal_rpow, ENNReal.toReal_inv, Real.inv_rpow hvol.le, ← Real.rpow_neg hvol.le]
  rw [hexp] at h
  have hI : ∫ x in U, ‖f x‖ ^ p = ∫ x in U, f x ^ p :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [abs_of_nonneg (hf0 x)])
  rw [hI] at h
  set I := ∫ x in U, f x ^ p with hIdef
  have hI0 : 0 ≤ I := setIntegral_nonneg_of_ae_restrict (Filter.Eventually.of_forall fun x => by
    exact Real.rpow_nonneg (hf0 x) _) 
  have hR0 : 0 ≤ R := le_trans (by positivity) h
  have h2 : I ^ (1 / p) ≤ (volume U).toReal ^ (1 / p) * R := by
    have := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hvol.le (1 / p))
    rwa [← mul_assoc, ← Real.rpow_add hvol, show 1 / p + -(1 / p) = 0 by ring, Real.rpow_zero,
      one_mul] at this
  have h3 : (I ^ (1 / p)) ^ p ≤ ((volume U).toReal ^ (1 / p) * R) ^ p :=
    Real.rpow_le_rpow (Real.rpow_nonneg hI0 _) h2 hp0.le
  rwa [← Real.rpow_mul hI0, show 1 / p * p = 1 by field_simp, Real.rpow_one,
    Real.mul_rpow (Real.rpow_nonneg hvol.le _) hR0, ← Real.rpow_mul hvol.le,
    show 1 / p * p = 1 by field_simp, Real.rpow_one] at h3

theorem vecEuclideanNorm_unitForce (k : Fin 2) (h : Vec 2 → ℝ) (x : Vec 2) :
    vecEuclideanNorm (unitForce k h x) = |h x| := by
  rw [vecEuclideanNorm, ← Real.sqrt_sq_eq_abs]
  congr 1
  simp only [vecNormSq, vecDot, unitForce, Fin.sum_univ_two]
  fin_cases k <;> simp [sq]

theorem matVecMul_one' (x : Vec 2) : matVecMul (1 : Mat 2) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply]

theorem isEllipticMatrix_one_two : IsEllipticMatrix 1 1 (1 : Mat 2) := by
  simpa only [sub_zero, add_zero, zero_smul] using
    isEllipticMatrix_one_add_radialReflectionMatrix (d := 2)
      (delta := (0 : ℝ)) (by norm_num) (by norm_num) (0 : Vec 2)

/-- **Ball CZ estimate in plain integrals** (constant `C` absolute, linear in `p`). -/
theorem exists_ball_cz_integral :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p : ℝ, 2 ≤ p → ∀ (g h : Vec 2 → ℝ) (k : Fin 2) (M : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) g → ContDiff ℝ (⊤ : ℕ∞) h → 0 ≤ M → (∀ x, |h x| ≤ M) →
      (∀ x, torusLap g x = -pd k h x) →
      ∫ x in euclideanBall (0 : Vec 2) (1 / 2 : ℝ), vecEuclideanNorm (classicalGradient g x) ^ p ≤
        (volume (euclideanBall (0 : Vec 2) (1 / 2 : ℝ))).toReal *
          (C * (Real.sqrt (integralAverage (euclideanBall (0 : Vec 2) 1)
              (fun x => vecNormSq (classicalGradient g x))) + p * M)) ^ p := by
  obtain ⟨C, hC1, hCZ⟩ := CZGeneralProof.result 2 two_pos 1 le_rfl
  refine ⟨C, hC1, ?_⟩
  intro p hp g h k M hg hh hM hhM hlap
  have hB1pos : 0 < volume (euclideanBall (0 : Vec 2) 1) := volume_euclideanBall_pos _ (by norm_num)
  have hB1top : volume (euclideanBall (0 : Vec 2) 1) < ⊤ :=
    lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ (by norm_num))
  have hB2pos : 0 < volume (euclideanBall (0 : Vec 2) (1 / 2 : ℝ)) :=
    volume_euclideanBall_pos _ (by norm_num)
  have hB2top : volume (euclideanBall (0 : Vec 2) (1 / 2 : ℝ)) < ⊤ :=
    lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ (by norm_num))
  have : IsFiniteMeasure (volumeOn (euclideanBall (0 : Vec 2) 1)) :=
    ⟨by rw [volumeOn, Measure.restrict_apply_univ]; exact hB1top⟩
  have : IsProbabilityMeasure (normalizedVolumeOn (euclideanBall (0 : Vec 2) 1)) :=
    isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top hB1pos hB1top
  have hnorm : (fun x => vecEuclideanNorm (unitForce k h x)) = fun x => |h x| :=
    funext (vecEuclideanNorm_unitForce k h)
  have hFcoord : ∀ i : Fin 2, AEStronglyMeasurable (fun x => unitForce k h x i)
      (volumeOn (euclideanBall (0 : Vec 2) 1)) := by
    intro i
    refine Continuous.aestronglyMeasurable ?_
    by_cases hik : i = k
    · subst hik; simpa [unitForce] using hh.continuous
    · simpa [unitForce, Pi.single_apply, hik] using continuous_const
  have hF : MemLp (fun x => vecEuclideanNorm (unitForce k h x)) (ENNReal.ofReal p)
      (volumeOn (euclideanBall (0 : Vec 2) 1)) := by
    rw [hnorm]
    exact MemLp.of_bound (hh.continuous.abs.aestronglyMeasurable) M
      (Filter.Eventually.of_forall fun x => by simpa using hhM x)
  have hclose : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec 2) 1),
      IsMatrixPerturbationLE (1 / (C * p)) (1 : Mat 2) (fun i j => integralAverage
        (euclideanBall (0 : Vec 2) 1) (fun _ : Vec 2 => (1 : Mat 2) i j)) := by
    have hMean : (fun i j => integralAverage (euclideanBall (0 : Vec 2) 1)
        (fun _ : Vec 2 => (1 : Mat 2) i j)) = (1 : Mat 2) := by
      funext i j
      rw [← integral_normalizedVolumeOn_eq_integralAverage]
      simp
    rw [hMean]
    filter_upwards with x
    intro xi
    have hdelta : 0 ≤ 1 / (C * p) := by
      have : 0 < C * p := by positivity
      positivity
    simpa only [sub_self, matVecMul, Matrix.zero_apply, vecEuclideanNorm, vecNormSq, vecDot,
      Pi.zero_apply, zero_mul, Finset.sum_const_zero, Real.sqrt_zero] using
      mul_nonneg hdelta (vecEuclideanNorm_nonneg xi)
  have hsol := smoothH1_isWeakSolution hg hh k hlap
  obtain ⟨-, hgrad, hbound⟩ := hCZ p hp (fun _ => (1 : Mat 2))
    (fun _ _ => measurable_const.aemeasurable) (Filter.Eventually.of_forall fun _ => isEllipticMatrix_one_two)
    hclose (smoothH1 hg) (unitForce k h) hFcoord hF hsol
  have hFmean : lpMeanNormOn (euclideanBall (0 : Vec 2) 1) (ENNReal.ofReal p)
      (fun x => vecEuclideanNorm (unitForce k h x))
      (memLp_normalizedVolumeOn_of_memLpOn hF hB1pos) ≤ M := by
    rw [lpMeanNormOn_eq_toReal]
    refine ENNReal.toReal_le_of_le_ofReal hM ?_
    unfold eLpMeanNormOn
    have := eLpNorm_le_of_ae_bound (p := ENNReal.ofReal p)
      (μ := normalizedVolumeOn (euclideanBall (0 : Vec 2) 1))
      (f := fun x => vecEuclideanNorm (unitForce k h x))
      (memLp_normalizedVolumeOn_of_memLpOn hF hB1pos).aestronglyMeasurable (C := M)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (vecEuclideanNorm_nonneg _), vecEuclideanNorm_unitForce]
        exact hhM x)
    simpa only [measure_univ, ENNReal.one_rpow, one_mul] using this
  have hmean : lpMeanNormOn (euclideanBall (0 : Vec 2) (1 / 2 : ℝ)) (ENNReal.ofReal p)
      (fun x => vecEuclideanNorm ((smoothH1 hg).grad x))
      (memLp_normalizedVolumeOn_of_memLpOn hgrad hB2pos) ≤
      C * (Real.sqrt (integralAverage (euclideanBall (0 : Vec 2) 1)
              (fun x => vecNormSq ((smoothH1 hg).grad x))) + p * M) := by
    refine le_trans hbound ?_
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    have hp0 : 0 ≤ p := by linarith
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hFmean hp0)
  exact integral_rpow_le_of_lpMeanNormOn_le hB2pos hB2top (by linarith)
    (fun x => vecEuclideanNorm_nonneg _) hgrad hmean

end PDE
