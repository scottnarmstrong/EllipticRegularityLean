module

public import PDEFoundation.Analysis.IteratedCoordDeriv
public import PDEFoundation.PDE.HarmonicDerivativeBounds
public import PDEFoundation.PDE.HarmonicLinfty
import PDEFoundation.Analysis.Inequalities.JohnNirenberg.BallBasic
import Mathlib.LinearAlgebra.Multilinear.Basis

/-!
# Derivative decay for harmonic functions of polynomial growth

For a smooth harmonic `u` on `Vec d` with `∫⨍_{B_r} u² ≤ C r^{2N}` for `r ≥ 1`, every
iterated coordinate derivative of order `m` is bounded by `B * R ^ (N - m)` for all large `R`,
and in particular vanishes when `m > N`.  The bridge from coordinate derivatives to
`iteratedFDeriv` is also recorded here.
-/

@[expose] public section

open Filter Topology MeasureTheory

namespace PDE

noncomputable section

variable {d : ℕ}

/-- A continuous multilinear map on `Vec d` vanishing on all coordinate basis vectors is zero. -/
theorem continuousMultilinearMap_eq_zero_of_basisVec {m : ℕ}
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin m => Vec d) ℝ)
    (h : ∀ ι : Fin m → Fin d, L (fun k => basisVec (ι k)) = 0) : L = 0 := by
  have hL : L.toMultilinearMap = (0 : ContinuousMultilinearMap ℝ (fun _ : Fin m => Vec d) ℝ).toMultilinearMap := by
    refine Module.Basis.ext_multilinear (fun _ => Pi.basisFun ℝ (Fin d)) fun ι => ?_
    have := h ι
    simpa [basisVec] using this
  exact ContinuousMultilinearMap.toMultilinearMap_injective hL

/-- If all iterated coordinate derivatives of order `m` vanish at `x`, so does the
iterated Fréchet derivative. -/
theorem iteratedFDeriv_eq_zero_of_iteratedCoordDeriv_eq_zero {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (m : ℕ) (x : Vec d)
    (h : ∀ ι : Fin m → Fin d, iteratedCoordDeriv m ι u x = 0) :
    iteratedFDeriv ℝ m u x = 0 := by
  refine continuousMultilinearMap_eq_zero_of_basisVec _ fun ι => ?_
  rw [iteratedFDeriv_eq_iteratedCoordDeriv isOpen_univ hu.contDiffOn m ι x (Set.mem_univ x)]
  exact h ι

theorem rpow_le_const_mul_of_mem {N r R : ℝ} (hR : 0 < R) (h2 : 2 * R ≤ r) (h4 : r ≤ 4 * R) :
    r ^ N ≤ (4 ^ N + 1) * R ^ N := by
  have hr : 0 < r := by linarith
  rcases le_total 0 N with hN | hN
  · calc r ^ N ≤ (4 * R) ^ N := Real.rpow_le_rpow hr.le h4 hN
      _ = 4 ^ N * R ^ N := Real.mul_rpow (by norm_num) hR.le
      _ ≤ (4 ^ N + 1) * R ^ N := by
        have : 0 ≤ R ^ N := Real.rpow_nonneg hR.le N
        nlinarith
  · calc r ^ N ≤ (2 * R) ^ N := Real.rpow_le_rpow_of_nonpos (by positivity) h2 hN
      _ = 2 ^ N * R ^ N := Real.mul_rpow (by norm_num) hR.le
      _ ≤ (4 ^ N + 1) * R ^ N := by
        have h1 : (2 : ℝ) ^ N ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hN
        have h0 : 0 ≤ R ^ N := Real.rpow_nonneg hR.le N
        have : (0 : ℝ) ≤ 4 ^ N := Real.rpow_nonneg (by norm_num) N
        nlinarith

/-- Growth control of the ball `L²` average gives a pointwise bound with rate `r ^ N`. -/
theorem abs_le_of_growth (hd : 0 < d) {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hharm : ∀ x, euclideanCoordLaplacian u x = 0) {N C : ℝ}
    (hgrow : ∀ r : ℝ, 1 ≤ r →
      integralAverage (euclideanBall (0 : Vec d) r) (fun x => u x ^ 2) ≤ C * r ^ (2 * N))
    {r : ℝ} (hr : 1 ≤ r) {y : Vec d} (hy : vecEuclideanNorm y ≤ r / 2) :
    |u y| ≤ (2 : ℝ) ^ d * (Real.sqrt (max C 0) * r ^ N) := by
  have hr0 : 0 < r := by linarith
  have hint : IntegrableOn (fun z => u z ^ 2) (euclideanBall (0 : Vec d) r) := by
    have hc : Continuous fun z => u z ^ 2 := (hu.continuous).pow 2
    exact (hc.locallyIntegrable.integrableOn_isCompact
      (isCompact_euclideanClosedBall (0 : Vec d) hr0.le)).mono_set
      (euclideanBall_subset_euclideanClosedBall _ _)
  have h1 := abs_harmonic_le_pow_mul_sqrt_integralAverage_sq hd hr0
    (hu.contDiffOn) (fun z _ => hharm z) hint
    ((mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).mpr (by simpa using hy))
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hsq : r ^ (2 * N) = (r ^ N) ^ 2 := by
    rw [mul_comm, Real.rpow_mul hr0.le]; norm_cast
  calc Real.sqrt (integralAverage (euclideanBall (0 : Vec d) r) fun z => u z ^ 2)
      ≤ Real.sqrt (max C 0 * r ^ (2 * N)) := by
        refine Real.sqrt_le_sqrt ((hgrow r hr).trans ?_)
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hr0.le _)
    _ = Real.sqrt (max C 0) * r ^ N := by
        rw [Real.sqrt_mul (le_max_right _ _), hsq, Real.sqrt_sq (Real.rpow_nonneg hr0.le N)]

/-- Quantitative decay of high iterated coordinate derivatives. -/
theorem abs_iteratedCoordDeriv_le_of_growth (hd : 0 < d) {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hharm : ∀ x, euclideanCoordLaplacian u x = 0) {N C : ℝ}
    (hgrow : ∀ r : ℝ, 1 ≤ r →
      integralAverage (euclideanBall (0 : Vec d) r) (fun x => u x ^ 2) ≤ C * r ^ (2 * N))
    (x : Vec d) (m : ℕ) (hm : 1 ≤ m) (ι : Fin m → Fin d) {R : ℝ}
    (hR1 : 1 ≤ R) (hRx : vecEuclideanNorm x ≤ R) :
    |iteratedCoordDeriv m ι u x| ≤
      (harmonicKernelDerivConst d * m) ^ m * ((2 : ℝ) ^ d * Real.sqrt (max C 0) * (4 ^ N + 1)) *
        R ^ (N - m) := by
  have hR0 : 0 < R := by linarith
  set r : ℝ := 2 * (R + vecEuclideanNorm x) with hr
  have hr1 : 1 ≤ r := by
    have := vecEuclideanNorm_nonneg x
    rw [hr]; linarith
  have hM : ∀ z ∈ euclideanClosedBall x R, |u z| ≤ (2 : ℝ) ^ d * (Real.sqrt (max C 0) * r ^ N) := by
    intro z hz
    refine abs_le_of_growth hd hu hharm hgrow hr1 ?_
    have hz' := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR0.le).mp hz
    have : vecEuclideanNorm z ≤ vecEuclideanNorm (z - x) + vecEuclideanNorm x := by
      simpa using vecEuclideanNorm_add_le (z - x) x
    rw [hr]; linarith
  have hder := abs_iteratedCoordDeriv_le_of_harmonicOn hd (x := x) (R := R + 1) (ρ := R)
    (M := (2 : ℝ) ^ d * (Real.sqrt (max C 0) * r ^ N))
    (hu.contDiffOn) (fun z _ => hharm z) hR0 (by linarith) hM m hm ι
  refine hder.trans ?_
  have hrN : r ^ N ≤ (4 ^ N + 1) * R ^ N :=
    rpow_le_const_mul_of_mem hR0 (by rw [hr]; linarith [vecEuclideanNorm_nonneg x])
      (by rw [hr]; linarith)
  have hK : 0 ≤ (harmonicKernelDerivConst d * m) ^ m :=
    pow_nonneg (mul_nonneg harmonicKernelDerivConst_nonneg (Nat.cast_nonneg m)) m
  have hRm : R ^ (N - m) = R ^ N / R ^ m := by
    rw [Real.rpow_sub hR0, Real.rpow_natCast]
  have hdiv : (harmonicKernelDerivConst d * m / R) ^ m = (harmonicKernelDerivConst d * m) ^ m / R ^ m :=
    div_pow _ _ _
  rw [hdiv, hRm]
  have hs : 0 ≤ (2 : ℝ) ^ d * Real.sqrt (max C 0) := by positivity
  have hpm : 0 < R ^ m := pow_pos hR0 m
  calc (harmonicKernelDerivConst d * m) ^ m / R ^ m * ((2 : ℝ) ^ d * (Real.sqrt (max C 0) * r ^ N))
      ≤ (harmonicKernelDerivConst d * m) ^ m / R ^ m *
          ((2 : ℝ) ^ d * (Real.sqrt (max C 0) * ((4 ^ N + 1) * R ^ N))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hrN (Real.sqrt_nonneg _)) (by positivity)
    _ = _ := by ring

/-- High-order coordinate derivatives of a harmonic function of polynomial growth vanish. -/
theorem iteratedCoordDeriv_eq_zero_of_growth (hd : 0 < d) {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hharm : ∀ x, euclideanCoordLaplacian u x = 0) {N C : ℝ}
    (hgrow : ∀ r : ℝ, 1 ≤ r →
      integralAverage (euclideanBall (0 : Vec d) r) (fun x => u x ^ 2) ≤ C * r ^ (2 * N))
    (x : Vec d) (m : ℕ) (hm : 1 ≤ m) (hmN : N < m) (ι : Fin m → Fin d) :
    iteratedCoordDeriv m ι u x = 0 := by
  set B : ℝ := (harmonicKernelDerivConst d * m) ^ m *
    ((2 : ℝ) ^ d * Real.sqrt (max C 0) * (4 ^ N + 1)) with hB
  have hlim : Tendsto (fun R : ℝ => B * R ^ (N - m)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (y := (m : ℝ) - N) (by linarith)).const_mul B
    simpa [neg_sub] using h
  have hle : |iteratedCoordDeriv m ι u x| ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop (max 1 (vecEuclideanNorm x))] with R hR
    have := abs_iteratedCoordDeriv_le_of_growth hd hu hharm hgrow x m hm ι
      (le_trans (le_max_left _ _) hR) (le_trans (le_max_right _ _) hR)
    simpa [hB, mul_assoc] using this
  exact abs_nonpos_iff.mp hle

end

end PDE
