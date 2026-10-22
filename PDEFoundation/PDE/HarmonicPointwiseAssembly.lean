module

public import PDEFoundation.PDE.HarmonicDerivativeBounds
public import PDEFoundation.PDE.HarmonicLinfty
public import PDEFoundation.Analysis.AnalyticOfDerivBoundResult
public import PDEFoundation.Analysis.IteratedCoordDeriv
public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.Mean
public import PDEFoundation.Geometry.EuclideanBall.Interior

/-! # Pointwise harmonic derivative bounds and analyticity -/

@[expose] public section

open MeasureTheory Filter
open Set
open scoped Topology

noncomputable section

namespace PDE

/-- Dimension-only constant for the pointwise derivative and analyticity
estimates of a smooth harmonic representative. -/
def harmonicPointwiseConst (d : ℕ) : ℝ :=
  2 ^ (d + 1) * Real.sqrt d * (harmonicKernelDerivConst d + 1)

/-- The pointwise harmonic constant is strictly positive in positive dimension. -/
theorem harmonicPointwiseConst_pos {d : ℕ} (hd : 0 < d) :
    0 < harmonicPointwiseConst d := by
  unfold harmonicPointwiseConst
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hK : 0 ≤ harmonicKernelDerivConst d := harmonicKernelDerivConst_nonneg
  positivity

theorem analyticAt_of_harmonicOn {d : ℕ} (hd : 0 < d)
    {v : Vec d → ℝ} {r : ℝ} (hr : 0 < r)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (euclideanBall 0 r))
    (hharm : ∀ z ∈ euclideanBall 0 r, euclideanCoordLaplacian v z = 0)
    {x₀ : Vec d} (hx₀ : x₀ ∈ euclideanBall 0 r) :
    AnalyticAt ℝ v x₀ := by
  have hx₀Norm : vecEuclideanNorm x₀ < r := by
    simpa using (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx₀
  let δ : ℝ := (r - vecEuclideanNorm x₀) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hthreeδ : 3 * δ < r - vecEuclideanNorm x₀ := by
    dsimp [δ]
    linarith
  have hqδ : vecEuclideanNorm x₀ + δ < r := by
    linarith
  have hlocal : euclideanBall x₀ δ ⊆ euclideanBall 0 r := by
    apply euclideanBall_subset_of_center_norm_add_le hδ hr
    simpa using hqδ.le
  have hclosed : euclideanClosedBall x₀ (3 * δ) ⊆ euclideanBall 0 r := by
    intro z hz
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).2
    have hzNorm : vecEuclideanNorm (z - x₀) ≤ 3 * δ :=
      (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).1 hz
    calc
      vecEuclideanNorm (z - 0) = vecEuclideanNorm ((z - x₀) + x₀) := by
        congr 1
        abel
      _ ≤ vecEuclideanNorm (z - x₀) + vecEuclideanNorm x₀ :=
        vecEuclideanNorm_add_le _ _
      _ ≤ 3 * δ + vecEuclideanNorm x₀ := by nlinarith [hzNorm]
      _ < r := by linarith
  obtain ⟨C, hC⟩ :=
    (isCompact_euclideanClosedBall x₀ (by positivity : 0 ≤ 3 * δ)).exists_bound_of_continuousOn
      ((hv.mono hclosed).continuousOn)
  let M : ℝ := max C 0
  have hM : 0 ≤ M := le_max_right C 0
  have hMbound : ∀ z ∈ euclideanClosedBall x₀ (3 * δ), |v z| ≤ M := by
    intro z hz
    dsimp [M]
    simpa only [Real.norm_eq_abs] using (hC z hz).trans (le_max_left C 0)
  have hK : 0 ≤ harmonicKernelDerivConst d := harmonicKernelDerivConst_nonneg
  have hKlocal : 0 ≤ harmonicKernelDerivConst d / (2 * δ) :=
    div_nonneg hK (by positivity)
  have hcoordBound : ∀ y ∈ euclideanBall x₀ δ,
      ∀ m : ℕ, ∀ ι : Fin m → Fin d,
        |iteratedFDeriv ℝ m v y (fun k => Pi.single (ι k) 1)| ≤
          M * ((harmonicKernelDerivConst d / (2 * δ) * m) ^ m) := by
    intro y hy m ι
    have hyNorm : vecEuclideanNorm (y - x₀) < δ :=
      (mem_euclideanBall_iff_vecEuclideanNorm_lt hδ).1 hy
    have hyOuter : y ∈ euclideanBall 0 r := hlocal hy
    have hyClosed : y ∈ euclideanClosedBall x₀ (3 * δ) := by
      apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
      exact hyNorm.le.trans (by linarith)
    have hEqCoord := iteratedFDeriv_eq_iteratedCoordDeriv
      (isOpen_euclideanBall 0 r) hv m ι y hyOuter
    have hEqBasis :
        iteratedFDeriv ℝ m v y (fun k => Pi.single (ι k) 1) =
          iteratedCoordDeriv m ι v y := by
      simpa [basisVec] using hEqCoord
    by_cases hm : m = 0
    · subst m
      rw [hEqBasis]
      simpa [iteratedCoordDeriv] using hMbound y hyClosed
    · have hmpos : 1 ≤ m := by omega
      have hnorm : vecEuclideanNorm y < vecEuclideanNorm x₀ + δ := by
        have htriangle :
            vecEuclideanNorm y ≤ vecEuclideanNorm (y - x₀) + vecEuclideanNorm x₀ := by
          calc
            vecEuclideanNorm y = vecEuclideanNorm ((y - x₀) + x₀) := by
              congr 1
              abel
            _ ≤ vecEuclideanNorm (y - x₀) + vecEuclideanNorm x₀ :=
              vecEuclideanNorm_add_le _ _
        have htemp := add_lt_add_right hyNorm (vecEuclideanNorm x₀)
        have htemp' : vecEuclideanNorm (y - x₀) + vecEuclideanNorm x₀ <
            δ + vecEuclideanNorm x₀ := by
          simpa [add_comm] using htemp
        calc
          vecEuclideanNorm y ≤ vecEuclideanNorm (y - x₀) + vecEuclideanNorm x₀ := htriangle
          _ < δ + vecEuclideanNorm x₀ := htemp'
          _ = vecEuclideanNorm x₀ + δ := by ring
      have hyRadius : 3 * δ < r - vecEuclideanNorm y := by
        dsimp [δ] at hthreeδ hnorm ⊢
        linarith
      have hRadiusPos : 0 < r - vecEuclideanNorm y := by linarith
      have hOuterY : euclideanBall y (r - vecEuclideanNorm y) ⊆ euclideanBall 0 r := by
        apply euclideanBall_subset_of_center_norm_add_le hRadiusPos hr
        simp [sub_zero]
      have hvY : ContDiffOn ℝ (⊤ : ℕ∞) v
          (euclideanBall y (r - vecEuclideanNorm y)) := hv.mono hOuterY
      have hharmY : ∀ z ∈ euclideanBall y (r - vecEuclideanNorm y),
          euclideanCoordLaplacian v z = 0 := fun z hz => hharm z (hOuterY hz)
      have hsmall : ∀ z ∈ euclideanClosedBall y (2 * δ), |v z| ≤ M := by
        intro z hz
        have hzNorm : vecEuclideanNorm (z - y) ≤ 2 * δ :=
          (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).1 hz
        have hzOuter : z ∈ euclideanClosedBall x₀ (3 * δ) := by
          apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
          calc
            vecEuclideanNorm (z - x₀) = vecEuclideanNorm ((z - y) + (y - x₀)) := by
              congr 1
              abel
            _ ≤ vecEuclideanNorm (z - y) + vecEuclideanNorm (y - x₀) :=
              vecEuclideanNorm_add_le _ _
            _ ≤ 2 * δ + δ := add_le_add hzNorm hyNorm.le
            _ = 3 * δ := by ring
        exact hMbound z hzOuter
      have hiter := abs_iteratedCoordDeriv_le_of_harmonicOn hd hvY hharmY
        (by positivity : 0 < 2 * δ) (by linarith) hsmall m hmpos ι
      rw [hEqBasis]
      calc
        |iteratedCoordDeriv m ι v y| ≤
            (harmonicKernelDerivConst d * m / (2 * δ)) ^ m * M := hiter
        _ = M * ((harmonicKernelDerivConst d / (2 * δ) * m) ^ m) := by
          rw [show harmonicKernelDerivConst d * m / (2 * δ) =
            harmonicKernelDerivConst d / (2 * δ) * m by ring]
          ring
  exact analyticAt_of_smooth_iteratedFDeriv_coordinate_bound v x₀ hδ hM hKlocal
    (hv.mono hlocal) hcoordBound

private theorem iteratedCoordDeriv_sub_const_eqOn {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {v : Vec d → ℝ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U) (c : ℝ)
    (m : ℕ) (ι : Fin m → Fin d) (hm : 1 ≤ m) :
    ∀ x ∈ U,
      iteratedCoordDeriv m ι (fun x => v x - c) x = iteratedCoordDeriv m ι v x := by
  intro x hx
  let w : Vec d → ℝ := fun y => v y - c
  have hw : ContDiffOn ℝ (⊤ : ℕ∞) w U := by
    dsimp [w]
    exact hv.sub contDiffOn_const
  have hvAt : ContDiffAt ℝ m v x :=
    ((hv x hx).contDiffAt (hU.mem_nhds hx)).of_le (by simp)
  have hcAt : ContDiffAt ℝ m (fun _ : Vec d => c) x := contDiffAt_const
  have hsub := iteratedFDeriv_sub_apply (i := m)
    hvAt hcAt
  rw [iteratedFDeriv_const_of_ne (by omega : m ≠ 0) c] at hsub
  simp at hsub
  have hsub' : iteratedFDeriv ℝ m w x = iteratedFDeriv ℝ m v x := by
    change iteratedFDeriv ℝ m (v - fun _ => c) x = iteratedFDeriv ℝ m v x
    exact hsub
  have hWcoord := iteratedFDeriv_eq_iteratedCoordDeriv hU hw m ι x hx
  have hVcoord := iteratedFDeriv_eq_iteratedCoordDeriv hU hv m ι x hx
  calc
    iteratedCoordDeriv m ι w x =
        iteratedFDeriv ℝ m w x (fun k => basisVec (ι k)) := hWcoord.symm
    _ = iteratedFDeriv ℝ m v x (fun k => basisVec (ι k)) := by
      exact congrArg (fun D => D (fun k => basisVec (ι k))) hsub'
    _ = iteratedCoordDeriv m ι v x := hVcoord

private theorem real_sqrt_natCast_pow (d m : ℕ) :
    Real.sqrt ((d : ℝ) ^ m) = (Real.sqrt d) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, Real.sqrt_mul (pow_nonneg (Nat.cast_nonneg d) m), ih, pow_succ]

/-- A smooth harmonic representative is analytic on the ball, and its
centered iterated derivative tensor obeys the dimension-explicit estimate. -/
theorem harmonicPointwise_of_representative {d : ℕ} (hd : 0 < d)
    {r : ℝ} (hr : 0 < r)
    (u : H1Function (euclideanBall (0 : Vec d) r))
    {v : Vec d → ℝ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (euclideanBall 0 r))
    (hharm : ∀ y ∈ euclideanBall 0 r, euclideanCoordLaplacian v y = 0)
    (hae : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) r), v x = u.toFun x) :
    AnalyticOnNhd ℝ v (euclideanBall 0 r) ∧
      ∀ (m : ℕ), 1 ≤ m →
        Real.sqrt (∑ ι : Fin m → Fin d,
          (iteratedFDeriv ℝ m v 0 (fun k => Pi.single (ι k) 1)) ^ 2) ≤
          (harmonicPointwiseConst d * m / r) ^ m *
            Real.sqrt (integralAverage (euclideanBall 0 r)
              (fun x => (u.toFun x - integralAverage (euclideanBall 0 r) u.toFun) ^ 2)) := by
  let U := euclideanBall (0 : Vec d) r
  have hUopen : IsOpen U := isOpen_euclideanBall 0 r
  have hzero : (0 : Vec d) ∈ U := center_mem_euclideanBall 0 hr
  let : IsFiniteMeasure (volumeOn U) := isFiniteMeasure_volumeOn_euclideanBall 0 hr.le
  refine ⟨?_, ?_⟩
  · intro x hx
    exact analyticAt_of_harmonicOn hd hr hv hharm hx
  · intro m hm
    let c := integralAverage U u.toFun
    let w : Vec d → ℝ := fun x => v x - c
    have hw : ContDiffOn ℝ (⊤ : ℕ∞) w U := by
      dsimp [w]
      exact hv.sub contDiffOn_const
    have hsecond : ∀ i z, z ∈ U →
        euclideanCoordSecondDeriv i i w z = euclideanCoordSecondDeriv i i v z := by
      intro i z hz
      have hderivOn := iteratedCoordDeriv_sub_const_eqOn hUopen hv c
        2 (fun _ => i) (by norm_num)
      have hderiv := hderivOn z hz
      change euclideanCoordSecondDeriv i i w z = euclideanCoordSecondDeriv i i v z
      exact hderiv
    have hharmW : ∀ z ∈ U, euclideanCoordLaplacian w z = 0 := by
      intro z hz
      rw [euclideanCoordLaplacian]
      calc
        (∑ i : Fin d, euclideanCoordSecondDeriv i i w z) =
            ∑ i : Fin d, euclideanCoordSecondDeriv i i v z := by
          apply Finset.sum_congr rfl
          intro i _
          exact hsecond i z hz
        _ = 0 := hharm z hz
    have huShift : MemLp (fun x => u.toFun x - c) 2 (volumeOn U) := by
      exact u.memL2.sub (memLp_const c)
    have huShiftSq : Integrable (fun x => (u.toFun x - c) ^ 2) (volumeOn U) :=
      huShift.integrable_sq
    have hsqAE : (fun x => w x ^ 2) =ᵐ[volumeOn U]
        fun x => (u.toFun x - c) ^ 2 := by
      filter_upwards [hae] with x hx
      simp [w, hx]
    have hwSq : Integrable (fun x => w x ^ 2) (volumeOn U) := by
      exact huShiftSq.congr hsqAE.symm
    have hwSqOn : IntegrableOn (fun x => w x ^ 2) U := by
      simpa only [IntegrableOn] using hwSq
    have hmeanSq : integralAverage U (fun x => w x ^ 2) =
        integralAverage U (fun x => (u.toFun x - c) ^ 2) :=
      integralAverage_congr_ae hsqAE
    let M := (2 : ℝ) ^ d * Real.sqrt (integralAverage U (fun x => w x ^ 2))
    have hM : 0 ≤ M := by dsimp [M]; positivity
    have hpoint : ∀ z ∈ euclideanClosedBall 0 (r / 2), |w z| ≤ M := by
      intro z hz
      exact abs_harmonic_le_pow_mul_sqrt_integralAverage_sq hd hr hw hharmW
        hwSqOn hz
    have hiter : ∀ (ι : Fin m → Fin d),
        |iteratedCoordDeriv m ι w 0| ≤
          (harmonicKernelDerivConst d * m / (r / 2)) ^ m * M := by
      intro ι
      exact abs_iteratedCoordDeriv_le_of_harmonicOn hd hw hharmW
        (by positivity : 0 < r / 2) (by linarith)
        hpoint m hm ι
    have hrootDim : Real.sqrt ((d : ℝ) ^ m) = (Real.sqrt d) ^ m :=
      real_sqrt_natCast_pow d m
    have hK : 0 ≤ harmonicKernelDerivConst d := harmonicKernelDerivConst_nonneg
    let B := (harmonicKernelDerivConst d * m / (r / 2)) ^ m * M
    have hB : 0 ≤ B := by
      dsimp [B]
      positivity
    have hcomponent : ∀ ι : Fin m → Fin d,
        |iteratedFDeriv ℝ m v 0 (fun k => Pi.single (ι k) 1)| ≤ B := by
      intro ι
      have hEqFDeriv := iteratedFDeriv_eq_iteratedCoordDeriv hUopen hv m ι 0 hzero
      have hEqW : iteratedFDeriv ℝ m v 0 (fun k => Pi.single (ι k) 1) =
          iteratedCoordDeriv m ι w 0 := by
        calc
          iteratedFDeriv ℝ m v 0 (fun k => Pi.single (ι k) 1) =
              iteratedCoordDeriv m ι v 0 := by simpa [basisVec] using hEqFDeriv
          _ = iteratedCoordDeriv m ι w 0 := by
            symm
            exact iteratedCoordDeriv_sub_const_eqOn hUopen hv c m ι hm 0 hzero
      rw [hEqW]
      exact hiter ι
    have hsum :
        (∑ ι : Fin m → Fin d,
          (iteratedFDeriv ℝ m v 0 (fun k => Pi.single (ι k) 1)) ^ 2) ≤
          (d : ℝ) ^ m * B ^ 2 := by
      calc
        _ ≤ ∑ ι : Fin m → Fin d, B ^ 2 := by
          apply Finset.sum_le_sum
          intro ι _
          apply (sq_le_sq).2
          simpa [abs_of_nonneg hB] using hcomponent ι
        _ = (d : ℝ) ^ m * B ^ 2 := by simp
    have hrootBound :
        Real.sqrt (∑ ι : Fin m → Fin d,
          (iteratedFDeriv ℝ m v 0 (fun k => Pi.single (ι k) 1)) ^ 2) ≤
        (Real.sqrt d) ^ m * B := by
      calc
        _ ≤ Real.sqrt ((d : ℝ) ^ m * B ^ 2) := Real.sqrt_le_sqrt hsum
        _ = (Real.sqrt d) ^ m * B := by
          rw [Real.sqrt_mul (pow_nonneg (Nat.cast_nonneg d) m), hrootDim,
            Real.sqrt_sq_eq_abs, abs_of_nonneg hB]
    have hmeanNonneg : 0 ≤ Real.sqrt
        (integralAverage U (fun x => (u.toFun x - c) ^ 2)) := Real.sqrt_nonneg _
    have htwoD : 1 ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    have hbase :
        (2 : ℝ) ^ d * Real.sqrt d * (2 * harmonicKernelDerivConst d * m / r) ≤
          harmonicPointwiseConst d * m / r := by
      have hfactor : 0 ≤ (2 : ℝ) ^ (d + 1) * Real.sqrt d * m / r := by positivity
      have hKle : harmonicKernelDerivConst d ≤ harmonicKernelDerivConst d + 1 := by linarith
      rw [harmonicPointwiseConst]
      calc
        (2 : ℝ) ^ d * Real.sqrt d * (2 * harmonicKernelDerivConst d * m / r) =
            ((2 : ℝ) ^ (d + 1) * Real.sqrt d * m / r) * harmonicKernelDerivConst d := by
              ring
        _ ≤ ((2 : ℝ) ^ (d + 1) * Real.sqrt d * m / r) *
            (harmonicKernelDerivConst d + 1) :=
              mul_le_mul_of_nonneg_left hKle hfactor
        _ = (2 : ℝ) ^ (d + 1) * Real.sqrt d *
            (harmonicKernelDerivConst d + 1) * m / r := by ring
    have hfactorBound :
        (2 : ℝ) ^ d * (Real.sqrt d) ^ m *
          (harmonicKernelDerivConst d * m / (r / 2)) ^ m ≤
        (harmonicPointwiseConst d * m / r) ^ m := by
      have hscale : harmonicKernelDerivConst d * m / (r / 2) =
          2 * harmonicKernelDerivConst d * m / r := by
        field_simp [hr.ne']
      rw [hscale]
      calc
        (2 : ℝ) ^ d * (Real.sqrt d) ^ m *
            (2 * harmonicKernelDerivConst d * m / r) ^ m =
            ((2 : ℝ) ^ d) ^ 1 *
              ((Real.sqrt d) * (2 * harmonicKernelDerivConst d * m / r)) ^ m := by
                rw [mul_pow]
                ring
        _ ≤ ((2 : ℝ) ^ d) ^ m *
              ((Real.sqrt d) * (2 * harmonicKernelDerivConst d * m / r)) ^ m := by
                exact mul_le_mul_of_nonneg_right
                  (pow_le_pow_right₀ htwoD (by omega)) (by positivity)
        _ = (((2 : ℝ) ^ d) * Real.sqrt d *
              (2 * harmonicKernelDerivConst d * m / r)) ^ m := by
                rw [mul_pow]
                ring
        _ ≤ (harmonicPointwiseConst d * m / r) ^ m := by
                exact pow_le_pow_left₀ (by positivity) hbase m
    calc
      Real.sqrt (∑ ι : Fin m → Fin d,
          (iteratedFDeriv ℝ m v 0 (fun k => Pi.single (ι k) 1)) ^ 2)
          ≤ (Real.sqrt d) ^ m * B := hrootBound
      _ = (2 : ℝ) ^ d * (Real.sqrt d) ^ m *
            (harmonicKernelDerivConst d * m / (r / 2)) ^ m *
            Real.sqrt (integralAverage U (fun x => w x ^ 2)) := by
          dsimp [B, M]
          rw [hmeanSq]
          ring
      _ ≤ (harmonicPointwiseConst d * m / r) ^ m *
            Real.sqrt (integralAverage U (fun x => (u.toFun x - c) ^ 2)) := by
          rw [hmeanSq]
          exact mul_le_mul_of_nonneg_right hfactorBound hmeanNonneg
