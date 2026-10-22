module

public import PDEFoundation.Measure.CommonSquareRadius
public import PDEFoundation.Sobolev.Trace.RawSlices
public import PDEFoundation.Sobolev.W1p.ConvexApprox.Summable
public import PDEFoundation.Sobolev.W1p.SquareShellEnergy

/-!
# A common good square radius for `H¹` approximation

This module combines the smooth convex approximation, square-shell energy,
and countable good-radius layers.  Its public conclusion keeps the original
gradient boundary energy and the two approximation-error energy families at
one common radius.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The two scalar enlarged-side error energy series at one radius.  Naming
this conjunction keeps the countable good-radius exceptional set small. -/
def HasSummableTwoWeightedEnlargedSquareSideEnergies
    (f g : ℕ → Vec 2 → ℝ) (w : ℕ → ℝ) (x₀ : Vec 2) (r ρ : ℝ) : Prop :=
  Summable (fun n => w n * enlargedSquareSideScalarEnergy (f n) x₀ r ρ) ∧
    Summable (fun n => w n * enlargedSquareSideScalarEnergy (g n) x₀ r ρ)

/-- Two weighted scalar enlarged-side energy families are simultaneously
summable for almost every radius in the dyadic annulus. -/
theorem ae_summable_two_weighted_scalar_enlargedSquareSide_energy
    {f g : ℕ → Vec 2 → ℝ} {w : ℕ → ℝ}
    {x₀ : Vec 2} {r : ℝ}
    (hf : ∀ n, MemL2On (centeredAxisCube x₀ (2 * r)) (f n))
    (hg : ∀ n, MemL2On (centeredAxisCube x₀ (2 * r)) (g n))
    (hw : ∀ n, 0 ≤ w n)
    (hsumf : Summable fun n =>
      w n * squareShellScalarEnergy (f n) x₀ r)
    (hsumg : Summable fun n =>
      w n * squareShellScalarEnergy (g n) x₀ r) :
    ∀ᵐ ρ ∂volume.restrict (Ioo r (2 * r)),
      HasSummableTwoWeightedEnlargedSquareSideEnergies f g w x₀ r ρ := by
  let F : ℕ → ℝ → ℝ := fun n ρ =>
    w n * (enlargedSquareSideScalarEnergy (f n) x₀ r ρ +
      enlargedSquareSideScalarEnergy (g n) x₀ r ρ)
  have hFint : ∀ n, IntegrableOn (F n) (Ioo r (2 * r)) := by
    intro n
    exact ((integrableOn_enlargedSquareSideScalarEnergy_of_memL2On (hf n)).add
      (integrableOn_enlargedSquareSideScalarEnergy_of_memL2On (hg n))).const_mul (w n)
  have hFbound : ∀ n,
      (∫ ρ in Ioo r (2 * r), ‖F n ρ‖) ≤
        4 * (w n * squareShellScalarEnergy (f n) x₀ r +
          w n * squareShellScalarEnergy (g n) x₀ r) := by
    intro n
    have hnonneg : ∀ ρ, 0 ≤ F n ρ := by
      intro ρ
      dsimp only [F]
      exact mul_nonneg (hw n) <|
        add_nonneg
          (enlargedSquareSideScalarEnergy_nonneg (f n) x₀ r ρ)
          (enlargedSquareSideScalarEnergy_nonneg (g n) x₀ r ρ)
    rw [show (fun ρ => ‖F n ρ‖) = F n by
      funext ρ
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg ρ)]]
    rw [show F n = fun ρ => w n *
        (enlargedSquareSideScalarEnergy (f n) x₀ r ρ +
          enlargedSquareSideScalarEnergy (g n) x₀ r ρ) by rfl,
      MeasureTheory.integral_const_mul]
    have hsumint := integral_add
      (integrableOn_enlargedSquareSideScalarEnergy_of_memL2On (hf n))
      (integrableOn_enlargedSquareSideScalarEnergy_of_memL2On (hg n))
    rw [hsumint]
    calc
      w n *
          ((∫ ρ in Ioo r (2 * r), enlargedSquareSideScalarEnergy (f n) x₀ r ρ) +
            ∫ ρ in Ioo r (2 * r), enlargedSquareSideScalarEnergy (g n) x₀ r ρ) ≤
          w n * (4 * squareShellScalarEnergy (f n) x₀ r +
            4 * squareShellScalarEnergy (g n) x₀ r) := by
        apply mul_le_mul_of_nonneg_left
          (add_le_add
            (integral_enlargedSquareSideScalarEnergy_le_four_mul_squareShellScalarEnergy
              (hf n))
            (integral_enlargedSquareSideScalarEnergy_le_four_mul_squareShellScalarEnergy
              (hg n)))
        exact hw n
      _ = 4 * (w n * squareShellScalarEnergy (f n) x₀ r +
          w n * squareShellScalarEnergy (g n) x₀ r) := by ring
  have hFsum : Summable fun n => ∫ ρ in Ioo r (2 * r), ‖F n ρ‖ := by
    refine Summable.of_nonneg_of_le ?_ hFbound ?_
    · intro n
      exact integral_nonneg fun ρ => norm_nonneg (F n ρ)
    · simpa only [mul_add] using (hsumf.add hsumg).mul_left 4
  filter_upwards [ae_summable_of_summable_integral_norm hFint hFsum]
    with ρ hρsum
  constructor
  · refine Summable.of_nonneg_of_le ?_ ?_ hρsum
    · intro n
      exact mul_nonneg (hw n)
        (enlargedSquareSideScalarEnergy_nonneg (f n) x₀ r ρ)
    · intro n
      dsimp only [F]
      nlinarith [mul_nonneg (hw n)
        (enlargedSquareSideScalarEnergy_nonneg (g n) x₀ r ρ)]
  · refine Summable.of_nonneg_of_le ?_ ?_ hρsum
    · intro n
      exact mul_nonneg (hw n)
        (enlargedSquareSideScalarEnergy_nonneg (g n) x₀ r ρ)
    · intro n
      dsimp only [F]
      nlinarith [mul_nonneg (hw n)
        (enlargedSquareSideScalarEnergy_nonneg (f n) x₀ r ρ)]

namespace H1Function

/-- Smooth convex approximants have one radius in the dyadic square annulus
which is good for the original tangential gradient energy and has summable
dyadically weighted value and Euclidean-gradient error energies. The selected
subsequence also retains its global dyadically weighted `H¹` graph-error
summability, so later normal-slice and side-trace constructions can use the
same approximants. -/
theorem exists_good_square_radius_summable_convexApproxSmoothW1p_error
    {U : Set (Vec 2)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) {x₀ : Vec 2} {r : ℝ}
    (hr : 0 < r)
    (houter : centeredAxisCube x₀ (2 * r) ⊆ U) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      (∀ n, ContDiff ℝ (⊤ : ℕ∞)
        (W1pFunction.convexApproxSmoothW1p hU (by norm_num)
          u.toW1pFunction x₀ hr (k n)).toFun) ∧
      Summable (fun n =>
        (2 : ℝ) ^ n *
          dist
            ((W1pFunction.convexApproxSmoothW1p hU (by norm_num)
              u.toW1pFunction x₀ hr (k n)).toW1pGraph)
            u.toW1pFunction.toW1pGraph ^ 2) ∧
      ∃ ρ ∈ Ioo r (2 * r),
        enlargedSquareSideTangentialEnergy u.grad x₀ r ρ ≤
          (4 / r) * squareShellVectorEnergy u.grad x₀ r ∧
        HasRawEnlargedSquareSideSlices u.toFun x₀ r ρ ∧
        HasRawEnlargedSquareTangentialSlices u.grad x₀ r ρ ∧
        Summable (fun n => (2 : ℝ) ^ n *
          enlargedSquareSideScalarEnergy
            (fun x =>
              (W1pFunction.convexApproxSmoothW1p hU (by norm_num)
                u.toW1pFunction x₀ hr (k n)).toFun x - u.toFun x)
            x₀ r ρ) ∧
        Summable (fun n => (2 : ℝ) ^ n *
          enlargedSquareSideScalarEnergy
            (fun x => vecEuclideanNorm
              ((W1pFunction.convexApproxSmoothW1p hU (by norm_num)
                u.toW1pFunction x₀ hr (k n)).grad x - u.grad x))
            x₀ r ρ) ∧
        (∀ n, HasRawEnlargedSquareSideSlices
          (fun x =>
            (W1pFunction.convexApproxSmoothW1p hU (by norm_num)
              u.toW1pFunction x₀ hr (k n)).toFun x - u.toFun x)
          x₀ r ρ) ∧
        ∀ n, HasRawEnlargedSquareSideSlices
          (fun x => vecEuclideanNorm
            ((W1pFunction.convexApproxSmoothW1p hU (by norm_num)
              u.toW1pFunction x₀ hr (k n)).grad x - u.grad x))
          x₀ r ρ := by
  have hclosedBall : Metric.closedBall x₀ r ⊆ U := by
    rw [← closedCenteredAxisCube_eq_metric_closedBall x₀ hr.le]
    exact
      (closedCenteredAxisCube_subset_centeredAxisCube_two x₀ hr).trans
        houter
  obtain ⟨k, hkmono, hksmooth, hkdist, hksum⟩ :=
    exists_strictMono_convexApproxSmoothW1p_summable_h1Graph_error
      hU u hclosedBall hr
  let ψ : ℕ → W1pFunction U (2 : ℝ≥0∞) := fun n =>
    W1pFunction.convexApproxSmoothW1p hU (by norm_num)
      u.toW1pFunction x₀ hr (k n)
  have hgradOuter : MemVectorL2On (centeredAxisCube x₀ (2 * r)) u.grad := by
    intro i
    exact memLpOn_mono houter (u.gradMemL2 i)
  have huOuter : MemL2On (centeredAxisCube x₀ (2 * r)) u.toFun :=
    memLpOn_mono houter u.memL2
  have hvalueOuter : ∀ n,
      MemL2On (centeredAxisCube x₀ (2 * r))
        (fun x => (ψ n).toFun x - u.toFun x) := by
    intro n
    exact memLpOn_mono houter ((ψ n).memLp.sub u.toW1pFunction.memLp)
  have hgradErrorOuter : ∀ n,
      MemL2On (centeredAxisCube x₀ (2 * r))
        (fun x => vecEuclideanNorm ((ψ n).grad x - u.grad x)) := by
    intro n
    apply memLpOn_mono houter
    apply GradMemLpOn.memLp_vecEuclideanNorm
    intro i
    exact (ψ n).gradMemLp i |>.sub (u.gradMemL2 i)
  have hvalueSum : Summable fun n => (2 : ℝ) ^ n *
      squareShellScalarEnergy (fun x => (ψ n).toFun x - u.toFun x) x₀ r := by
    apply summable_dyadic_squareShellScalarEnergy_sub_toW1pFunction ψ u
    · exact fun _ hx => houter hx.1
    simpa only [ψ, H1Function.toW1pFunction_toFun,
      H1Function.toW1pFunction_grad] using hksum
  have hgradSum : Summable fun n => (2 : ℝ) ^ n *
      squareShellScalarEnergy
        (fun x => vecEuclideanNorm ((ψ n).grad x - u.grad x)) x₀ r := by
    apply summable_dyadic_squareShellScalarEnergy_grad_sub_toW1pFunction ψ u
    · exact fun _ hx => houter hx.1
    simpa only [ψ, H1Function.toW1pFunction_toFun,
      H1Function.toW1pFunction_grad] using hksum
  have hsumAE := ae_summable_two_weighted_scalar_enlargedSquareSide_energy
    hvalueOuter hgradErrorOuter
    (fun n => pow_nonneg (by norm_num) n) hvalueSum hgradSum
  have hsliceAE : ∀ᵐ ρ ∂volume.restrict (Ioo r (2 * r)),
      ∀ n, HasRawEnlargedSquareSideSlices
        (fun x => (ψ n).toFun x - u.toFun x) x₀ r ρ ∧
        HasRawEnlargedSquareSideSlices
          (fun x => vecEuclideanNorm ((ψ n).grad x - u.grad x)) x₀ r ρ := by
    exact ae_all_iff.2 fun n =>
      (ae_memLp_enlargedSquare_raw_slices_of_memL2On (hvalueOuter n)).and
        (ae_memLp_enlargedSquare_raw_slices_of_memL2On (hgradErrorOuter n))
  have hrawAE : ∀ᵐ ρ ∂volume.restrict (Ioo r (2 * r)),
      HasRawEnlargedSquareSideSlices u.toFun x₀ r ρ ∧
        HasRawEnlargedSquareTangentialSlices u.grad x₀ r ρ :=
    (ae_memLp_enlargedSquare_raw_slices_of_memL2On huOuter).and
      (ae_memLp_enlargedSquare_raw_tangential_slices_of_memVectorL2On
        hgradOuter)
  let GoodAt : ℝ → Prop := fun ρ =>
    HasSummableTwoWeightedEnlargedSquareSideEnergies
      (fun n x => (ψ n).toFun x - u.toFun x)
      (fun n x => vecEuclideanNorm ((ψ n).grad x - u.grad x))
      (fun n => (2 : ℝ) ^ n) x₀ r ρ ∧
    (∀ n, HasRawEnlargedSquareSideSlices
        (fun x => (ψ n).toFun x - u.toFun x) x₀ r ρ ∧
        HasRawEnlargedSquareSideSlices
          (fun x => vecEuclideanNorm ((ψ n).grad x - u.grad x)) x₀ r ρ) ∧
      HasRawEnlargedSquareSideSlices u.toFun x₀ r ρ ∧
        HasRawEnlargedSquareTangentialSlices u.grad x₀ r ρ
  let N : Set ℝ := Ioo r (2 * r) ∩ {ρ | ¬GoodAt ρ}
  have hN : volume N = 0 := by
    have hbad : (volume.restrict (Ioo r (2 * r)))
        {ρ | ¬GoodAt ρ} = 0 := by
      rw [← ae_iff]
      filter_upwards [hsumAE, hsliceAE, hrawAE] with ρ hsum hslice hraw
      exact show GoodAt ρ from ⟨hsum, hslice, hraw⟩
    rw [Measure.restrict_apply' measurableSet_Ioo] at hbad
    change volume (Ioo r (2 * r) ∩ {ρ | ¬GoodAt ρ}) = 0
    rw [inter_comm]
    exact hbad
  obtain ⟨ρ, hρ, hρN, hρgrad⟩ :=
    exists_good_enlargedSquare_radius_of_memVectorL2On hr hgradOuter hN
  have hρsum :
      HasSummableTwoWeightedEnlargedSquareSideEnergies
        (fun n x => (ψ n).toFun x - u.toFun x)
        (fun n x => vecEuclideanNorm ((ψ n).grad x - u.grad x))
        (fun n => (2 : ℝ) ^ n) x₀ r ρ ∧
      (∀ n, HasRawEnlargedSquareSideSlices
        (fun x => (ψ n).toFun x - u.toFun x) x₀ r ρ ∧
        HasRawEnlargedSquareSideSlices
          (fun x => vecEuclideanNorm ((ψ n).grad x - u.grad x)) x₀ r ρ) ∧
        HasRawEnlargedSquareSideSlices u.toFun x₀ r ρ ∧
          HasRawEnlargedSquareTangentialSlices u.grad x₀ r ρ := by
    have hgood : GoodAt ρ := by
      by_contra hnot
      exact hρN ⟨hρ, hnot⟩
    exact hgood
  refine ⟨k, hkmono, ?_, ?_, ρ, hρ, hρgrad, hρsum.2.2.1, hρsum.2.2.2,
    ?_, ?_, ?_, ?_⟩
  · simpa only [ψ] using hksmooth
  · exact hksum
  · simpa only [HasSummableTwoWeightedEnlargedSquareSideEnergies, ψ,
      H1Function.toW1pFunction_toFun] using hρsum.1.1
  · simpa only [HasSummableTwoWeightedEnlargedSquareSideEnergies, ψ,
      H1Function.toW1pFunction_grad] using hρsum.1.2
  · intro n
    simpa only [ψ, H1Function.toW1pFunction_toFun] using (hρsum.2.1 n).1
  · intro n
    simpa only [ψ, H1Function.toW1pFunction_grad] using (hρsum.2.1 n).2

end H1Function

end

end PDE
