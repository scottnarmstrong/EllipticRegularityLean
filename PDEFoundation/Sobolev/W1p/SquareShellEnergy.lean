module

public import PDEFoundation.Measure.SquareLoopFubini
public import PDEFoundation.Sobolev.H1.Graph
public import PDEFoundation.Sobolev.W1p.RepresentativeGraph
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Shell energies controlled by the `H¹` graph distance

This module transfers the maximum-norm `H¹` graph distance to the scalar
square-shell energies used in the square-trace construction.  The scalar value
and Euclidean gradient components each have constant one; the restriction to
the shell is the only measure comparison.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

/-- A scalar `L²` class controls the square-shell energy of any of its
representatives, with no loss of constant. -/
theorem squareShellScalarEnergy_le_sq_norm_of_ae_eq
    {U : Set (Vec 2)} (F : ScalarLp U (2 : ℝ≥0∞))
    (f : Vec 2 → ℝ) {x₀ : Vec 2} {r : ℝ}
    (hF : ⇑F =ᵐ[volumeOn U] f)
    (hsub : dyadicSquareShell x₀ r ⊆ U) :
    squareShellScalarEnergy f x₀ r ≤ ‖F‖ ^ 2 := by
  have hmem : MemLp f 2 (volumeOn U) :=
    MemLp.ae_eq hF (Lp.memLp F)
  have hint : Integrable (fun x => f x ^ 2) (volumeOn U) :=
    hmem.integrable_sq
  have hle : squareShellScalarEnergy f x₀ r ≤
      ∫ x, f x ^ 2 ∂(volumeOn U) := by
    unfold squareShellScalarEnergy
    exact integral_mono_measure
      (Measure.restrict_mono hsub le_rfl)
      (Filter.Eventually.of_forall fun x => sq_nonneg (f x)) hint
  have hnorm : (∫ x, f x ^ 2 ∂(volumeOn U)) = ‖F‖ ^ 2 := by
    calc
      (∫ x, f x ^ 2 ∂(volumeOn U)) = ∫ x, F x ^ 2 ∂(volumeOn U) := by
        apply integral_congr_ae
        filter_upwards [hF] with x hx
        rw [hx]
      _ = RCLike.re (inner ℝ F F) := by
        rw [L2.inner_def, ← integral_re (L2.integrable_inner F F)]
        apply integral_congr_ae
        filter_upwards with x
        simp
      _ = ‖F‖ ^ 2 := inner_self_eq_norm_sq F
  rwa [hnorm] at hle

/-- The scalar value difference on a square shell is bounded by the squared
distance in the complete `H¹` graph, with constant one. -/
theorem squareShellScalarEnergy_sub_toFun_le_dist_sq
    {U : Set (Vec 2)} (v w : W1pFunction U (2 : ℝ≥0∞))
    {x₀ : Vec 2} {r : ℝ}
    (hsub : dyadicSquareShell x₀ r ⊆ U) :
    squareShellScalarEnergy (fun x => v.toFun x - w.toFun x) x₀ r ≤
      dist v.toW1pGraph w.toW1pGraph ^ 2 := by
  let F : ScalarLp U (2 : ℝ≥0∞) :=
    (v.toW1pGraph - w.toW1pGraph).1.1
  have hF : ⇑F =ᵐ[volumeOn U] fun x => v.toFun x - w.toFun x := by
    dsimp only [F]
    change ⇑(v.toW1pGraph.1.1 - w.toW1pGraph.1.1) =ᵐ[volumeOn U]
      fun x => v.toFun x - w.toFun x
    filter_upwards [Lp.coeFn_sub v.toW1pGraph.1.1 w.toW1pGraph.1.1,
      v.coeFn_toW1pGraph_fst, w.coeFn_toW1pGraph_fst] with x hsub hv hw
    rw [hsub]
    simp only [Pi.sub_apply, hv, hw]
  have hcomponent := squareShellScalarEnergy_le_sq_norm_of_ae_eq F
    (fun x => v.toFun x - w.toFun x) hF hsub
  have hnorm : ‖F‖ ≤ ‖v.toW1pGraph - w.toW1pGraph‖ := by
    rw [H1Graph.norm_eq_max]
    exact le_max_left _ _
  calc
    squareShellScalarEnergy (fun x => v.toFun x - w.toFun x) x₀ r ≤ ‖F‖ ^ 2 :=
      hcomponent
    _ ≤ ‖v.toW1pGraph - w.toW1pGraph‖ ^ 2 := by
      gcongr
    _ = dist v.toW1pGraph w.toW1pGraph ^ 2 := by
      rw [dist_eq_norm]

/-- A Hilbert-vector `L²` class controls the square-shell energy of the norm
of any of its representatives, with no loss of constant. -/
theorem squareShellScalarEnergy_le_sq_norm_of_ae_eq_hilbert
    {U : Set (Vec 2)} (F : HilbertVectorLp U (2 : ℝ≥0∞))
    (f : Vec 2 → ℝ) {x₀ : Vec 2} {r : ℝ}
    (hF : (fun x => ‖F x‖) =ᵐ[volumeOn U] f)
    (hsub : dyadicSquareShell x₀ r ⊆ U) :
    squareShellScalarEnergy f x₀ r ≤ ‖F‖ ^ 2 := by
  have hmem : MemLp f 2 (volumeOn U) :=
    MemLp.ae_eq hF (Lp.memLp F).norm
  have hint : Integrable (fun x => f x ^ 2) (volumeOn U) :=
    hmem.integrable_sq
  have hle : squareShellScalarEnergy f x₀ r ≤
      ∫ x, f x ^ 2 ∂(volumeOn U) := by
    unfold squareShellScalarEnergy
    exact integral_mono_measure
      (Measure.restrict_mono hsub le_rfl)
      (Filter.Eventually.of_forall fun x => sq_nonneg (f x)) hint
  have hnorm : (∫ x, f x ^ 2 ∂(volumeOn U)) = ‖F‖ ^ 2 := by
    calc
      (∫ x, f x ^ 2 ∂(volumeOn U)) = ∫ x, ‖F x‖ ^ 2 ∂(volumeOn U) := by
        apply integral_congr_ae
        filter_upwards [hF] with x hx
        rw [hx]
      _ = RCLike.re (inner ℝ F F) := by
        rw [L2.inner_def, ← integral_re (L2.integrable_inner F F)]
        apply integral_congr_ae
        filter_upwards with x
        simp
      _ = ‖F‖ ^ 2 := inner_self_eq_norm_sq F
  rwa [hnorm] at hle

/-- The Euclidean gradient difference on a square shell is bounded by the
squared distance in the complete `H¹` graph, with constant one. -/
theorem squareShellScalarEnergy_grad_sub_le_dist_sq
    {U : Set (Vec 2)} (v w : W1pFunction U (2 : ℝ≥0∞))
    {x₀ : Vec 2} {r : ℝ}
    (hsub : dyadicSquareShell x₀ r ⊆ U) :
    squareShellScalarEnergy
      (fun x => vecEuclideanNorm (v.grad x - w.grad x)) x₀ r ≤
      dist v.toW1pGraph w.toW1pGraph ^ 2 := by
  let F : HilbertVectorLp U (2 : ℝ≥0∞) :=
    (v.toW1pGraph - w.toW1pGraph).1.2
  have hF : (fun x => ‖F x‖) =ᵐ[volumeOn U]
      fun x => vecEuclideanNorm (v.grad x - w.grad x) := by
    dsimp only [F]
    change (fun x => ‖(v.toW1pGraph.1.2 - w.toW1pGraph.1.2) x‖) =ᵐ[volumeOn U]
      fun x => vecEuclideanNorm (v.grad x - w.grad x)
    filter_upwards [Lp.coeFn_sub v.toW1pGraph.1.2 w.toW1pGraph.1.2,
      v.coeFn_toW1pGraph_snd, w.coeFn_toW1pGraph_snd] with x hsub hv hw
    rw [hsub]
    rw [Pi.sub_apply, hv, hw]
    change ‖(toHilbertVecField v.grad - toHilbertVecField w.grad) x‖ = _
    rw [congrFun (toHilbertVecField_sub v.grad w.grad) x]
    exact norm_toHilbertVecField_apply (fun x => v.grad x - w.grad x) x
  have hcomponent := squareShellScalarEnergy_le_sq_norm_of_ae_eq_hilbert F
    (fun x => vecEuclideanNorm (v.grad x - w.grad x)) hF hsub
  have hnorm : ‖F‖ ≤ ‖v.toW1pGraph - w.toW1pGraph‖ := by
    rw [H1Graph.norm_eq_max]
    exact le_max_right _ _
  calc
    squareShellScalarEnergy
        (fun x => vecEuclideanNorm (v.grad x - w.grad x)) x₀ r ≤ ‖F‖ ^ 2 :=
      hcomponent
    _ ≤ ‖v.toW1pGraph - w.toW1pGraph‖ ^ 2 := by
      gcongr
    _ = dist v.toW1pGraph w.toW1pGraph ^ 2 := by
      rw [dist_eq_norm]

/-- A nonnegative weighted graph-error summability bound transfers to the
corresponding scalar square-shell energies. -/
theorem summable_weighted_squareShellScalarEnergy_sub_toFun
    {U : Set (Vec 2)} (ψ : ℕ → W1pFunction U (2 : ℝ≥0∞))
    (u : W1pFunction U (2 : ℝ≥0∞)) (w : ℕ → ℝ)
    {x₀ : Vec 2} {r : ℝ}
    (hsub : dyadicSquareShell x₀ r ⊆ U)
    (hw : ∀ n, 0 ≤ w n)
    (hsum : Summable fun n =>
      w n * dist (ψ n).toW1pGraph u.toW1pGraph ^ 2) :
    Summable fun n =>
      w n * squareShellScalarEnergy (fun x => (ψ n).toFun x - u.toFun x) x₀ r := by
  refine Summable.of_nonneg_of_le ?_ ?_ hsum
  · intro n
    exact mul_nonneg (hw n) (squareShellScalarEnergy_nonneg _ x₀ r)
  · intro n
    exact mul_le_mul_of_nonneg_left
      (squareShellScalarEnergy_sub_toFun_le_dist_sq (ψ n) u hsub) (hw n)

/-- A nonnegative weighted graph-error summability bound transfers to the
corresponding Euclidean-gradient square-shell energies. -/
theorem summable_weighted_squareShellScalarEnergy_grad_sub
    {U : Set (Vec 2)} (ψ : ℕ → W1pFunction U (2 : ℝ≥0∞))
    (u : W1pFunction U (2 : ℝ≥0∞)) (w : ℕ → ℝ)
    {x₀ : Vec 2} {r : ℝ}
    (hsub : dyadicSquareShell x₀ r ⊆ U)
    (hw : ∀ n, 0 ≤ w n)
    (hsum : Summable fun n =>
      w n * dist (ψ n).toW1pGraph u.toW1pGraph ^ 2) :
    Summable fun n => w n * squareShellScalarEnergy
      (fun x => vecEuclideanNorm ((ψ n).grad x - u.grad x)) x₀ r := by
  refine Summable.of_nonneg_of_le ?_ ?_ hsum
  · intro n
    exact mul_nonneg (hw n) (squareShellScalarEnergy_nonneg _ x₀ r)
  · intro n
    exact mul_le_mul_of_nonneg_left
      (squareShellScalarEnergy_grad_sub_le_dist_sq (ψ n) u hsub) (hw n)

/-- The dyadically weighted scalar square-shell energy errors are summable
whenever the corresponding graph errors are. -/
theorem summable_dyadic_squareShellScalarEnergy_sub_toFun
    {U : Set (Vec 2)} (ψ : ℕ → W1pFunction U (2 : ℝ≥0∞))
    (u : W1pFunction U (2 : ℝ≥0∞))
    {x₀ : Vec 2} {r : ℝ}
    (hsub : dyadicSquareShell x₀ r ⊆ U)
    (hsum : Summable fun n =>
      (2 : ℝ) ^ n * dist (ψ n).toW1pGraph u.toW1pGraph ^ 2) :
    Summable fun n => (2 : ℝ) ^ n *
      squareShellScalarEnergy (fun x => (ψ n).toFun x - u.toFun x) x₀ r :=
  summable_weighted_squareShellScalarEnergy_sub_toFun ψ u
    (fun n => (2 : ℝ) ^ n) hsub (fun n => pow_nonneg (by norm_num) n) hsum

/-- The dyadically weighted Euclidean-gradient square-shell energy errors are
summable whenever the corresponding graph errors are. -/
theorem summable_dyadic_squareShellScalarEnergy_grad_sub
    {U : Set (Vec 2)} (ψ : ℕ → W1pFunction U (2 : ℝ≥0∞))
    (u : W1pFunction U (2 : ℝ≥0∞))
    {x₀ : Vec 2} {r : ℝ}
    (hsub : dyadicSquareShell x₀ r ⊆ U)
    (hsum : Summable fun n =>
      (2 : ℝ) ^ n * dist (ψ n).toW1pGraph u.toW1pGraph ^ 2) :
    Summable fun n => (2 : ℝ) ^ n * squareShellScalarEnergy
      (fun x => vecEuclideanNorm ((ψ n).grad x - u.grad x)) x₀ r :=
  summable_weighted_squareShellScalarEnergy_grad_sub ψ u
    (fun n => (2 : ℝ) ^ n) hsub (fun n => pow_nonneg (by norm_num) n) hsum

namespace H1Function

/-- The dyadically weighted value errors of `H¹` graph approximants have
summable scalar square-shell energies. -/
theorem summable_dyadic_squareShellScalarEnergy_sub_toW1pFunction
    {U : Set (Vec 2)} (ψ : ℕ → W1pFunction U (2 : ℝ≥0∞))
    (u : H1Function U) {x₀ : Vec 2} {r : ℝ}
    (hsub : dyadicSquareShell x₀ r ⊆ U)
    (hsum : Summable fun n =>
      (2 : ℝ) ^ n * dist (ψ n).toW1pGraph u.toW1pFunction.toW1pGraph ^ 2) :
    Summable fun n => (2 : ℝ) ^ n * squareShellScalarEnergy
      (fun x => (ψ n).toFun x - u.toW1pFunction.toFun x) x₀ r :=
  summable_dyadic_squareShellScalarEnergy_sub_toFun ψ u.toW1pFunction hsub hsum

/-- The dyadically weighted Euclidean-gradient errors of `H¹` graph
approximants have summable scalar square-shell energies. -/
theorem summable_dyadic_squareShellScalarEnergy_grad_sub_toW1pFunction
    {U : Set (Vec 2)} (ψ : ℕ → W1pFunction U (2 : ℝ≥0∞))
    (u : H1Function U) {x₀ : Vec 2} {r : ℝ}
    (hsub : dyadicSquareShell x₀ r ⊆ U)
    (hsum : Summable fun n =>
      (2 : ℝ) ^ n * dist (ψ n).toW1pGraph u.toW1pFunction.toW1pGraph ^ 2) :
    Summable fun n => (2 : ℝ) ^ n * squareShellScalarEnergy
      (fun x => vecEuclideanNorm ((ψ n).grad x - u.toW1pFunction.grad x)) x₀ r :=
  summable_dyadic_squareShellScalarEnergy_grad_sub ψ u.toW1pFunction hsub hsum

end H1Function

end PDE
