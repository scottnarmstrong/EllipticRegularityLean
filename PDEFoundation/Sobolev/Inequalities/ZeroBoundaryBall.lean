module

public import PDEFoundation.Geometry.AxisBox
public import PDEFoundation.Geometry.EuclideanBall
public import PDEFoundation.Sobolev.H1.Pairing
public import PDEFoundation.Sobolev.H1.ZeroExtension
public import PDEFoundation.Sobolev.Inequalities.ZeroBoundaryPoincare
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Zero-boundary `L²` Poincaré on round Euclidean balls

Extend an `H¹₀` representative by zero from a round ball to its enclosing
axis box, apply the coordinatewise box estimate, and restrict the resulting
value and gradient integrals back to the round ball.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace PDE

open MeasureTheory

private theorem euclideanBall_subset_enclosingAxisBox {d : ℕ}
    (x₀ : Vec d) {R : ℝ} (hR : 0 < R) :
    euclideanBall x₀ R ⊆
      axisBox (fun i => x₀ i - R) (fun i => x₀ i + R) := by
  intro x hx i _
  have hnorm : vecEuclideanNorm (x - x₀) < R :=
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mp hx
  have hcoord : |x i - x₀ i| < R := by
    have hle := abs_apply_le_vecEuclideanNorm (x - x₀) i
    simpa only [Pi.sub_apply] using lt_of_le_of_lt hle hnorm
  rcases abs_lt.mp hcoord with ⟨hlo, hhi⟩
  constructor <;> dsimp <;> linarith

private theorem indicator_sq {d : ℕ} (U : Set (Vec d))
    (f : Vec d → ℝ) (x : Vec d) :
    (Set.indicator U f x) ^ 2 = Set.indicator U (fun y => f y ^ 2) x := by
  by_cases hx : x ∈ U
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

private theorem indicator_vecNormSq {d : ℕ} (U : Set (Vec d))
    (F : Vec d → Vec d) (x : Vec d) :
    vecNormSq (Set.indicator U F x) =
      Set.indicator U (fun y => vecNormSq (F y)) x := by
  by_cases hx : x ∈ U
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx, vecNormSq, vecDot]

private theorem setIntegral_indicator_eq_of_subset {d : ℕ}
    {U V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ U)
    (f : Vec d → ℝ) :
    ∫ x in U, Set.indicator V f x = ∫ x in V, f x := by
  rw [setIntegral_indicator hV, Set.inter_eq_self_of_subset_right hVU]

/-- Coordinatewise zero-boundary Poincaré on a round ball. The scale factor is
the square of the side length of its enclosing axis box. -/
theorem h10_setIntegral_sq_le_four_mul_radius_sq_setIntegral_sq_grad_coord_on_euclideanBall
    {d : ℕ} {x₀ : Vec d} {R : ℝ} (hR : 0 < R)
    (u : H10Function (euclideanBall x₀ R)) (i : Fin d) :
    (∫ x in euclideanBall x₀ R, u x ^ 2 ∂volume) ≤
      (2 * R) ^ 2 *
        ∫ x in euclideanBall x₀ R,
          (u.toH1Function.grad x i) ^ 2 ∂volume := by
  let a : Vec d := fun j => x₀ j - R
  let b : Vec d := fun j => x₀ j + R
  let Q : Set (Vec d) := axisBox a b
  let V : Set (Vec d) := euclideanBall x₀ R
  have hVopen : IsOpen V := by
    exact isOpen_euclideanBall x₀ R
  have hQopen : IsOpen Q := by
    exact isOpen_axisBox a b
  have hVQ : V ⊆ Q := by
    simpa only [V, Q, a, b] using euclideanBall_subset_enclosingAxisBox x₀ hR
  let v : H10Function Q := u.zeroExtend hQopen hVopen hVQ
  have hab : ∀ j, a j < b j := by
    intro j
    dsimp [a, b]
    linarith
  have hbox :
      (∫ x in Q, v.toH1Function.toFun x ^ 2 ∂volume) ≤
        (b i - a i) ^ 2 *
          ∫ x in Q, (v.toH1Function.grad x i) ^ 2 ∂volume := by
    simpa only [Q] using
      (h10_setIntegral_sq_le_side_sq_setIntegral_sq_grad_coord_on_axisBox
        (a := a) (b := b) v hab i)
  have hvalueFun :
      (fun x => v.toH1Function.toFun x ^ 2) =
        Set.indicator V (fun x => u.toH1Function.toFun x ^ 2) := by
    funext x
    dsimp [v]
    exact indicator_sq V u.toH1Function.toFun x
  have hvalueIntegral :
      (∫ x in Q, v.toH1Function.toFun x ^ 2 ∂volume) =
    ∫ x in V, u.toH1Function.toFun x ^ 2 ∂volume := by
    rw [hvalueFun]
    exact setIntegral_indicator_eq_of_subset
      (isOpen_euclideanBall x₀ R).measurableSet hVQ _
  have hgradFun :
      (fun x => (v.toH1Function.grad x i) ^ 2) =
        Set.indicator V (fun x => (u.toH1Function.grad x i) ^ 2) := by
    funext x
    dsimp [v]
    have hcoord :
        Set.indicator V u.toH1Function.grad x i =
          Set.indicator V (fun y => u.toH1Function.grad y i) x := by
      by_cases hx : x ∈ V
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    rw [hcoord]
    exact indicator_sq V (fun y => u.toH1Function.grad y i) x
  have hgradIntegral :
      (∫ x in Q, (v.toH1Function.grad x i) ^ 2 ∂volume) =
    ∫ x in V, (u.toH1Function.grad x i) ^ 2 ∂volume := by
    rw [hgradFun]
    exact setIntegral_indicator_eq_of_subset
      (isOpen_euclideanBall x₀ R).measurableSet hVQ _
  have hside : b i - a i = 2 * R := by
    dsimp [a, b]
    ring
  simpa only [hvalueIntegral, hgradIntegral, hside] using hbox

/-- Full-vector zero-boundary Poincaré on a round Euclidean ball. The
explicit constant is `(2R)²`, where `2R` is the side length of an axis box
containing the ball. -/
theorem h10_setIntegral_sq_le_four_mul_radius_sq_setIntegral_vecNormSq_grad_on_euclideanBall
    {d : ℕ} (hd : 0 < d) {x₀ : Vec d} {R : ℝ} (hR : 0 < R)
    (u : H10Function (euclideanBall x₀ R)) :
    (∫ x in euclideanBall x₀ R, u x ^ 2 ∂volume) ≤
      (2 * R) ^ 2 *
        ∫ x in euclideanBall x₀ R,
          vecNormSq (u.toH1Function.grad x) ∂volume := by
  let i : Fin d := ⟨0, hd⟩
  have hcoord :=
    h10_setIntegral_sq_le_four_mul_radius_sq_setIntegral_sq_grad_coord_on_euclideanBall
      hR u i
  have hgradL2 : MemVectorL2On (euclideanBall x₀ R) u.toH1Function.grad := by
    intro j
    exact u.toH1Function.gradMemL2 j
  have hcoordInt : IntegrableOn
      (fun x => (u.toH1Function.grad x i) ^ 2) (euclideanBall x₀ R) :=
    by
      simpa only [IntegrableOn] using
        (u.toH1Function.gradMemL2 i).integrable_sq
  have hgradInt : IntegrableOn
      (fun x => vecNormSq (u.toH1Function.grad x)) (euclideanBall x₀ R) :=
    integrableOn_vecNormSq_of_memVectorL2On hgradL2
  have hcoord_le_grad :
      (∫ x in euclideanBall x₀ R,
        (u.toH1Function.grad x i) ^ 2 ∂volume) ≤
        ∫ x in euclideanBall x₀ R,
          vecNormSq (u.toH1Function.grad x) ∂volume := by
    apply setIntegral_mono hcoordInt hgradInt
    intro x
    change (u.toH1Function.grad x i) ^ 2 ≤
      vecNormSq (u.toH1Function.grad x)
    rw [vecNormSq_eq_sum_sq]
    exact Finset.single_le_sum
      (fun j _ => sq_nonneg (u.toH1Function.grad x j)) (Finset.mem_univ i)
  calc
    (∫ x in euclideanBall x₀ R, u x ^ 2 ∂volume) ≤
        (2 * R) ^ 2 *
          ∫ x in euclideanBall x₀ R,
            (u.toH1Function.grad x i) ^ 2 ∂volume := hcoord
    _ ≤ (2 * R) ^ 2 *
          ∫ x in euclideanBall x₀ R,
            vecNormSq (u.toH1Function.grad x) ∂volume :=
      mul_le_mul_of_nonneg_left hcoord_le_grad (sq_nonneg (2 * R))

end PDE
