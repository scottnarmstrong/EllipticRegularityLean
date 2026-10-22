module

public import PDEFoundation.Ambient.EuclideanNorm
public import PDEFoundation.Measure.RestrictedVolume
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.MetricSpace.Holder

/-!
# Hölder-seminorm bounds on native vectors

The inherited norm on `Vec d` is the finite-product supremum norm. This module
therefore keeps two explicitly named predicates:

* `SupHolderSeminormLE`, using the inherited supremum norm;
* `EuclideanHolderSeminormLE`, using `vecEuclideanNorm`.

Cube-based Campanato arguments naturally prove the first, while public PDE
estimates should normally expose the second. The conversion from the supremum
bound to the Euclidean bound loses no constant.
-/

@[expose] public section

namespace PDE

open MeasureTheory

variable {d : ℕ}

/-- A Hölder-seminorm bound using the inherited finite-product supremum norm
on `Vec d`. -/
def SupHolderSeminormLE (U : Set (Vec d)) (u : Vec d → ℝ)
    (α K : ℝ) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U,
    |u x - u y| ≤ K * ‖x - y‖ ^ α

/-- A Hölder-seminorm bound using the explicit Euclidean magnitude on
`Vec d`, rather than its inherited supremum norm. -/
def EuclideanHolderSeminormLE (U : Set (Vec d)) (u : Vec d → ℝ)
    (α K : ℝ) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U,
    |u x - u y| ≤ K * vecEuclideanNorm (x - y) ^ α

namespace SupHolderSeminormLE

theorem mono_set {U V : Set (Vec d)} {u : Vec d → ℝ} {α K : ℝ}
    (h : SupHolderSeminormLE U u α K) (hVU : V ⊆ U) :
    SupHolderSeminormLE V u α K :=
  fun x hx y hy => h x (hVU hx) y (hVU hy)

theorem mono_const {U : Set (Vec d)} {u : Vec d → ℝ}
    {α K K' : ℝ}
    (h : SupHolderSeminormLE U u α K) (hKK' : K ≤ K') :
    SupHolderSeminormLE U u α K' := by
  intro x hx y hy
  exact (h x hx y hy).trans
    (mul_le_mul_of_nonneg_right hKK'
      (Real.rpow_nonneg (norm_nonneg (x - y)) α))

end SupHolderSeminormLE

namespace EuclideanHolderSeminormLE

theorem mono_set {U V : Set (Vec d)} {u : Vec d → ℝ} {α K : ℝ}
    (h : EuclideanHolderSeminormLE U u α K) (hVU : V ⊆ U) :
    EuclideanHolderSeminormLE V u α K :=
  fun x hx y hy => h x (hVU hx) y (hVU hy)

theorem mono_const {U : Set (Vec d)} {u : Vec d → ℝ}
    {α K K' : ℝ}
    (h : EuclideanHolderSeminormLE U u α K) (hKK' : K ≤ K') :
    EuclideanHolderSeminormLE U u α K' := by
  intro x hx y hy
  exact (h x hx y hy).trans
    (mul_le_mul_of_nonneg_right hKK'
      (Real.rpow_nonneg (vecEuclideanNorm_nonneg (x - y)) α))

end EuclideanHolderSeminormLE

/-- A supremum-norm Hölder bound implies the Euclidean-distance version with
the identical exponent and constant. -/
theorem supHolderSeminormLE_to_euclidean
    {U : Set (Vec d)} {u : Vec d → ℝ} {α K : ℝ}
    (h : SupHolderSeminormLE U u α K)
    (hα : 0 ≤ α) (hK : 0 ≤ K) :
    EuclideanHolderSeminormLE U u α K := by
  intro x hx y hy
  refine (h x hx y hy).trans
    (mul_le_mul_of_nonneg_left ?_ hK)
  exact Real.rpow_le_rpow (norm_nonneg (x - y))
    (norm_le_vecEuclideanNorm (x - y)) hα

/-- A Euclidean Hölder bound also yields a supremum-norm bound, with the
explicit norm-equivalence factor `(sqrt d) ^ α`. -/
theorem euclideanHolderSeminormLE_to_sup
    {U : Set (Vec d)} {u : Vec d → ℝ} {α K : ℝ}
    (h : EuclideanHolderSeminormLE U u α K)
    (hα : 0 ≤ α) (hK : 0 ≤ K) :
    SupHolderSeminormLE U u α
      (K * Real.sqrt d ^ α) := by
  intro x hx y hy
  calc
    |u x - u y| ≤
        K * vecEuclideanNorm (x - y) ^ α :=
      h x hx y hy
    _ ≤ K * (Real.sqrt d * ‖x - y‖) ^ α :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow
          (vecEuclideanNorm_nonneg (x - y))
          (vecEuclideanNorm_le_sqrt_natCast_mul_norm (x - y))
          hα)
        hK
    _ = (K * Real.sqrt d ^ α) * ‖x - y‖ ^ α := by
      rw [Real.mul_rpow (Real.sqrt_nonneg _) (norm_nonneg _)]
      ring

/-- A supremum-norm Hölder bound supplies Mathlib's local Hölder predicate. -/
theorem supHolderSeminormLE_to_holderOnWith
    {U : Set (Vec d)} {u : Vec d → ℝ} {α K : ℝ}
    (h : SupHolderSeminormLE U u α K)
    (hα : 0 ≤ α) (hK : 0 ≤ K) :
    HolderOnWith ⟨K, hK⟩ ⟨α, hα⟩ u U := by
  let exponent : NNReal := ⟨α, hα⟩
  let constant : NNReal := ⟨K, hK⟩
  change HolderOnWith constant exponent u U
  intro x hx y hy
  have hbound := h x hx y hy
  have hdist :
      edist x y = ENNReal.ofReal ‖x - y‖ := by
    rw [edist_dist, dist_eq_norm]
  have hvalue :
      edist (u x) (u y) =
        ENNReal.ofReal |u x - u y| := by
    rw [edist_dist, Real.dist_eq]
  rw [hvalue, hdist,
    ENNReal.ofReal_rpow_of_nonneg
      (norm_nonneg (x - y)) exponent.coe_nonneg,
    ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul constant.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal
    (by simpa only [exponent, constant] using! hbound)

/-- A positive-exponent supremum-norm Hölder estimate implies continuity on
the stated set. -/
theorem SupHolderSeminormLE.continuousOn
    {U : Set (Vec d)} {u : Vec d → ℝ} {α K : ℝ}
    (h : SupHolderSeminormLE U u α K)
    (hα : 0 < α) (hK : 0 ≤ K) :
    ContinuousOn u U :=
  (supHolderSeminormLE_to_holderOnWith h hα.le hK).continuousOn
    (show 0 < (⟨α, hα.le⟩ : NNReal) by exact hα)

/-- A positive-exponent Euclidean Hölder estimate also implies continuity on
the stated set. -/
theorem EuclideanHolderSeminormLE.continuousOn
    {U : Set (Vec d)} {u : Vec d → ℝ} {α K : ℝ}
    (h : EuclideanHolderSeminormLE U u α K)
    (hα : 0 < α) (hK : 0 ≤ K) :
    ContinuousOn u U := by
  apply
    (euclideanHolderSeminormLE_to_sup h hα.le hK).continuousOn
  · exact hα
  · exact mul_nonneg hK
      (Real.rpow_nonneg (Real.sqrt_nonneg _) α)

/-- A Euclidean Hölder representative together with its a.e. agreement on
the stated set. -/
def HasEuclideanHolderRepresentativeOn
    (U : Set (Vec d)) (u : Vec d → ℝ) (α K : ℝ) : Prop :=
  ∃ representative : Vec d → ℝ,
    representative =ᵐ[volumeOn U] u ∧
      EuclideanHolderSeminormLE U representative α K

/-- A pointwise Euclidean Hölder bound packages the function itself as its
own representative. -/
theorem EuclideanHolderSeminormLE.hasRepresentative
    {U : Set (Vec d)} {u : Vec d → ℝ} {α K : ℝ}
    (h : EuclideanHolderSeminormLE U u α K) :
    HasEuclideanHolderRepresentativeOn U u α K :=
  ⟨u, Filter.Eventually.of_forall fun _ => rfl, h⟩

end PDE
