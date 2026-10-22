module

public import PDEFoundation.Geometry.AxisBox
public import PDEFoundation.Sobolev.Cutoff.Basic
public import PDEFoundation.Sobolev.Cutoff.Profile
public import PDEFoundation.Sobolev.Cutoff.AxisBox
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Smooth cutoffs on centered axis cubes

The cutoff is a product of one-dimensional lower and upper transitions. Its
topological support lies in the cube of half-side `3r/2`, and its explicit
Euclidean gradient bound is `32 * d / r`.
-/

@[expose] public section

noncomputable section

namespace PDE

/-- The product of the lower and upper smooth transitions on an interval. -/
def cubeCutoffScalarFactor (a b δ t : ℝ) : ℝ :=
  axisBoxLowerTransition a δ t * axisBoxUpperTransition b δ t

/-- The one-dimensional factor used in the cutoff on a centered cube. -/
def centeredCubeCutoffScalarFactor (x₀ᵢ r t : ℝ) : ℝ :=
  cubeCutoffScalarFactor (x₀ᵢ - 2 * r) (x₀ᵢ + 2 * r) r t

/-- The coordinate factor in the product cutoff on a centered cube. -/
def centeredCubeCutoffFactor {d : ℕ} (x₀ : Vec d) (r : ℝ)
    (i : Fin d) (x : Vec d) : ℝ :=
  centeredCubeCutoffScalarFactor (x₀ i) r (x i)

/-- The smooth product cutoff equal to one on the closed cube of half-side `r`.
-/
def centeredCubeCutoff {d : ℕ} (x₀ : Vec d) (r : ℝ) : Vec d → ℝ :=
  fun x => ∏ i : Fin d, centeredCubeCutoffFactor x₀ r i x

/-- The compactly supported closed box containing the support of the product
cutoff. -/
def centeredCubeCutoffSupportBox {d : ℕ}
    (x₀ : Vec d) (r : ℝ) : Set (Vec d) :=
  Set.pi Set.univ fun i => Set.Icc (x₀ i - 3 * r / 2) (x₀ i + 3 * r / 2)

theorem cubeCutoffScalarFactor_smooth (a b δ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (cubeCutoffScalarFactor a b δ) := by
  unfold cubeCutoffScalarFactor axisBoxLowerTransition axisBoxUpperTransition
  have hLower : ContDiff ℝ (⊤ : ℕ∞)
      (fun t : ℝ => smoothTransitionProfile ((t - a) / (δ / 2) - 1)) := by
    exact smoothTransitionProfile.smooth.comp
      (((contDiff_id.sub contDiff_const).div_const _).sub contDiff_const)
  have hUpper : ContDiff ℝ (⊤ : ℕ∞)
      (fun t : ℝ => smoothTransitionProfile ((b - t) / (δ / 2) - 1)) := by
    exact smoothTransitionProfile.smooth.comp
      (((contDiff_const.sub contDiff_id).div_const _).sub contDiff_const)
  exact hLower.mul hUpper

theorem cubeCutoffScalarFactor_nonneg (a b δ t : ℝ) :
    0 ≤ cubeCutoffScalarFactor a b δ t := by
  exact mul_nonneg (axisBoxLowerTransition_nonneg _ _ _)
    (axisBoxUpperTransition_nonneg _ _ _)

theorem cubeCutoffScalarFactor_le_one (a b δ t : ℝ) :
    cubeCutoffScalarFactor a b δ t ≤ 1 := by
  exact (mul_le_of_le_one_left (axisBoxUpperTransition_nonneg _ _ _)
      (axisBoxLowerTransition_le_one _ _ _)).trans
    (axisBoxUpperTransition_le_one _ _ _)

theorem centeredCubeCutoffScalarFactor_eq_one
    {x₀ᵢ r t : ℝ} (hr : 0 < r)
    (ht : x₀ᵢ - r ≤ t ∧ t ≤ x₀ᵢ + r) :
    centeredCubeCutoffScalarFactor x₀ᵢ r t = 1 := by
  unfold centeredCubeCutoffScalarFactor cubeCutoffScalarFactor
  have hLower := axisBoxLowerTransition_eq_one_of_add_delta_le
    (a := x₀ᵢ - 2 * r) (δ := r) (t := t) hr (by linarith [ht.1])
  have hUpper := axisBoxUpperTransition_eq_one_of_add_delta_le
    (b := x₀ᵢ + 2 * r) (δ := r) (t := t) hr (by linarith [ht.2])
  simp only [hLower, hUpper, mul_one]

theorem centeredCubeCutoffScalarFactor_zero_of_le
    {x₀ᵢ r t : ℝ} (hr : 0 < r)
    (ht : t ≤ x₀ᵢ - 3 * r / 2) :
    centeredCubeCutoffScalarFactor x₀ᵢ r t = 0 := by
  unfold centeredCubeCutoffScalarFactor cubeCutoffScalarFactor
  have hLower := axisBoxLowerTransition_eq_zero_of_le_add_half_delta
    (a := x₀ᵢ - 2 * r) (δ := r) (t := t) hr (by linarith [ht])
  simp only [hLower, zero_mul]

theorem centeredCubeCutoffScalarFactor_zero_of_ge
    {x₀ᵢ r t : ℝ} (hr : 0 < r)
    (ht : x₀ᵢ + 3 * r / 2 ≤ t) :
    centeredCubeCutoffScalarFactor x₀ᵢ r t = 0 := by
  unfold centeredCubeCutoffScalarFactor cubeCutoffScalarFactor
  have hUpper := axisBoxUpperTransition_eq_zero_of_sub_half_delta_le
    (b := x₀ᵢ + 2 * r) (δ := r) (t := t) hr (by linarith [ht])
  simp only [hUpper, mul_zero]

theorem cubeCutoffScalarFactor_hasDerivAt_lower
    {a δ t : ℝ} :
    HasDerivAt (axisBoxLowerTransition a δ)
      (deriv smoothTransitionProfile ((t - a) / (δ / 2) - 1) *
        (δ / 2)⁻¹) t := by
  have hargument : HasDerivAt (fun s : ℝ => (s - a) / (δ / 2) - 1)
      ((δ / 2)⁻¹) t := by
    have h := (((hasDerivAt_id' t).sub_const a).div_const (δ / 2)).sub_const 1
    rw [one_div] at h
    exact h
  have hprofile : HasDerivAt smoothTransitionProfile
      (deriv smoothTransitionProfile ((t - a) / (δ / 2) - 1))
      ((t - a) / (δ / 2) - 1) :=
    (smoothTransitionProfile.smooth.differentiable (by simp)
      ((t - a) / (δ / 2) - 1)).hasDerivAt
  simpa only [axisBoxLowerTransition, Function.comp_apply] using!
    hprofile.comp t hargument

theorem cubeCutoffScalarFactor_hasDerivAt_upper
    {b δ t : ℝ} :
    HasDerivAt (axisBoxUpperTransition b δ)
      (deriv smoothTransitionProfile ((b - t) / (δ / 2) - 1) *
        (-(δ / 2)⁻¹)) t := by
  have hargument : HasDerivAt (fun s : ℝ => (b - s) / (δ / 2) - 1)
      (-(δ / 2)⁻¹) t := by
    have h := (((hasDerivAt_id' t).const_sub b).div_const (δ / 2)).sub_const 1
    rw [neg_div, one_div] at h
    exact h
  have hprofile : HasDerivAt smoothTransitionProfile
      (deriv smoothTransitionProfile ((b - t) / (δ / 2) - 1))
      ((b - t) / (δ / 2) - 1) :=
    (smoothTransitionProfile.smooth.differentiable (by simp)
      ((b - t) / (δ / 2) - 1)).hasDerivAt
  simpa only [axisBoxUpperTransition, Function.comp_apply] using!
    hprofile.comp t hargument

theorem abs_deriv_axisBoxLowerTransition_le
    {a δ t : ℝ} (hδ : 0 < δ) :
    |deriv (axisBoxLowerTransition a δ) t| ≤ 16 / δ := by
  rw [cubeCutoffScalarFactor_hasDerivAt_lower.deriv]
  have hhalf : 0 < δ / 2 := by linarith
  have hinv : |(δ / 2)⁻¹| = 2 / δ := by
    rw [abs_inv, abs_of_pos hhalf, inv_div]
  rw [abs_mul, hinv]
  calc
    |deriv smoothTransitionProfile ((t - a) / (δ / 2) - 1)| * (2 / δ) ≤
        8 * (2 / δ) :=
      mul_le_mul_of_nonneg_right
        (smoothTransitionProfile.abs_deriv_le_eight _)
        (by positivity)
    _ = 16 / δ := by ring

theorem abs_deriv_axisBoxUpperTransition_le
    {b δ t : ℝ} (hδ : 0 < δ) :
    |deriv (axisBoxUpperTransition b δ) t| ≤ 16 / δ := by
  rw [cubeCutoffScalarFactor_hasDerivAt_upper.deriv]
  have hhalf : 0 < δ / 2 := by linarith
  have hinv : |-(δ / 2)⁻¹| = 2 / δ := by
    rw [abs_neg, abs_inv, abs_of_pos hhalf, inv_div]
  rw [abs_mul, hinv]
  calc
    |deriv smoothTransitionProfile ((b - t) / (δ / 2) - 1)| * (2 / δ) ≤
        8 * (2 / δ) :=
      mul_le_mul_of_nonneg_right
        (smoothTransitionProfile.abs_deriv_le_eight _)
        (by positivity)
    _ = 16 / δ := by ring

theorem cubeCutoffScalarFactor_hasDerivAt
    {a b δ t : ℝ} :
    HasDerivAt (cubeCutoffScalarFactor a b δ)
      (deriv (axisBoxLowerTransition a δ) t * axisBoxUpperTransition b δ t +
        axisBoxLowerTransition a δ t * deriv (axisBoxUpperTransition b δ) t) t := by
  change HasDerivAt
    (axisBoxLowerTransition a δ * axisBoxUpperTransition b δ) _ t
  have hlower := cubeCutoffScalarFactor_hasDerivAt_lower (a := a) (δ := δ) (t := t)
  have hupper := cubeCutoffScalarFactor_hasDerivAt_upper (b := b) (δ := δ) (t := t)
  rw [hlower.deriv, hupper.deriv]
  exact hlower.mul hupper

theorem abs_deriv_cubeCutoffScalarFactor_le
    {a b δ t : ℝ} (hδ : 0 < δ) :
    |deriv (cubeCutoffScalarFactor a b δ) t| ≤ 32 / δ := by
  rw [cubeCutoffScalarFactor_hasDerivAt.deriv]
  calc
    |deriv (axisBoxLowerTransition a δ) t * axisBoxUpperTransition b δ t +
        axisBoxLowerTransition a δ t * deriv (axisBoxUpperTransition b δ) t| ≤
      |deriv (axisBoxLowerTransition a δ) t * axisBoxUpperTransition b δ t| +
        |axisBoxLowerTransition a δ t * deriv (axisBoxUpperTransition b δ) t| :=
      abs_add_le _ _
    _ = |deriv (axisBoxLowerTransition a δ) t| *
          |axisBoxUpperTransition b δ t| +
        |axisBoxLowerTransition a δ t| *
          |deriv (axisBoxUpperTransition b δ) t| := by
      rw [abs_mul, abs_mul]
    _ ≤ (16 / δ) * 1 + 1 * (16 / δ) := by
      gcongr
      · exact abs_deriv_axisBoxLowerTransition_le hδ
      · rw [abs_of_nonneg (axisBoxUpperTransition_nonneg _ _ _)]
        exact axisBoxUpperTransition_le_one _ _ _
      · rw [abs_of_nonneg (axisBoxLowerTransition_nonneg _ _ _)]
        exact axisBoxLowerTransition_le_one _ _ _
      · exact abs_deriv_axisBoxUpperTransition_le hδ
    _ = 32 / δ := by ring

theorem centeredCubeCutoffScalarFactor_deriv_bound
    {x₀ᵢ r t : ℝ} (hr : 0 < r) :
    |deriv (centeredCubeCutoffScalarFactor x₀ᵢ r) t| ≤ 32 / r := by
  exact abs_deriv_cubeCutoffScalarFactor_le hr

theorem centeredCubeCutoffFactor_smooth {d : ℕ}
    (x₀ : Vec d) (r : ℝ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (centeredCubeCutoffFactor x₀ r i) := by
  change ContDiff ℝ (⊤ : ℕ∞)
    (centeredCubeCutoffScalarFactor (x₀ i) r ∘ fun x : Vec d => x i)
  have hscalar : ContDiff ℝ (⊤ : ℕ∞)
      (centeredCubeCutoffScalarFactor (x₀ i) r) := by
    unfold centeredCubeCutoffScalarFactor
    exact cubeCutoffScalarFactor_smooth (x₀ i - 2 * r) (x₀ i + 2 * r) r
  exact hscalar.comp (contDiff_apply ℝ ℝ i)

theorem centeredCubeCutoffFactor_nonneg {d : ℕ}
    (x₀ : Vec d) (r : ℝ) (i : Fin d) (x : Vec d) :
    0 ≤ centeredCubeCutoffFactor x₀ r i x := by
  exact cubeCutoffScalarFactor_nonneg _ _ _ _

theorem centeredCubeCutoffFactor_le_one {d : ℕ}
    (x₀ : Vec d) (r : ℝ) (i : Fin d) (x : Vec d) :
    centeredCubeCutoffFactor x₀ r i x ≤ 1 := by
  exact cubeCutoffScalarFactor_le_one _ _ _ _

theorem centeredCubeCutoffFactor_zero_of_le {d : ℕ}
    (x₀ : Vec d) {r : ℝ} (hr : 0 < r) (i : Fin d) (x : Vec d)
    (hx : x i ≤ x₀ i - 3 * r / 2) :
    centeredCubeCutoffFactor x₀ r i x = 0 :=
  centeredCubeCutoffScalarFactor_zero_of_le hr hx

theorem centeredCubeCutoffFactor_zero_of_ge {d : ℕ}
    (x₀ : Vec d) {r : ℝ} (hr : 0 < r) (i : Fin d) (x : Vec d)
    (hx : x₀ i + 3 * r / 2 ≤ x i) :
    centeredCubeCutoffFactor x₀ r i x = 0 :=
  centeredCubeCutoffScalarFactor_zero_of_ge hr hx

theorem centeredCubeCutoff_smooth {d : ℕ}
    (x₀ : Vec d) (r : ℝ) :
  ContDiff ℝ (⊤ : ℕ∞) (centeredCubeCutoff x₀ r) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x =>
    ∏ i ∈ Finset.univ, centeredCubeCutoffFactor x₀ r i x)
  exact contDiff_prod fun i _hi => centeredCubeCutoffFactor_smooth x₀ r i

theorem centeredCubeCutoff_support_subset
    {d : ℕ} {x₀ : Vec d} {r : ℝ} (hr : 0 < r) :
    Function.support (centeredCubeCutoff x₀ r) ⊆
      centeredCubeCutoffSupportBox x₀ r := by
  intro x hx i _
  have hprod : (∏ j ∈ Finset.univ, centeredCubeCutoffFactor x₀ r j x) ≠ 0 := hx
  have hfactor : centeredCubeCutoffFactor x₀ r i x ≠ 0 := by
    intro hz
    exact hprod (Finset.prod_eq_zero (Finset.mem_univ i) hz)
  constructor
  · by_contra hnot
    exact hfactor (centeredCubeCutoffFactor_zero_of_le x₀ hr i x
      (le_of_not_ge hnot))
  · by_contra hnot
    exact hfactor (centeredCubeCutoffFactor_zero_of_ge x₀ hr i x
      (le_of_not_ge hnot))

theorem centeredCubeCutoffSupportBox_isCompact
    {d : ℕ} (x₀ : Vec d) (r : ℝ) :
    IsCompact (centeredCubeCutoffSupportBox x₀ r) := by
  unfold centeredCubeCutoffSupportBox
  exact isCompact_univ_pi fun i => isCompact_Icc

theorem centeredCubeCutoff_tsupport_subset
    {d : ℕ} (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    tsupport (centeredCubeCutoff x₀ r) ⊆ centeredAxisCube x₀ (2 * r) := by
  have hclosed : IsClosed (centeredCubeCutoffSupportBox x₀ r) :=
    (centeredCubeCutoffSupportBox_isCompact x₀ r).isClosed
  have htsub : tsupport (centeredCubeCutoff x₀ r) ⊆
      centeredCubeCutoffSupportBox x₀ r :=
    closure_minimal (centeredCubeCutoff_support_subset hr) hclosed
  intro x hx i _
  have hi := htsub hx i (Set.mem_univ i)
  change x₀ i - 3 * r / 2 ≤ x i ∧ x i ≤ x₀ i + 3 * r / 2 at hi
  change x₀ i - 2 * r < x i ∧ x i < x₀ i + 2 * r
  constructor <;> linarith

theorem centeredCubeCutoff_eq_one_on_inner
    {d : ℕ} {x₀ : Vec d} {r : ℝ} (hr : 0 < r)
    {x : Vec d} (hx : x ∈ closedCenteredAxisCube x₀ r) :
    centeredCubeCutoff x₀ r x = 1 := by
  unfold centeredCubeCutoff
  apply Finset.prod_eq_one
  intro i _
  have hi := hx i (Set.mem_univ i)
  change x₀ i - r ≤ x i ∧ x i ≤ x₀ i + r at hi
  exact centeredCubeCutoffScalarFactor_eq_one hr hi

theorem fderiv_centeredCubeCutoffFactor_apply
    {d : ℕ} (x₀ : Vec d) (r : ℝ) (i j : Fin d) (x : Vec d) :
    (fderiv ℝ (centeredCubeCutoffFactor x₀ r i) x) (basisVec j) =
      deriv (centeredCubeCutoffScalarFactor (x₀ i) r) (x i) * basisVec j i := by
  have hscalar_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (centeredCubeCutoffScalarFactor (x₀ i) r) := by
    unfold centeredCubeCutoffScalarFactor
    exact cubeCutoffScalarFactor_smooth (x₀ i - 2 * r) (x₀ i + 2 * r) r
  have hscalar_diff : DifferentiableAt ℝ
      (centeredCubeCutoffScalarFactor (x₀ i) r) (x i) :=
    (hscalar_smooth.differentiable (by simp)).differentiableAt
  have hscalar : HasDerivAt (centeredCubeCutoffScalarFactor (x₀ i) r)
      (deriv (centeredCubeCutoffScalarFactor (x₀ i) r) (x i)) (x i) :=
    hscalar_diff.hasDerivAt
  have hcoord : HasFDerivAt (fun y : Vec d => y i)
      ((ContinuousLinearMap.proj i) : Vec d →L[ℝ] ℝ) x :=
    hasFDerivAt_apply (𝕜 := ℝ) i x
  have hcomp := hscalar.comp_hasFDerivAt x hcoord
  change (fderiv ℝ
    (centeredCubeCutoffScalarFactor (x₀ i) r ∘ fun y : Vec d => y i) x)
      (basisVec j) = _
  rw [hcomp.fderiv]
  simp only [smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

theorem classicalGradient_centeredCubeCutoff_apply
    {d : ℕ} {x₀ : Vec d} {r : ℝ} (hr : 0 < r) {j : Fin d} (x : Vec d) :
    |classicalGradient (centeredCubeCutoff x₀ r) x j| ≤ 32 / r := by
  rw [classicalGradient_apply]
  change |(fderiv ℝ (fun y =>
    ∏ i ∈ Finset.univ, centeredCubeCutoffFactor x₀ r i y) x) (basisVec j)| ≤ 32 / r
  rw [fderiv_finsetProd (fun i _ =>
    ((centeredCubeCutoffFactor_smooth x₀ r i).differentiable (by simp) x))]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp only [fderiv_centeredCubeCutoffFactor_apply, basisVec_apply,
      ite_true, mul_one]
    rw [abs_mul, abs_of_nonneg]
    · calc
        (∏ i ∈ Finset.univ.erase j, centeredCubeCutoffFactor x₀ r i x) *
            |deriv (centeredCubeCutoffScalarFactor (x₀ j) r) (x j)| ≤
          1 * (32 / r) := by
            have hprod_le_one :
                (∏ i ∈ Finset.univ.erase j,
                  centeredCubeCutoffFactor x₀ r i x) ≤ 1 :=
              Finset.prod_le_one₀
                (fun i _ => centeredCubeCutoffFactor_nonneg x₀ r i x)
                (fun i _ => centeredCubeCutoffFactor_le_one x₀ r i x)
            have hderiv := centeredCubeCutoffScalarFactor_deriv_bound
              (x₀ᵢ := x₀ j) (r := r) (t := x j) hr
            exact mul_le_mul hprod_le_one hderiv (abs_nonneg _) (by norm_num)
      _ = 32 / r := by ring
    · exact Finset.prod_nonneg fun i _ =>
        centeredCubeCutoffFactor_nonneg x₀ r i x
  · intro i hi hij
    have hcoord := fderiv_centeredCubeCutoffFactor_apply x₀ r i j x
    rw [hcoord]
    simp [basisVec_apply, hij]
  · simp

theorem centeredCubeCutoff_gradient_bound
    {d : ℕ} {x₀ : Vec d} {r : ℝ} (hr : 0 < r) (x : Vec d) :
    vecEuclideanNorm (classicalGradient (centeredCubeCutoff x₀ r) x) ≤
      (32 * (d : ℝ)) / r := by
  calc
    vecEuclideanNorm (classicalGradient (centeredCubeCutoff x₀ r) x) ≤
        ∑ i : Fin d, |classicalGradient (centeredCubeCutoff x₀ r) x i| :=
      vecEuclideanNorm_le_sum_abs _
    _ ≤ ∑ _i : Fin d, 32 / r := by
      apply Finset.sum_le_sum
      intro i _
      exact classicalGradient_centeredCubeCutoff_apply hr x
    _ = (32 * (d : ℝ)) / r := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring

/-- A quantitative smooth cutoff equal to one on the closed cube of half-side
`r`, supported in the open cube of half-side `2r`. Its gradient constant is
`32 * d / r`, depending only on the dimension and scale. -/
noncomputable def quantitativeCenteredAxisCubeCutoff {d : ℕ}
    (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    QuantitativeSmoothCutoff
      (closedCenteredAxisCube x₀ r)
      (centeredAxisCube x₀ (2 * r)) ((32 * (d : ℝ)) / r) where
  toFun := centeredCubeCutoff x₀ r
  smooth := centeredCubeCutoff_smooth x₀ r
  hasCompactSupport := HasCompactSupport.of_support_subset_isCompact
    (centeredCubeCutoffSupportBox_isCompact x₀ r)
    (centeredCubeCutoff_support_subset hr)
  tsupport_subset := centeredCubeCutoff_tsupport_subset x₀ hr
  nonneg := fun x => by
    change 0 ≤ ∏ i ∈ Finset.univ, centeredCubeCutoffFactor x₀ r i x
    exact Finset.prod_nonneg fun i _ =>
      centeredCubeCutoffFactor_nonneg x₀ r i x
  le_one := fun x => by
    change ∏ i ∈ Finset.univ, centeredCubeCutoffFactor x₀ r i x ≤ 1
    exact Finset.prod_le_one₀
      (fun i _ => centeredCubeCutoffFactor_nonneg x₀ r i x)
      (fun i _ => centeredCubeCutoffFactor_le_one x₀ r i x)
  eq_one_on_inner := fun x hx => centeredCubeCutoff_eq_one_on_inner hr hx
  gradient_bound := centeredCubeCutoff_gradient_bound hr

end PDE
