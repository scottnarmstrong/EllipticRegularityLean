module

public import EllipticRegularity.Parabolic.Cauchy.Weights.TruncatedDistance
public import EllipticRegularity.Parabolic.Cauchy.Energy.Global
public import Mathlib.Tactic.Linarith

/-!
# Geometry and weighted slices for the Nash--Aronson estimate

This module connects separated initial supports to the pointwise distance
condition in weighted Cauchy--Schwarz, and records that a bounded truncated
Gaussian weight preserves the global `L²` property of a solution slice.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Weights

open MeasureTheory Set

variable {d : ℕ}

private theorem euclideanSetDistance_range_nonempty_local {K : Set (Vec d)}
    (hK : K.Nonempty) (x : Vec d) :
    (Set.range fun y : K => vecEuclideanNorm (x - (y : Vec d))).Nonempty := by
  rcases hK with ⟨y, hy⟩
  exact ⟨vecEuclideanNorm (x - y), ⟨⟨y, hy⟩, rfl⟩⟩

private theorem euclideanSetDistance_bddBelow_local (K : Set (Vec d)) (x : Vec d) :
    BddBelow (Set.range fun y : K => vecEuclideanNorm (x - (y : Vec d))) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact vecEuclideanNorm_nonneg _

private theorem euclideanSetDistance_le_local {K : Set (Vec d)}
    (x : Vec d) (y : K) :
    euclideanSetDistance K x ≤ vecEuclideanNorm (x - (y : Vec d)) := by
  exact csInf_le (euclideanSetDistance_bddBelow_local K x) ⟨y, rfl⟩

/-- Separation of two nonempty sets implies a lower bound on the sum of their
Euclidean distance functions at every point. -/
theorem euclideanSetDistance_sum_ge_of_separated
    {K₁ K₂ : Set (Vec d)} {r : ℝ}
    (hK₁ : K₁.Nonempty) (hK₂ : K₂.Nonempty) (hr : 0 ≤ r)
    (hsep : ∀ x ∈ K₁, ∀ y ∈ K₂, r ^ 2 ≤ euclideanSqDist x y)
    (z : Vec d) :
    r ≤ euclideanSetDistance K₁ z + euclideanSetDistance K₂ z := by
  have hK₂range := euclideanSetDistance_range_nonempty_local hK₂ z
  have hK₁range := euclideanSetDistance_range_nonempty_local hK₁ z
  have hnormsep (x : K₁) (y : K₂) :
      r ≤ vecEuclideanNorm ((x : Vec d) - (y : Vec d)) := by
    have hsq := hsep x x.property y y.property
    change r ^ 2 ≤ vecNormSq ((x : Vec d) - (y : Vec d)) at hsq
    rw [← vecEuclideanNorm_sq] at hsq
    exact (sq_le_sq₀ hr (vecEuclideanNorm_nonneg _)).mp hsq
  have hfirst (x : K₁) : r - vecEuclideanNorm ((x : Vec d) - z) ≤
      euclideanSetDistance K₂ z := by
    apply le_csInf hK₂range
    rintro _ ⟨y, rfl⟩
    have htri : vecEuclideanNorm ((x : Vec d) - (y : Vec d)) ≤
        vecEuclideanNorm ((x : Vec d) - z) + vecEuclideanNorm (z - (y : Vec d)) := by
      rw [show (x : Vec d) - (y : Vec d) = ((x : Vec d) - z) + (z - (y : Vec d)) by abel]
      exact vecEuclideanNorm_add_le _ _
    linarith [hnormsep x y, htri]
  have hsecond : r - euclideanSetDistance K₂ z ≤ euclideanSetDistance K₁ z := by
    apply le_csInf hK₁range
    rintro _ ⟨x, rfl⟩
    have hx := hfirst x
    have hnorm : vecEuclideanNorm ((x : Vec d) - z) =
        vecEuclideanNorm (z - (x : Vec d)) := by
      exact vecEuclideanNorm_sub_comm _ _
    rw [hnorm] at hx
    linarith
  linarith

/-- Capping both support distances at any radius at least the support
separation preserves the pointwise sum lower bound. -/
theorem truncatedEuclideanSetDistance_sum_ge_of_separated
    {K₁ K₂ : Set (Vec d)} {r R : ℝ}
    (hK₁ : K₁.Nonempty) (hK₂ : K₂.Nonempty)
    (hr : 0 ≤ r) (hR : r ≤ R)
    (hsep : ∀ x ∈ K₁, ∀ y ∈ K₂, r ^ 2 ≤ euclideanSqDist x y)
    (z : Vec d) :
    r ≤ truncatedEuclideanSetDistance K₁ R z +
      truncatedEuclideanSetDistance K₂ R z := by
  have hd₁ := euclideanSetDistance_nonneg hK₁ z
  have hd₂ := euclideanSetDistance_nonneg hK₂ z
  have hsum := euclideanSetDistance_sum_ge_of_separated hK₁ hK₂ hr hsep z
  by_cases h₁ : R ≤ euclideanSetDistance K₁ z
  · change r ≤ min R (euclideanSetDistance K₁ z) + min R (euclideanSetDistance K₂ z)
    rw [min_eq_left h₁]
    have hcap : 0 ≤ truncatedEuclideanSetDistance K₂ R z :=
      truncatedEuclideanSetDistance_nonneg hK₂ (le_trans hr hR) z
    change 0 ≤ min R (euclideanSetDistance K₂ z) at hcap
    linarith
  · by_cases h₂ : R ≤ euclideanSetDistance K₂ z
    · change r ≤ min R (euclideanSetDistance K₁ z) + min R (euclideanSetDistance K₂ z)
      rw [min_eq_right (le_of_not_ge h₁), min_eq_left h₂]
      have hcap : 0 ≤ truncatedEuclideanSetDistance K₁ R z :=
        truncatedEuclideanSetDistance_nonneg hK₁ (le_trans hr hR) z
      change 0 ≤ min R (euclideanSetDistance K₁ z) at hcap
      linarith
    · change r ≤ min R (euclideanSetDistance K₁ z) + min R (euclideanSetDistance K₂ z)
      rw [min_eq_right (le_of_not_ge h₁), min_eq_right (le_of_not_ge h₂)]
      exact hsum

private theorem cauchy_slice_aestronglyMeasurable_local {s T t : ℝ}
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T)) (ht : t ∈ Icc s T) :
    AEStronglyMeasurable (fun x : Vec d => u.toFun (x, t)) volume := by
  let K : ℕ → Set (Vec d) := fun n => euclideanClosedBall 0 ((n : ℝ) + 1)
  have hcover : (⋃ n, K n) = (univ : Set (Vec d)) := by
    ext x
    constructor
    · intro _
      exact mem_univ x
    · intro _
      obtain ⟨N, hN⟩ := exists_nat_gt (vecEuclideanNorm x)
      refine mem_iUnion.mpr ⟨N, ?_⟩
      change x ∈ euclideanClosedBall 0 ((N : ℝ) + 1)
      apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
      rw [sub_zero]
      linarith
  have hloc : ∀ n, AEStronglyMeasurable (fun x : Vec d => u.toFun (x, t))
      (volume.restrict (K n)) := by
    intro n
    exact (u.sliceL2loc t ht (K n)
      (isCompact_euclideanClosedBall 0 (by positivity)) (subset_univ _)).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun x : Vec d => u.toFun (x, t))
      (volume.restrict (⋃ n, K n)) := AEStronglyMeasurable.iUnion hloc
  rw [show volume.restrict (⋃ n, K n) = volume by rw [hcover, Measure.restrict_univ]] at hmeas
  exact hmeas

/-- Every-time slices of a whole-space Cauchy energy solution belong to
global `L²`. -/
theorem cauchy_slice_memLp_of_solution
    {s T t Lam : ℝ} (hT : s < T) (ht : t ∈ Icc s T)
    {a : ParCoeffField d} {f : Vec d → ℝ}
    (ha : IsParabolicCoeff 1 Lam a univ (Icc s T)) (hf : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) :
    MemLp (fun x : Vec d => u.toFun (x, t)) 2 volume := by
  have hsq := PDE.Parabolic.Cauchy.Energy.cauchy_slice_square_integrable
    hT ha f hf u hu ht
  rw [memLp_two_iff_integrable_sq (cauchy_slice_aestronglyMeasurable_local u ht)]
  exact hsq

/-- Multiplication by a bounded truncated Gaussian weight preserves `L²` for
every solution slice, including the endpoint slices. -/
theorem cauchy_nash_truncated_weighted_slice_memLp
    {s T t A H R Lam : ℝ} (hT : s < T) (hA : 0 < A) (hH : 0 < H)
    (hR : 0 ≤ R) (ht : t ∈ Icc s T)
    {a : ParCoeffField d} {f : Vec d → ℝ}
    (ha : IsParabolicCoeff 1 Lam a univ (Icc s T))
    (hf : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) (K : Set (Vec d)) (hK : K.Nonempty) :
    MemLp (fun x : Vec d =>
      Real.exp (truncatedEuclideanSetDistance K R x ^ 2 / (4 * A * H)) *
        u.toFun (x, t)) 2 volume := by
  have huMem := cauchy_slice_memLp_of_solution hT ht ha hf u hu
  let W : Vec d → ℝ := fun x =>
    Real.exp (truncatedEuclideanSetDistance K R x ^ 2 / (4 * A * H))
  have hWmeas : AEStronglyMeasurable W volume := by
    have hρcont : Continuous (truncatedEuclideanSetDistance K R) :=
      (truncatedEuclideanSetDistance_eucLip hK).continuous (by norm_num)
    have hcont : Continuous W := by
      dsimp [W]
      fun_prop
    exact hcont.aestronglyMeasurable
  let C : ℝ := Real.exp (R ^ 2 / (4 * A * H))
  have hWbound : ∀ᵐ x ∂volume, ‖W x‖ ≤ C := by
    filter_upwards [] with x
    have hρ0 := truncatedEuclideanSetDistance_nonneg hK hR x
    have hρR := truncatedEuclideanSetDistance_le (K := K) (R := R) x
    have hρsq : truncatedEuclideanSetDistance K R x ^ 2 ≤ R ^ 2 := by
      nlinarith [sq_nonneg (truncatedEuclideanSetDistance K R x - R)]
    have hden : 0 < 4 * A * H := by positivity
    have harg : truncatedEuclideanSetDistance K R x ^ 2 / (4 * A * H) ≤
        R ^ 2 / (4 * A * H) := div_le_div_of_nonneg_right hρsq hden.le
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.mpr harg
  have hprodMeas : AEStronglyMeasurable (fun x : Vec d => W x * u.toFun (x, t)) volume :=
    hWmeas.mul huMem.aestronglyMeasurable
  have hprodBound : ∀ᵐ x ∂volume,
      ‖W x * u.toFun (x, t)‖ ≤ C * ‖u.toFun (x, t)‖ := by
    filter_upwards [hWbound] with x hx
    rw [Real.norm_eq_abs] at hx
    have hWnn : 0 ≤ W x := by
      dsimp [W]
      exact Real.exp_nonneg _
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hWnn] using
      mul_le_mul_of_nonneg_right hx (abs_nonneg (u.toFun (x, t)))
  have hprod := huMem.of_le_mul hprodMeas hprodBound
  simpa [W] using hprod

end PDE.Parabolic.Cauchy.Weights
