module

public import PDEFoundation.Analysis.FiniteWeightedOperatorInterpolation
public import PDEFoundation.Measure.FiniteAtomCompressedLpBound

@[expose] public section

namespace PDE

open MeasureTheory Set Function
open scoped ENNReal BigOperators

noncomputable section

variable {α β ι κ : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Fintype ι] [Fintype κ]

private def finiteAtomMatrixLinearMap
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ]
    (E : ι → Set α) (hE : ∀ i, MeasurableSet (E i))
    (H : κ → Set β) (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν) :
    (ι → ℝ) →ₗ[ℝ] (κ → ℝ) where
  toFun v j := ∑ i, finiteAtomOperatorMatrix μ ν E hE H T j i * v i
  map_add' v w := by
    ext j
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    ext j
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

private theorem abs_rpow_four (x : ℝ) : |x| ^ (4 : ℝ) = x ^ 4 := by
  calc
    |x| ^ (4 : ℝ) = |x| ^ (4 : ℕ) := Real.rpow_natCast _ _
    _ = (|x| ^ 2) ^ 2 := by ring
    _ = (x ^ 2) ^ 2 := by rw [sq_abs]
    _ = x ^ 4 := by ring

private theorem rpow_eq_root_of_rpow_eq
    {x A p : ℝ} (hx : 0 ≤ x) (hp : 0 < p) (h : x ^ p = A) :
    x = A ^ (1 / p) := by
  rw [← h, ← Real.rpow_mul hx]
  rw [show p * (1 / p) = 1 by field_simp [hp.ne'], Real.rpow_one]

/-- The finite atom compression of an operator satisfying genuine `L²` and
`L⁴` bounds satisfies every interpolated atom `Lᵖ` bound for `2 ≤ p ≤ 4`. -/
theorem eLpNorm_finiteAtomAveraging_operator_le_of_two_four
    (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : ι → Set α) (hE : ∀ i, MeasurableSet (E i))
    (hEdisj : Pairwise (Disjoint on E))
    (H : κ → Set β) (hH : ∀ j, MeasurableSet (H j))
    (hHdisj : Pairwise (Disjoint on H))
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν)
    {p M : ℝ} (hp : 2 ≤ p) (hpFour : p ≤ 4) (hM : 1 ≤ M)
    (hTwo : ∀ f : Lp ℝ 2 μ, MemLp f 2 μ →
      eLpNorm (T f) 2 ν ≤ ENNReal.ofReal M * eLpNorm f 2 μ)
    (hFour : ∀ f : Lp ℝ 2 μ, MemLp f 4 μ →
      eLpNorm (T f) 4 ν ≤ ENNReal.ofReal M * eLpNorm f 4 μ)
    (v : ι → ℝ) :
    eLpNorm
        (finiteAtomAveraging ν H
          (T (finiteAtomInputLinearMap μ E hE v)))
        (ENNReal.ofReal p) ν ≤
      ENNReal.ofReal M *
        eLpNorm (finiteDisjointAtomSum E v) (ENNReal.ofReal p) μ := by
  let S := finiteAtomMatrixLinearMap μ ν E hE H T
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hTwo' (x : ι → ℝ) :
      ∑ j, (ν (H j)).toReal * (S x j) ^ 2 ≤
        M ^ 2 * ∑ i, (μ (E i)).toReal * (x i) ^ 2 := by
    have h := finiteAtomOperatorMatrix_weighted_rpow_le
      μ ν E hE hEdisj H hH hHdisj T (q := (2 : ℝ))
      (by norm_num) hM0 (by
        intro f hf
        simpa only [ENNReal.ofReal_ofNat] using hTwo f (by
          simpa only [ENNReal.ofReal_ofNat] using hf)) x
    simpa only [S, finiteAtomMatrixLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
      Real.rpow_two, sq_abs] using h
  have hFour' (x : ι → ℝ) :
      ∑ j, (ν (H j)).toReal * (S x j) ^ 4 ≤
        M ^ 4 * ∑ i, (μ (E i)).toReal * (x i) ^ 4 := by
    have h := finiteAtomOperatorMatrix_weighted_rpow_le
      μ ν E hE hEdisj H hH hHdisj T (q := (4 : ℝ))
      (by norm_num) hM0 (by
        intro f hf
        simpa only [ENNReal.ofReal_ofNat] using hFour f (by
          simpa only [ENNReal.ofReal_ofNat] using hf)) x
    simp_rw [abs_rpow_four] at h
    have hMr : M ^ (4 : ℝ) = M ^ (4 : ℕ) := Real.rpow_natCast M 4
    rw [hMr] at h
    change
      ∑ j, (ν (H j)).toReal *
          (∑ i, finiteAtomOperatorMatrix μ ν E hE H T j i * x i) ^ 4 ≤
        M ^ 4 * ∑ i, (μ (E i)).toReal * (x i) ^ 4
    exact h
  have hinterp := weighted_lp_operator_le_of_two_four S
    (fun i => (μ (E i)).toReal) (fun j => (ν (H j)).toReal)
    (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg)
    p M hp hpFour hM hTwo' hFour' v
  let fout : β → ℝ := finiteAtomAveraging ν H
    (T (finiteAtomInputLinearMap μ E hE v))
  let fin : α → ℝ := finiteDisjointAtomSum E v
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hfout : MemLp fout (ENNReal.ofReal p) ν :=
    memLp_finiteAtomAveraging ν H hH _ _
  have hfin : MemLp fin (ENNReal.ofReal p) μ :=
    memLp_finiteDisjointAtomSum μ E hE v _
  have houtPow :
      (eLpNorm fout (ENNReal.ofReal p) ν).toReal ^ p =
        ∑ j, (ν (H j)).toReal * |S v j| ^ p := by
    unfold fout finiteAtomAveraging
    rw [eLpNorm_finiteDisjointAtomSum_toReal_rpow
      ν H hH hHdisj
      (fun j => finiteAtomAverage ν (H j)
        (T (finiteAtomInputLinearMap μ E hE v))) hp0]
    apply Finset.sum_congr rfl
    intro j _
    rw [finiteAtomAverage_operator_input_eq_matrix_mul
      μ ν E hE H T v j]
    rfl
  have hinPow :
      (eLpNorm fin (ENNReal.ofReal p) μ).toReal ^ p =
        ∑ i, (μ (E i)).toReal * |v i| ^ p := by
    exact eLpNorm_finiteDisjointAtomSum_toReal_rpow
      μ E hE hEdisj v hp0
  have houtRoot :
      (eLpNorm fout (ENNReal.ofReal p) ν).toReal =
        (∑ j, (ν (H j)).toReal * |S v j| ^ p) ^ (1 / p) :=
    rpow_eq_root_of_rpow_eq ENNReal.toReal_nonneg hp0 houtPow
  have hinRoot :
      (eLpNorm fin (ENNReal.ofReal p) μ).toReal =
        (∑ i, (μ (E i)).toReal * |v i| ^ p) ^ (1 / p) :=
    rpow_eq_root_of_rpow_eq ENNReal.toReal_nonneg hp0 hinPow
  have hreal :
      (eLpNorm fout (ENNReal.ofReal p) ν).toReal ≤
        M * (eLpNorm fin (ENNReal.ofReal p) μ).toReal := by
    rw [houtRoot, hinRoot]
    exact hinterp
  apply (ENNReal.toReal_le_toReal hfout.eLpNorm_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.eLpNorm_ne_top)).mp
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM0] using hreal

end

end PDE
