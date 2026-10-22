module

public import PDEFoundation.Analysis.Newtonian.WeakType.HormanderKernel
public import PDEFoundation.Analysis.Newtonian.WeakType.HormanderRadial

/-! # The Hörmander integral outside the dilated cube

For an abstract kernel `K : Vec d → Mat d` with the Hölder property (`KernelHolder`), a vector
field `b` supported in the closed Euclidean ball `|y - c| ≤ r`, and `x` outside the open ball
`B(c, 2 r)`:

* `norm_integral_kernel_sub_le`: pointwise bound `A r |x - c|^{-(d+1)} ‖b‖₁`;
* `lintegral_exterior_hormander_le`: the exterior integral over `B(c, 2r)ᶜ` is at most
  `(d |B₁| / 2) A ‖b‖₁`.

The mean-zero property of `b` is used only in the identification of this integral with
`∫ K (x - y) b y dy`; see `integral_kernel_eq_of_integral_eq_zero`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.NewtonWeakType

noncomputable section

variable {d : ℕ}

/-- Pointwise Hörmander bound: for `|x - c| ≥ 2 r` and `b` supported in `|y - c| ≤ r`. -/
theorem norm_integral_kernel_sub_le [NeZero d] {K : Vec d → Mat d} {A : ℝ} (hA : 0 ≤ A)
    (hK : KernelHolder d K A) {c : Vec d} {r : ℝ} (hr : 0 < r) {b : Vec d → Vec d}
    (hb : ∀ i, Integrable (fun y => b y i))
    (hsupp : ∀ y, r < vecEuclideanNorm (y - c) → b y = 0) {x : Vec d}
    (hx : 2 * r ≤ vecEuclideanNorm (x - c)) :
    vecEuclideanNorm
        (fun i => ∫ y, matVecMul (K (x - y) - K (x - c)) (b y) i) ≤
      A * r / vecEuclideanNorm (x - c) ^ (d + 1) * ∫ y, vecEuclideanNorm (b y) := by
  set z := x - c with hz
  have hzpos : 0 < vecEuclideanNorm z := by linarith
  have hz0 : z ≠ 0 := fun h => by simp [h, vecEuclideanNorm_eq_zero_iff.mpr rfl] at hzpos
  have hpow : 0 < vecEuclideanNorm z ^ (d + 1) := pow_pos hzpos _
  have hbn : Integrable (fun y => vecEuclideanNorm (b y)) :=
    integrable_vecEuclideanNorm_of_coord b hb
  let f : Vec d → Vec d := fun y => matVecMul (K (x - y) - K (x - c)) (b y)
  let G : Vec d → ℝ := fun y => A * (r / vecEuclideanNorm z ^ (d + 1)) * vecEuclideanNorm (b y)
  have hG : Integrable G := hbn.const_mul _
  have hfG : ∀ y, vecEuclideanNorm (f y) ≤ G y := by
    intro y
    by_cases hy : vecEuclideanNorm (y - c) ≤ r
    · have hsub : z - (x - y) = y - c := by simp [hz]
      have hhalf : vecEuclideanNorm (z - (x - y)) ≤ vecEuclideanNorm z / 2 := by
        rw [hsub]; linarith
      have h1 := hK z (x - y) hz0 hhalf (b y)
      have h2 : f y = -matVecMul (K z - K (x - y)) (b y) := by
        rw [← matVecMul_neg', neg_sub]
      rw [h2, vecEuclideanNorm_neg]
      refine h1.trans ?_
      rw [hsub]
      have : vecEuclideanNorm (y - c) / vecEuclideanNorm z ^ (d + 1) ≤
          r / vecEuclideanNorm z ^ (d + 1) := div_le_div_of_nonneg_right hy hpow.le
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hA)
        (vecEuclideanNorm_nonneg _)
    · have h0 : b y = 0 := hsupp y (not_le.mp hy)
      have : f y = 0 := by simp only [f, h0, matVecMul_zero_right]
      rw [this, vecEuclideanNorm_eq_zero_iff.mpr rfl]
      exact mul_nonneg (mul_nonneg hA (div_nonneg hr.le hpow.le)) (vecEuclideanNorm_nonneg _)
  have hcoord : ∀ i, Integrable (fun y => f y i) := by
    intro i
    have hmeas : AEStronglyMeasurable (fun y => f y i) volume := by
      have e : (fun y => f y i) = fun y => ∑ j, (K (x - y) i j - K (x - c) i j) * b y j := by
        funext y
        simp [f, Matrix.sub_apply]
      rw [e]
      refine Finset.aestronglyMeasurable_fun_sum _ (fun j _ => ?_)
      exact ((hK.aestronglyMeasurable_entry x i j).sub aestronglyMeasurable_const).mul
        (hb j).aestronglyMeasurable
    refine hG.mono' hmeas (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_apply_le_vecEuclideanNorm (f y) i).trans (hfG y)
  have hfn : Integrable (fun y => vecEuclideanNorm (f y)) :=
    integrable_vecEuclideanNorm_of_coord f hcoord
  calc
    vecEuclideanNorm (fun i => ∫ y, f y i) ≤ ∫ y, vecEuclideanNorm (f y) :=
      vecEuclideanNorm_integral_le_integral_vecEuclideanNorm f hcoord
    _ ≤ ∫ y, G y := integral_mono hfn hG hfG
    _ = A * r / vecEuclideanNorm z ^ (d + 1) * ∫ y, vecEuclideanNorm (b y) := by
      simp only [G]
      rw [integral_const_mul]
      ring

/-- Translation of the exterior radial integral. -/
theorem lintegral_compl_euclideanBall_comp_sub (c : Vec d) (R : ℝ) (φ : ℝ → ℝ≥0∞) :
    ∫⁻ x in (euclideanBall c R)ᶜ, φ (vecEuclideanNorm (x - c)) =
      ∫⁻ z in (euclideanBall (0 : Vec d) R)ᶜ, φ (vecEuclideanNorm z) := by
  have h1 := (measurePreserving_sub_right (volume : Measure (Vec d)) c).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.subRight c).measurableEmbedding (fun z => φ (vecEuclideanNorm z))
    (euclideanBall (0 : Vec d) R)ᶜ
  have hpre : (fun x : Vec d => x - c) ⁻¹' (euclideanBall (0 : Vec d) R)ᶜ =
      (euclideanBall c R)ᶜ := by
    ext x
    simp [euclideanBall, euclideanSqDist]
  rw [← hpre]
  exact h1

/-- The constant of the exterior Hörmander integral. -/
def hormanderConst (d : ℕ) : ℝ :=
  (d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal / 2

theorem hormanderConst_nonneg (d : ℕ) : 0 ≤ hormanderConst d := by
  unfold hormanderConst
  positivity

/-- **Hörmander integral.** For `b` supported in `|y - c| ≤ r`, the exterior integral over
`B(c, 2 r)ᶜ` of the Hörmander integrand is bounded by `C(d) A ‖b‖₁`. -/
theorem lintegral_exterior_hormander_le [NeZero d] {K : Vec d → Mat d} {A : ℝ} (hA : 0 ≤ A)
    (hK : KernelHolder d K A) {c : Vec d} {r : ℝ} (hr : 0 < r) {b : Vec d → Vec d}
    (hb : ∀ i, Integrable (fun y => b y i))
    (hsupp : ∀ y, r < vecEuclideanNorm (y - c) → b y = 0) :
    ∫⁻ x in (euclideanBall c (2 * r))ᶜ,
        ENNReal.ofReal (vecEuclideanNorm
          (fun i => ∫ y, matVecMul (K (x - y) - K (x - c)) (b y) i)) ≤
      ENNReal.ofReal (hormanderConst d * A * ∫ y, vecEuclideanNorm (b y)) := by
  set B : ℝ := ∫ y, vecEuclideanNorm (b y) with hB
  have hB0 : 0 ≤ B := integral_nonneg fun y => vecEuclideanNorm_nonneg _
  have hr2 : 0 < 2 * r := by linarith
  have hpt : ∀ x ∈ (euclideanBall c (2 * r))ᶜ,
      ENNReal.ofReal (vecEuclideanNorm
          (fun i => ∫ y, matVecMul (K (x - y) - K (x - c)) (b y) i)) ≤
        ENNReal.ofReal (A * r * B) *
          ENNReal.ofReal (vecEuclideanNorm (x - c) ^ (-((d : ℝ) + 1))) := by
    intro x hx
    have hx' : 2 * r ≤ vecEuclideanNorm (x - c) := by
      have : ¬ vecEuclideanNorm (x - c) < 2 * r := fun h =>
        hx ((mem_euclideanBall_iff_vecEuclideanNorm_lt hr2).mpr h)
      exact not_lt.mp this
    have hbd := norm_integral_kernel_sub_le hA hK hr hb hsupp hx'
    have hzpos : 0 < vecEuclideanNorm (x - c) := by linarith
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    refine hbd.trans (le_of_eq ?_)
    rw [Real.rpow_neg hzpos.le, ← Real.rpow_natCast, Nat.cast_add, Nat.cast_one]
    field_simp
    rw [hB]
  calc
    _ ≤ ∫⁻ x in (euclideanBall c (2 * r))ᶜ, ENNReal.ofReal (A * r * B) *
          ENNReal.ofReal (vecEuclideanNorm (x - c) ^ (-((d : ℝ) + 1))) :=
      setLIntegral_mono' (measurableSet_euclideanBall c _).compl hpt
    _ = ENNReal.ofReal (A * r * B) * ∫⁻ x in (euclideanBall c (2 * r))ᶜ,
          ENNReal.ofReal (vecEuclideanNorm (x - c) ^ (-((d : ℝ) + 1))) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (A * r * B) * ENNReal.ofReal
          ((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal * (2 * r)⁻¹) := by
      rw [lintegral_compl_euclideanBall_comp_sub c (2 * r)
        (fun t => ENNReal.ofReal (t ^ (-((d : ℝ) + 1)))),
        lintegral_compl_euclideanBall_tail hr2]
    _ = ENNReal.ofReal (hormanderConst d * A * B) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      unfold hormanderConst
      field_simp

/-- For mean-zero `b`, the kernel integral equals the Hörmander integral. -/
theorem integral_kernel_sub_eq_of_integral_eq_zero {K : Vec d → Mat d} {c x : Vec d}
    {b : Vec d → Vec d} (hb : ∀ i, Integrable (fun y => b y i))
    (hmean : ∀ i, ∫ y, b y i = 0)
    (hint : ∀ i, Integrable (fun y => matVecMul (K (x - y)) (b y) i)) (i : Fin d) :
    ∫ y, matVecMul (K (x - y) - K (x - c)) (b y) i =
      ∫ y, matVecMul (K (x - y)) (b y) i := by
  have hsplit : ∀ y, matVecMul (K (x - y) - K (x - c)) (b y) i =
      matVecMul (K (x - y)) (b y) i - ∑ j, K (x - c) i j * b y j := by
    intro y
    simp [matVecMul, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have hsum : Integrable (fun y => ∑ j, K (x - c) i j * b y j) :=
    integrable_finsetSum _ fun j _ => (hb j).const_mul _
  simp_rw [hsplit]
  rw [integral_sub (hint i) hsum, integral_finsetSum _ fun j _ => (hb j).const_mul _]
  simp [integral_const_mul, hmean]

end

end PDE.NewtonWeakType
