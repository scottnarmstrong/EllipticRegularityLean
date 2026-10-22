module

public import PDEFoundation.Sobolev.H1.MeanEnergy
public import PDEFoundation.Sobolev.H1.VectorL2Bounds

/-!
# Vector mean oscillation

This file develops the elementary Hilbert-space algebra of the coordinatewise
integral mean of a native vector field.  All quadratic quantities use
`vecNormSq`, so the inherited supremum norm on `Vec d` never enters the API.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The coordinatewise integral average of a native vector field. -/
def vectorIntegralAverage (U : Set (Vec d)) (g : Vec d → Vec d) : Vec d :=
  fun i => integralAverage U (fun x => g x i)

@[simp]
theorem vectorIntegralAverage_apply (U : Set (Vec d)) (g : Vec d → Vec d)
    (i : Fin d) :
    vectorIntegralAverage U g i = integralAverage U (fun x => g x i) :=
  rfl

/-- Coordinatewise `L²` membership on a finite-volume domain implies
Bochner integrability of the native vector field. -/
theorem integrableOn_of_memVectorL2On_of_volume_lt_top
    {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : MemVectorL2On U g) (hUtop : volume U < ∞) :
    IntegrableOn g U volume := by
  let : IsFiniteMeasure (volumeOn U) :=
    isFiniteMeasure_restrict.mpr hUtop.ne
  exact Integrable.of_eval fun i => (hg i).integrable (by norm_num)

/-- The vector integral average is the normalized Bochner integral. -/
theorem vectorIntegralAverage_eq_smul_setIntegral
    {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : IntegrableOn g U volume) :
    vectorIntegralAverage U g =
      (volume U).toReal⁻¹ • ∫ x in U, g x ∂volume := by
  funext i
  rw [vectorIntegralAverage_apply, integralAverage, Pi.smul_apply,
    smul_eq_mul, MeasureTheory.eval_integral]
  exact fun j => hg.eval j

/-- The vector integral average is additive for integrable fields. -/
theorem vectorIntegralAverage_add
    {U : Set (Vec d)} {f g : Vec d → Vec d}
    (hf : IntegrableOn f U volume) (hg : IntegrableOn g U volume) :
    vectorIntegralAverage U (fun x => f x + g x) =
      vectorIntegralAverage U f + vectorIntegralAverage U g := by
  funext i
  simp only [vectorIntegralAverage_apply, Pi.add_apply, integralAverage]
  rw [integral_add (hf.eval i) (hg.eval i)]
  ring

/-- Every coordinate of the field centered at its vector mean has zero
integral. -/
theorem meanZeroOn_apply_sub_vectorIntegralAverage
    {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : MemVectorL2On U g) (hUpos : 0 < volume U) (hUtop : volume U < ∞)
    (i : Fin d) :
    MeanZeroOn U (fun x => (g x - vectorIntegralAverage U g) i) := by
  let : IsFiniteMeasure (volumeOn U) :=
    isFiniteMeasure_restrict.mpr hUtop.ne
  simpa only [Pi.sub_apply, vectorIntegralAverage_apply] using
    meanZeroOn_sub_integralAverage
      ((hg i).integrable (by norm_num)) hUpos hUtop

private theorem integrableOn_sq_sub_const_of_memL2On
    {U : Set (Vec d)} {f : Vec d → ℝ} (hf : MemL2On U f)
    (hUtop : volume U < ∞) (c : ℝ) :
    IntegrableOn (fun x => (f x - c) ^ 2) U volume := by
  have hsq : IntegrableOn (fun x => f x ^ 2) U volume := by
    simpa only [pow_two] using! hf.integrable_mul hf
  let : IsFiniteMeasure (volumeOn U) :=
    isFiniteMeasure_restrict.mpr hUtop.ne
  have hfint : IntegrableOn f U volume := hf.integrable (by norm_num)
  have hexpand : (fun x => (f x - c) ^ 2) =
      fun x => f x ^ 2 + (-2 * c) * f x + c ^ 2 := by
    funext x
    ring
  rw [hexpand]
  exact (hsq.add (hfint.const_mul (-2 * c))).add (integrableOn_const hUtop.ne)

/-- Subtracting a constant preserves native vector `L²` membership on a
finite-volume domain. -/
theorem memVectorL2On_sub_const
    {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : MemVectorL2On U g) (hUtop : volume U < ∞) (c : Vec d) :
    MemVectorL2On U (fun x => g x - c) := by
  intro i
  let : IsFiniteMeasure (volumeOn U) :=
    isFiniteMeasure_restrict.mpr hUtop.ne
  simpa only [Pi.sub_apply] using!
    (hg i).sub (memLp_const (μ := volumeOn U) (p := 2) (c i))

/-- Exact Pythagorean identity for squared Euclidean deviation from the vector
mean. -/
theorem setIntegral_vecNormSq_sub_eq_centered_add
    {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : MemVectorL2On U g) (hUpos : 0 < volume U) (hUtop : volume U < ∞)
    (c : Vec d) :
    (∫ x in U, vecNormSq (g x - c) ∂volume) =
      (∫ x in U, vecNormSq (g x - vectorIntegralAverage U g) ∂volume) +
        (volume U).toReal * vecNormSq (vectorIntegralAverage U g - c) := by
  have hleft : ∀ i : Fin d, IntegrableOn (fun x => (g x i - c i) ^ 2) U volume :=
    fun i => integrableOn_sq_sub_const_of_memL2On (hg i) hUtop (c i)
  have hcentered : ∀ i : Fin d,
      IntegrableOn (fun x => (g x i - vectorIntegralAverage U g i) ^ 2) U volume :=
    fun i => integrableOn_sq_sub_const_of_memL2On (hg i) hUtop
      (vectorIntegralAverage U g i)
  simp only [vecNormSq_eq_sum_sq]
  simp only [Pi.sub_apply]
  rw [integral_finsetSum Finset.univ (fun i _ => hleft i),
    integral_finsetSum Finset.univ (fun i _ => hcentered i)]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  let a := vectorIntegralAverage U g i
  have hfint : IntegrableOn (fun x => g x i) U volume := by
    let : IsFiniteMeasure (volumeOn U) :=
      isFiniteMeasure_restrict.mpr hUtop.ne
    exact (hg i).integrable (by norm_num)
  have hcenter := meanZeroOn_apply_sub_vectorIntegralAverage hg hUpos hUtop i
  have hcenterInt : IntegrableOn (fun x => (g x i - a) ^ 2) U volume :=
    integrableOn_sq_sub_const_of_memL2On (hg i) hUtop a
  have hcrossInt : IntegrableOn (fun x => 2 * (g x i - a) * (a - c i)) U volume :=
    by
      have haint : IntegrableOn (fun _x : Vec d => a) U volume :=
        integrableOn_const hUtop.ne
      simpa only [Pi.sub_apply, mul_assoc, mul_comm, mul_left_comm] using!
        (hfint.sub haint).mul_const (2 * (a - c i))
  have hconstInt : IntegrableOn (fun _x : Vec d => (a - c i) ^ 2) U volume :=
    integrableOn_const hUtop.ne
  have hexpand : (fun x => (g x i - c i) ^ 2) = fun x =>
      (g x i - a) ^ 2 + 2 * (g x i - a) * (a - c i) + (a - c i) ^ 2 := by
    funext x
    ring
  change (∫ x in U, (g x i - c i) ^ 2 ∂volume) =
    (∫ x in U, (g x i - a) ^ 2 ∂volume) +
      (volume U).toReal * (a - c i) ^ 2
  rw [hexpand]
  have hsplitOuter :
      (∫ x in U, ((g x i - a) ^ 2 +
          2 * (g x i - a) * (a - c i)) + (a - c i) ^ 2 ∂volume) =
        (∫ x in U, (g x i - a) ^ 2 +
          2 * (g x i - a) * (a - c i) ∂volume) +
        ∫ _x in U, (a - c i) ^ 2 ∂volume := by
    simpa only [Pi.add_apply] using
      integral_add (hcenterInt.add hcrossInt) hconstInt
  have hsplitInner :
      (∫ x in U, (g x i - a) ^ 2 +
          2 * (g x i - a) * (a - c i) ∂volume) =
        (∫ x in U, (g x i - a) ^ 2 ∂volume) +
        ∫ x in U, 2 * (g x i - a) * (a - c i) ∂volume := by
    simpa only [Pi.add_apply] using integral_add hcenterInt hcrossInt
  rw [hsplitOuter, hsplitInner, setIntegral_const]
  have hcross : (∫ x in U, 2 * (g x i - a) * (a - c i) ∂volume) = 0 := by
    calc
      (∫ x in U, 2 * (g x i - a) * (a - c i) ∂volume) =
          2 * (a - c i) * ∫ x in U, (g x i - a) ∂volume := by
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = 0 := by
        rw [show (∫ x in U, (g x i - a) ∂volume) = 0 by exact hcenter]
        ring
  rw [hcross]
  simp only [add_zero, smul_eq_mul]
  congr 1

/-- The vector integral mean minimizes raw squared Euclidean deviation among
constant vectors. -/
theorem setIntegral_vecNormSq_sub_vectorIntegralAverage_le
    {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : MemVectorL2On U g) (hUpos : 0 < volume U) (hUtop : volume U < ∞)
    (c : Vec d) :
    (∫ x in U, vecNormSq (g x - vectorIntegralAverage U g) ∂volume) ≤
      ∫ x in U, vecNormSq (g x - c) ∂volume := by
  rw [setIntegral_vecNormSq_sub_eq_centered_add hg hUpos hUtop c]
  exact le_add_of_nonneg_right
    (mul_nonneg ENNReal.toReal_nonneg (vecNormSq_nonneg _))

/-- The normalized centered Euclidean `L²` seminorm of a vector field. -/
def centeredVectorMeanL2 (U : Set (Vec d)) (g : Vec d → Vec d) : ℝ :=
  Real.sqrt (integralAverage U
    (fun x => vecNormSq (g x - vectorIntegralAverage U g)))

/-- Centered vector mean `L²` is subadditive. -/
theorem centeredVectorMeanL2_add_le
    {U : Set (Vec d)} {f g : Vec d → Vec d}
    (hf : MemVectorL2On U f) (hg : MemVectorL2On U g)
    (hUtop : volume U < ∞) :
    centeredVectorMeanL2 U (fun x => f x + g x) ≤
      centeredVectorMeanL2 U f + centeredVectorMeanL2 U g := by
  have hfint := integrableOn_of_memVectorL2On_of_volume_lt_top hf hUtop
  have hgint := integrableOn_of_memVectorL2On_of_volume_lt_top hg hUtop
  have havg := vectorIntegralAverage_add hfint hgint
  have hfcenter := memVectorL2On_sub_const hf hUtop (vectorIntegralAverage U f)
  have hgcenter := memVectorL2On_sub_const hg hUtop (vectorIntegralAverage U g)
  unfold centeredVectorMeanL2
  rw [havg]
  simp only
  have hpoint : (fun x => f x + g x -
      (vectorIntegralAverage U f + vectorIntegralAverage U g)) =
      fun x => (f x - vectorIntegralAverage U f) +
        (g x - vectorIntegralAverage U g) := by
    funext x
    ext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  simp_rw [congrFun hpoint]
  simp only [sqrt_integralAverage_vecNormSq_eq]
  exact (div_le_div_of_nonneg_right
    (sqrt_setIntegral_vecNormSq_add_le hfcenter hgcenter)
    (Real.sqrt_nonneg _)).trans_eq (add_div _ _ _)

/-- On nested positive finite-volume domains, the difference of vector means
is controlled by the outer centered mean `L²` with the exact square-root
volume ratio. -/
theorem vecEuclideanNorm_vectorIntegralAverage_sub_le
    {V U : Set (Vec d)} (hVU : V ⊆ U)
    {g : Vec d → Vec d} (hg : MemVectorL2On U g)
    (hVpos : 0 < volume V) (hVtop : volume V < ∞)
    (hUpos : 0 < volume U) (hUtop : volume U < ∞) :
    vecEuclideanNorm (vectorIntegralAverage V g - vectorIntegralAverage U g) ≤
      Real.sqrt ((volume U).toReal / (volume V).toReal) *
        centeredVectorMeanL2 U g := by
  have hgV : MemVectorL2On V g := fun i =>
    (hg i).mono_measure (Measure.restrict_mono hVU le_rfl)
  have hcenterU := memVectorL2On_sub_const hg hUtop (vectorIntegralAverage U g)
  have hidentity := setIntegral_vecNormSq_sub_eq_centered_add
    hgV hVpos hVtop (vectorIntegralAverage U g)
  have hcenteredVNonneg :
      0 ≤ ∫ x in V, vecNormSq (g x - vectorIntegralAverage V g) ∂volume :=
    integral_nonneg fun x => vecNormSq_nonneg _
  have hmeanTerm :
      (volume V).toReal *
          vecNormSq (vectorIntegralAverage V g - vectorIntegralAverage U g) ≤
        ∫ x in V, vecNormSq (g x - vectorIntegralAverage U g) ∂volume := by
    rw [hidentity]
    exact le_add_of_nonneg_left hcenteredVNonneg
  have hrestrict :
      (∫ x in V, vecNormSq (g x - vectorIntegralAverage U g) ∂volume) ≤
        ∫ x in U, vecNormSq (g x - vectorIntegralAverage U g) ∂volume :=
    setIntegral_vecNormSq_mono_set hVU hcenterU
  have hmul := hmeanTerm.trans hrestrict
  have hVreal : 0 < (volume V).toReal :=
    ENNReal.toReal_pos hVpos.ne' hVtop.ne
  have hUreal : 0 < (volume U).toReal :=
    ENNReal.toReal_pos hUpos.ne' hUtop.ne
  have hnormSq :
      vecNormSq (vectorIntegralAverage V g - vectorIntegralAverage U g) ≤
        (∫ x in U, vecNormSq (g x - vectorIntegralAverage U g) ∂volume) /
          (volume V).toReal := by
    apply (le_div_iff₀ hVreal).2
    simpa only [mul_comm] using hmul
  unfold vecEuclideanNorm centeredVectorMeanL2
  calc
    Real.sqrt (vecNormSq
        (vectorIntegralAverage V g - vectorIntegralAverage U g)) ≤
        Real.sqrt ((∫ x in U,
          vecNormSq (g x - vectorIntegralAverage U g) ∂volume) /
            (volume V).toReal) :=
      Real.sqrt_le_sqrt hnormSq
    _ = Real.sqrt ((volume U).toReal / (volume V).toReal) *
        Real.sqrt (integralAverage U
          (fun x => vecNormSq (g x - vectorIntegralAverage U g))) := by
      have hEnergy : 0 ≤ ∫ x in U,
          vecNormSq (g x - vectorIntegralAverage U g) ∂volume :=
        integral_nonneg fun x => vecNormSq_nonneg _
      rw [sqrt_integralAverage_vecNormSq_eq,
        Real.sqrt_div hEnergy,
        Real.sqrt_div ENNReal.toReal_nonneg]
      have hVsqrt : Real.sqrt (volume V).toReal ≠ 0 :=
        (Real.sqrt_pos.mpr hVreal).ne'
      have hUsqrt : Real.sqrt (volume U).toReal ≠ 0 :=
        (Real.sqrt_pos.mpr hUreal).ne'
      field_simp

end

end PDE
