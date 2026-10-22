module

public import PDEFoundation.Sobolev.H1.VectorMeanOscillation

/-!
# Coordinatewise means for finite-dimensional vector fields

This file extends the coordinatewise integral average to fields whose source
and target dimensions may differ.  Quadratic quantities are expressed through
`vecNormSq`.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d m : ℕ}

/-- The coordinatewise integral average of a vector field, with independent
source and target dimensions. -/
def coordinateVectorAverage (U : Set (Vec d)) (g : Vec d → Vec m) : Vec m :=
  fun i => integralAverage U (fun x => g x i)

@[simp]
theorem coordinateVectorAverage_apply (U : Set (Vec d)) (g : Vec d → Vec m)
    (i : Fin m) :
    coordinateVectorAverage U g i = integralAverage U (fun x => g x i) :=
  rfl

/-- In equal dimensions, the generalized average is the existing vector
integral average. -/
theorem coordinateVectorAverage_eq_vectorIntegralAverage
    (U : Set (Vec d)) (g : Vec d → Vec d) :
    coordinateVectorAverage U g = vectorIntegralAverage U g :=
  rfl

private theorem integrableOn_sq_sub_const_of_memL2On'
    {U : Set (Vec d)} {f : Vec d → ℝ} (hf : MemLp f 2 (volumeOn U))
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

/-- Coordinatewise `L²` membership makes squared Euclidean deviation from
every constant vector integrable. -/
theorem integrableOn_vecNormSq_sub_const_of_coordinate_memLp
    {U : Set (Vec d)} {g : Vec d → Vec m}
    (hg : ∀ i : Fin m, MemLp (fun x => g x i) 2 (volumeOn U))
    (hUtop : volume U < ∞) (c : Vec m) :
    IntegrableOn (fun x => vecNormSq (g x - c)) U volume := by
  simp only [vecNormSq_eq_sum_sq, Pi.sub_apply]
  exact integrable_finsetSum Finset.univ fun i _ =>
    integrableOn_sq_sub_const_of_memL2On' (hg i) hUtop (c i)

/-- Every coordinate centered at the coordinatewise average has zero
integral. -/
theorem meanZeroOn_apply_sub_coordinateVectorAverage
    {U : Set (Vec d)} {g : Vec d → Vec m}
    (hg : ∀ i : Fin m, MemLp (fun x => g x i) 2 (volumeOn U))
    (hUpos : 0 < volume U) (hUtop : volume U < ∞) (i : Fin m) :
    MeanZeroOn U (fun x => (g x - coordinateVectorAverage U g) i) := by
  let : IsFiniteMeasure (volumeOn U) :=
    isFiniteMeasure_restrict.mpr hUtop.ne
  simpa only [Pi.sub_apply, coordinateVectorAverage_apply] using
    meanZeroOn_sub_integralAverage
      ((hg i).integrable (by norm_num)) hUpos hUtop

/-- Exact variance decomposition for a finite-dimensional vector field. -/
theorem setIntegral_vecNormSq_sub_eq_coordinateVectorAverage_add
    {U : Set (Vec d)} {g : Vec d → Vec m}
    (hg : ∀ i : Fin m, MemLp (fun x => g x i) 2 (volumeOn U))
    (hUpos : 0 < volume U) (hUtop : volume U < ∞) (c : Vec m) :
    (∫ x in U, vecNormSq (g x - c) ∂volume) =
      (∫ x in U, vecNormSq (g x - coordinateVectorAverage U g) ∂volume) +
        (volume U).toReal * vecNormSq (coordinateVectorAverage U g - c) := by
  have hleft : ∀ i : Fin m, IntegrableOn (fun x => (g x i - c i) ^ 2) U volume :=
    fun i => integrableOn_sq_sub_const_of_memL2On' (hg i) hUtop (c i)
  have hcentered : ∀ i : Fin m,
      IntegrableOn (fun x => (g x i - coordinateVectorAverage U g i) ^ 2) U volume :=
    fun i => integrableOn_sq_sub_const_of_memL2On' (hg i) hUtop
      (coordinateVectorAverage U g i)
  simp only [vecNormSq_eq_sum_sq, Pi.sub_apply]
  rw [integral_finsetSum Finset.univ (fun i _ => hleft i),
    integral_finsetSum Finset.univ (fun i _ => hcentered i)]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  let a := coordinateVectorAverage U g i
  have hfint : IntegrableOn (fun x => g x i) U volume := by
    let : IsFiniteMeasure (volumeOn U) :=
      isFiniteMeasure_restrict.mpr hUtop.ne
    exact (hg i).integrable (by norm_num)
  have hcenter := meanZeroOn_apply_sub_coordinateVectorAverage hg hUpos hUtop i
  have hcenterInt : IntegrableOn (fun x => (g x i - a) ^ 2) U volume :=
    integrableOn_sq_sub_const_of_memL2On' (hg i) hUtop a
  have hcrossInt : IntegrableOn (fun x => 2 * (g x i - a) * (a - c i)) U volume := by
    have haint : IntegrableOn (fun _x : Vec d => a) U volume := integrableOn_const hUtop.ne
    simpa only [Pi.sub_apply, mul_assoc, mul_comm, mul_left_comm] using!
      (hfint.sub haint).mul_const (2 * (a - c i))
  have hconstInt : IntegrableOn (fun _x : Vec d => (a - c i) ^ 2) U volume :=
    integrableOn_const hUtop.ne
  have hexpand : (fun x => (g x i - c i) ^ 2) = fun x =>
      (g x i - a) ^ 2 + 2 * (g x i - a) * (a - c i) + (a - c i) ^ 2 := by
    funext x
    ring
  change (∫ x in U, (g x i - c i) ^ 2 ∂volume) =
    (∫ x in U, (g x i - a) ^ 2 ∂volume) + (volume U).toReal * (a - c i) ^ 2
  rw [hexpand]
  have hsplitOuter :
      (∫ x in U, ((g x i - a) ^ 2 + 2 * (g x i - a) * (a - c i)) +
          (a - c i) ^ 2 ∂volume) =
        (∫ x in U, (g x i - a) ^ 2 + 2 * (g x i - a) * (a - c i) ∂volume) +
          ∫ _x in U, (a - c i) ^ 2 ∂volume := by
    simpa only [Pi.add_apply] using integral_add (hcenterInt.add hcrossInt) hconstInt
  have hsplitInner :
      (∫ x in U, (g x i - a) ^ 2 + 2 * (g x i - a) * (a - c i) ∂volume) =
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

/-- The coordinatewise average minimizes squared Euclidean deviation among
constant target vectors. -/
theorem setIntegral_vecNormSq_sub_coordinateVectorAverage_le
    {U : Set (Vec d)} {g : Vec d → Vec m}
    (hg : ∀ i : Fin m, MemLp (fun x => g x i) 2 (volumeOn U))
    (hUpos : 0 < volume U) (hUtop : volume U < ∞) (c : Vec m) :
    (∫ x in U, vecNormSq (g x - coordinateVectorAverage U g) ∂volume) ≤
      ∫ x in U, vecNormSq (g x - c) ∂volume := by
  rw [setIntegral_vecNormSq_sub_eq_coordinateVectorAverage_add hg hUpos hUtop c]
  exact le_add_of_nonneg_right
    (mul_nonneg ENNReal.toReal_nonneg (vecNormSq_nonneg _))

end

end PDE
