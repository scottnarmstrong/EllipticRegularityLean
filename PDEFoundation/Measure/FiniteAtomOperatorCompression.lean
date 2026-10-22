module

public import PDEFoundation.Measure.FiniteAtomAverageLp
public import PDEFoundation.Measure.FiniteDisjointAtomLp
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

@[expose] public section

namespace PDE

open MeasureTheory Set Function
open scoped ENNReal BigOperators

noncomputable section

variable {α β ι κ : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Fintype ι]

private theorem coeFn_finset_sum_ae
    {γ I : Type*} [MeasurableSpace γ] {ρ : Measure γ}
    (s : Finset I) (F : I → Lp ℝ 2 ρ) :
    (⇑(∑ i ∈ s, F i) : γ → ℝ) =ᵐ[ρ] fun x => ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using! Lp.coeFn_zero ℝ 2 ρ
  | @insert i s hi ih =>
      filter_upwards [Lp.coeFn_add (F i) (∑ k ∈ s, F k), ih] with x hadd hsum
      rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd]
      simp only [Pi.add_apply, hsum]

/-- The raw indicator of a measurable finite-measure atom, as an `L²`
element. -/
def finiteAtomBasis (μ : Measure α) [IsFiniteMeasure μ]
    (E : ι → Set α) (hE : ∀ i, MeasurableSet (E i)) (i : ι) :
    Lp ℝ 2 μ :=
  (memLp_indicator_const 2 (hE i) (1 : ℝ)
    (Or.inr (measure_lt_top μ (E i)).ne)).toLp
      ((E i).indicator fun _ => (1 : ℝ))

/-- The literal linear combination of raw atom indicators in `L²`. -/
def finiteAtomInputLinearMap (μ : Measure α) [IsFiniteMeasure μ]
    (E : ι → Set α) (hE : ∀ i, MeasurableSet (E i)) :
    (ι → ℝ) →ₗ[ℝ] Lp ℝ 2 μ where
  toFun v := ∑ i, v i • finiteAtomBasis μ E hE i
  map_add' v w := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_smul,
      Finset.smul_sum]

/-- The `L²` atom input map has the expected literal finite-indicator
representative. -/
theorem finiteAtomInputLinearMap_ae_eq_finiteDisjointAtomSum
    (μ : Measure α) [IsFiniteMeasure μ]
    (E : ι → Set α) (hE : ∀ i, MeasurableSet (E i)) (v : ι → ℝ) :
    finiteAtomInputLinearMap μ E hE v =ᵐ[μ]
      finiteDisjointAtomSum E v := by
  classical
  have hb (i : ι) :
      finiteAtomBasis μ E hE i =ᵐ[μ]
        (E i).indicator (fun _ => (1 : ℝ)) :=
    MemLp.coeFn_toLp _
  have hcoe := coeFn_finset_sum_ae (ρ := μ) Finset.univ
    (fun i => v i • finiteAtomBasis μ E hE i)
  filter_upwards [ae_all_iff.2 hb, hcoe,
    ae_all_iff.2 fun i => Lp.coeFn_smul (v i) (finiteAtomBasis μ E hE i)]
      with x hx hsum hsmul
  rw [show finiteAtomInputLinearMap μ E hE v =
      ∑ i, v i • finiteAtomBasis μ E hE i by rfl]
  rw [hsum]
  simp only [finiteDisjointAtomSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hsmul i]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hx i]
  by_cases hxi : x ∈ E i <;> simp [hxi]

/-- The matrix obtained by applying an `L²` operator to raw input atoms and
averaging its output over raw output atoms. -/
def finiteAtomOperatorMatrix
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ]
    (E : ι → Set α) (hE : ∀ i, MeasurableSet (E i))
    (H : κ → Set β) (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν)
    (j : κ) (i : ι) : ℝ :=
  finiteAtomAverage ν (H j) (T (finiteAtomBasis μ E hE i))

/-- Output atom averaging of the operator applied to an atom input is exactly
multiplication by its finite compression matrix. -/
theorem finiteAtomAverage_operator_input_eq_matrix_mul
    (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : ι → Set α) (hE : ∀ i, MeasurableSet (E i))
    (H : κ → Set β) (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν)
    (v : ι → ℝ) (j : κ) :
    finiteAtomAverage ν (H j) (T (finiteAtomInputLinearMap μ E hE v)) =
      ∑ i, finiteAtomOperatorMatrix μ ν E hE H T j i * v i := by
  classical
  have hint (i : ι) : Integrable (T (finiteAtomBasis μ E hE i)) ν :=
    (Lp.memLp (T (finiteAtomBasis μ E hE i))).integrable (by norm_num)
  have hterm (i : ι) :
      ∫ x in H j, (v i • T (finiteAtomBasis μ E hE i)) x ∂ν =
        v i * ∫ x in H j, T (finiteAtomBasis μ E hE i) x ∂ν := by
    rw [integral_congr_ae (ae_restrict_of_ae
      (Lp.coeFn_smul (v i) (T (finiteAtomBasis μ E hE i))))]
    exact integral_const_mul _ _
  unfold finiteAtomAverage finiteAtomOperatorMatrix
  rw [show T (finiteAtomInputLinearMap μ E hE v) =
      ∑ i, v i • T (finiteAtomBasis μ E hE i) by
        simp [finiteAtomInputLinearMap]]
  rw [integral_congr_ae (ae_restrict_of_ae
    (coeFn_finset_sum_ae (ρ := ν) Finset.univ
      (fun i => v i • T (finiteAtomBasis μ E hE i))))]
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hterm i]
    unfold finiteAtomAverage
    ring
  · intro i _
    exact (Lp.memLp (v i • T (finiteAtomBasis μ E hE i))).integrable
      (by norm_num) |>.integrableOn

end

end PDE
