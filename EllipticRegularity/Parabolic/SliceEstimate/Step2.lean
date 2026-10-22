module

public import EllipticRegularity.Parabolic.SliceEstimate.Step2Main

/-!
# Step 2: testing the equation of `u` with `φ² v`
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Slice

open MeasureTheory Set Filter Topology Metric PDE PDE.Parabolic PDE.Parabolic.Energy
  PDE.Parabolic.WeakSlice

variable {d : ℕ}

/-- **Step 2.**  `∫ φ² v² = - ∫ φ² a∇u·∇v - 2 ∫ φ v a∇u·∇φ` over `B × (-1,0]`. -/
theorem step2_identity {lam Lam : ℝ} {a₀ : Vec d → Mat d}
    (ha : IsParabolicCoeff lam Lam (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (u v : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hu : IsParabolicWeakSolution (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u)
    (hv : ∀ ψ : ParTestFunction (euclideanBall (0 : Vec d) 1) (interior (Ioc (-1 : ℝ) 0)),
      ∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, v.toFun z * ψ.toFun z =
        -∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
          u.toFun z * parTimeDeriv ψ.toFun z)
    (φ : ParCutoff (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)) :
    Integrable (fun z : Vec d × ℝ => φ.toFun z ^ 2 * v.toFun z ^ 2)
        (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) ∧
      Integrable (fun z : Vec d × ℝ => φ.toFun z ^ 2 *
          vecDot (matVecMul (a₀ z.1) (u.grad z)) (v.grad z))
        (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) ∧
      Integrable (fun z : Vec d × ℝ => 2 * φ.toFun z * v.toFun z *
          vecDot (matVecMul (a₀ z.1) (u.grad z)) (parSpaceGrad φ.toFun z))
        (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) ∧
      (∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, φ.toFun z ^ 2 * v.toFun z ^ 2) +
        (∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, φ.toFun z ^ 2 *
          vecDot (matVecMul (a₀ z.1) (u.grad z)) (v.grad z)) +
        (∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, 2 * φ.toFun z * v.toFun z *
          vecDot (matVecMul (a₀ z.1) (u.grad z)) (parSpaceGrad φ.toFun z)) = 0 := by
  have hU : IsOpen (euclideanBall (0 : Vec d) 1) := isOpen_euclideanBall _ _
  set ν : Measure (Vec d × ℝ) :=
    volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0) with hν
  have hmBJ : MeasurableSet (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0) :=
    hU.measurableSet.prod measurableSet_Ioc
  have hae : ∀ᵐ z ∂ν, z ∈ euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 :=
    ae_restrict_mem hmBJ
  have hφc : Continuous φ.toFun := φ.contDiff.continuous
  obtain ⟨Cφ, hCφ0, hCφ⟩ := PDE.ParabCaccioppoli.exists_bound hU φ
  have hdφ : ∀ i, Continuous fun z : Vec d × ℝ => parSpaceGrad φ.toFun z i := fun i =>
    (φ.contDiff.continuous_fderiv one_ne_zero).clm_apply continuous_const
  -- `L²` bookkeeping on the whole cylinder
  have hF2 : ∀ i, MemLp (fun z : Vec d × ℝ => matVecMul (a₀ z.1) (u.grad z) i) 2 ν :=
    fun i => flux_memLp ha u i
  have hA : ∀ i, MemLp (fun z => φ.toFun z ^ 2 * v.grad z i) 2 ν := fun i => by
    refine (v.gradMemL2 i).of_le_mul (c := Cφ ^ 2) ((hφc.pow 2).aestronglyMeasurable.mul
      (v.gradMemL2 i).aestronglyMeasurable) ?_
    filter_upwards [hae] with z hz
    have h1 := (hCφ z hz).1
    simp only [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) h1 2) (abs_nonneg _)
  have hB : ∀ i, MemLp (fun z => 2 * φ.toFun z * v.toFun z * parSpaceGrad φ.toFun z i) 2 ν :=
    fun i => by
      refine v.memL2.of_le_mul (c := 2 * Cφ * Cφ)
        ((((continuous_const.mul hφc).aestronglyMeasurable.mul v.memL2.aestronglyMeasurable).mul
          (hdφ i).aestronglyMeasurable)) ?_
      filter_upwards [hae] with z hz
      have h1 := (hCφ z hz).1
      have h2 := abs_parSpaceGrad_le φ z Cφ (hCφ z hz).2 i
      simp only [Real.norm_eq_abs, abs_mul, abs_two]
      nlinarith [abs_nonneg (φ.toFun z), abs_nonneg (v.toFun z),
        abs_nonneg (parSpaceGrad φ.toFun z i),
        mul_nonneg (abs_nonneg (φ.toFun z)) (abs_nonneg (v.toFun z)),
        mul_le_mul h1 h2 (abs_nonneg _) hCφ0]
  -- integrability of the three terms
  have i1 : Integrable (fun z : Vec d × ℝ => φ.toFun z ^ 2 * v.toFun z ^ 2) ν := by
    have hφ2 : ∀ᵐ z ∂ν, ‖φ.toFun z ^ 2‖ ≤ Cφ ^ 2 := by
      filter_upwards [hae] with z hz
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hCφ z hz).1 2
    exact (v.memL2.integrable_sq).bdd_mul (hφc.pow 2).aestronglyMeasurable hφ2
  have hvec : ∀ (g : Vec d → ℝ) (z : Vec d × ℝ), g 0 = g 0 → True := fun _ _ _ => trivial
  have hexp : ∀ (z : Vec d × ℝ) (h : Vec d), vecDot (matVecMul (a₀ z.1) (u.grad z)) h =
      ∑ i, matVecMul (a₀ z.1) (u.grad z) i * h i := fun z h => rfl
  have i2 : Integrable (fun z : Vec d × ℝ => φ.toFun z ^ 2 *
      vecDot (matVecMul (a₀ z.1) (u.grad z)) (v.grad z)) ν := by
    have : (fun z : Vec d × ℝ => φ.toFun z ^ 2 * vecDot (matVecMul (a₀ z.1) (u.grad z)) (v.grad z)) =
        fun z => ∑ i, (φ.toFun z ^ 2 * v.grad z i) * matVecMul (a₀ z.1) (u.grad z) i := by
      funext z; rw [hexp, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    exact integrable_finsetSum _ fun i _ => (hA i).integrable_mul (hF2 i)
  have i3 : Integrable (fun z : Vec d × ℝ => 2 * φ.toFun z * v.toFun z *
      vecDot (matVecMul (a₀ z.1) (u.grad z)) (parSpaceGrad φ.toFun z)) ν := by
    have : (fun z : Vec d × ℝ => 2 * φ.toFun z * v.toFun z *
        vecDot (matVecMul (a₀ z.1) (u.grad z)) (parSpaceGrad φ.toFun z)) =
        fun z => ∑ i, (2 * φ.toFun z * v.toFun z * parSpaceGrad φ.toFun z i) *
          matVecMul (a₀ z.1) (u.grad z) i := by
      funext z; rw [hexp, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    exact integrable_finsetSum _ fun i _ => (hB i).integrable_mul (hF2 i)
  refine ⟨i1, i2, i3, ?_⟩
  have key := step2_key ha u v hu hv φ
  have hpt : ∀ z : Vec d × ℝ, (v.toFun z * (φ.toFun z ^ 2 * v.toFun z) +
      ∑ i, matVecMul (a₀ z.1) (u.grad z) i *
        (φ.toFun z ^ 2 * v.grad z i + 2 * φ.toFun z * v.toFun z * parSpaceGrad φ.toFun z i)) =
      (φ.toFun z ^ 2 * v.toFun z ^ 2 + φ.toFun z ^ 2 *
        vecDot (matVecMul (a₀ z.1) (u.grad z)) (v.grad z)) + 2 * φ.toFun z * v.toFun z *
        vecDot (matVecMul (a₀ z.1) (u.grad z)) (parSpaceGrad φ.toFun z) := by
    intro z
    rw [hexp, hexp, Finset.mul_sum, Finset.mul_sum]
    have : ∑ i, matVecMul (a₀ z.1) (u.grad z) i *
        (φ.toFun z ^ 2 * v.grad z i + 2 * φ.toFun z * v.toFun z * parSpaceGrad φ.toFun z i) =
        ∑ i, φ.toFun z ^ 2 * (matVecMul (a₀ z.1) (u.grad z) i * v.grad z i) +
        ∑ i, 2 * φ.toFun z * v.toFun z * (matVecMul (a₀ z.1) (u.grad z) i * parSpaceGrad φ.toFun z i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]; ring
  simp only [hpt] at key
  have i12 : Integrable (fun z : Vec d × ℝ => φ.toFun z ^ 2 * v.toFun z ^ 2 + φ.toFun z ^ 2 *
      vecDot (matVecMul (a₀ z.1) (u.grad z)) (v.grad z)) ν := i1.add i2
  rw [integral_add i12 i3, integral_add i1 i2] at key
  exact key

end PDE.Parabolic.Slice
