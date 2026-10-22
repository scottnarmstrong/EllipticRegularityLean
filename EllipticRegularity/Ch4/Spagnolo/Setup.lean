module

public import EllipticRegularity.Ch4.Spagnolo.CircleWirtinger
public import PDEFoundation.PDE.DGNM.Bridge
public import PDEFoundation.Geometry.ConvexDomain
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Integrability bookkeeping on the unit disc

Elementary facts used throughout the Piccinini--Spagnolo argument on the unit
disc `B₁ ⊆ Vec 2`: continuous functions are bounded on `B₁`, products of
continuous and `L²` / integrable functions stay in `L²` / integrable, and the
flux `σ = a ∇u`, the energy density `∇u · a ∇u` and the radial flux `σ · x`
have the expected integrability for a weak solution.
-/

@[expose] public section

namespace PDE.Ch4Spagnolo

open MeasureTheory Set

theorem continuous_vecNormSq : Continuous (fun x : Vec 2 => vecNormSq x) := by
  simp only [vecNormSq, vecDot]; fun_prop

theorem continuous_vecEuclideanNorm : Continuous (fun x : Vec 2 => vecEuclideanNorm x) :=
  Real.continuous_sqrt.comp continuous_vecNormSq

theorem mem_ball_one_iff {x : Vec 2} :
    x ∈ euclideanBall (0 : Vec 2) 1 ↔ vecNormSq x < 1 := by
  change vecNormSq (x - 0) < 1 ^ 2 ↔ vecNormSq x < 1
  rw [sub_zero, one_pow]

theorem abs_apply_le_one_of_mem {x : Vec 2} (hx : x ∈ euclideanBall (0 : Vec 2) 1)
    (i : Fin 2) : |x i| ≤ 1 := by
  have h1 := sq_apply_le_vecNormSq x i
  have h2 := mem_ball_one_iff.1 hx
  have : x i ^ 2 ≤ 1 := by linarith
  exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith)

/-- A continuous function is bounded on the unit disc. -/
theorem exists_bound_of_continuous {f : Vec 2 → ℝ} (hf : Continuous f) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ euclideanBall (0 : Vec 2) 1, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Vec 2) 1).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have hx' : x ∈ Metric.closedBall (0 : Vec 2) 1 :=
    Metric.ball_subset_closedBall (euclideanBall_subset_supBall (by norm_num) hx)
  have h1 : |f x| ≤ C := by simpa [Real.norm_eq_abs] using hC x hx'
  exact h1.trans (le_max_left _ _)

theorem ae_bound_of_continuous {f : Vec 2 → ℝ} (hf : Continuous f) :
    ∃ C, 0 ≤ C ∧ ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec 2) 1)), ‖f x‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_continuous hf
  refine ⟨C, hC0, ?_⟩
  filter_upwards [ae_restrict_mem (measurableSet_euclideanBall _ _)] with x hx
  simpa [Real.norm_eq_abs] using hC x hx

/-- Continuous times integrable is integrable on the unit disc. -/
theorem integrableOn_continuous_mul {f g : Vec 2 → ℝ} (hf : Continuous f)
    (hg : IntegrableOn g (euclideanBall (0 : Vec 2) 1)) :
    IntegrableOn (fun x => f x * g x) (euclideanBall (0 : Vec 2) 1) := by
  obtain ⟨C, -, hC⟩ := ae_bound_of_continuous hf
  exact Integrable.bdd_mul hg hf.aestronglyMeasurable hC

/-- Continuous functions are in `L²` of the unit disc. -/
theorem memL2On_of_continuous {f : Vec 2 → ℝ} (hf : Continuous f) :
    MemL2On (euclideanBall (0 : Vec 2) 1) f := by
  obtain ⟨C, -, hC⟩ := ae_bound_of_continuous hf
  have : IsFiniteMeasure (volumeOn (euclideanBall (0 : Vec 2) 1)) :=
    (isOpenBoundedConvexDomain_euclideanBall (0 : Vec 2) one_pos).isFiniteMeasure_volumeOn
  exact MemLp.of_bound hf.aestronglyMeasurable C hC

/-- Continuous times `L²` is in `L²` of the unit disc. -/
theorem memL2On_continuous_mul {f g : Vec 2 → ℝ} (hf : Continuous f)
    (hg : MemL2On (euclideanBall (0 : Vec 2) 1) g) :
    MemL2On (euclideanBall (0 : Vec 2) 1) (fun x => f x * g x) := by
  obtain ⟨C, -, hC⟩ := ae_bound_of_continuous hf
  refine MemLp.of_le_mul (c := C) hg (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable) ?_
  filter_upwards [hC] with x hx
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

/-- The identity vector field is in `L²` of the unit disc. -/
theorem memVectorL2On_id : MemVectorL2On (euclideanBall (0 : Vec 2) 1) (fun x => x) :=
  fun i => memL2On_of_continuous (continuous_apply i)

section Solution

variable {Λ : ℝ} {a : CoeffField 2}

/-- The flux `σ = a ∇u` is in `L²` of the unit disc. -/
theorem memVectorL2On_flux
    (hmeas : ∀ i j : Fin 2, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec 2) 1)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec 2) 1, IsEllipticMatrix 1 Λ (a x))
    (u : H1Function (euclideanBall (0 : Vec 2) 1)) :
    MemVectorL2On (euclideanBall (0 : Vec 2) 1) (fun x => matVecMul (a x) (u.grad x)) :=
  DGNM.memVectorL2On_matVecMul_of_aemeasurable (measurableSet_euclideanBall _ _) hmeas hell
    u.gradMemL2

/-- The energy density `∇u · a ∇u` is integrable on the unit disc. -/
theorem integrableOn_energy
    (hmeas : ∀ i j : Fin 2, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec 2) 1)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec 2) 1, IsEllipticMatrix 1 Λ (a x))
    (u : H1Function (euclideanBall (0 : Vec 2) 1)) :
    IntegrableOn (fun x => vecDot (u.grad x) (matVecMul (a x) (u.grad x)))
      (euclideanBall (0 : Vec 2) 1) :=
  integrableOn_vecDot_of_memVectorL2On u.gradMemL2 (memVectorL2On_flux hmeas hell u)

/-- The radial flux `σ · x` is integrable on the unit disc. -/
theorem integrableOn_flux_dot
    (hmeas : ∀ i j : Fin 2, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec 2) 1)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec 2) 1, IsEllipticMatrix 1 Λ (a x))
    (u : H1Function (euclideanBall (0 : Vec 2) 1)) :
    IntegrableOn (fun x => vecDot (matVecMul (a x) (u.grad x)) x)
      (euclideanBall (0 : Vec 2) 1) :=
  integrableOn_vecDot_of_memVectorL2On (memVectorL2On_flux hmeas hell u) memVectorL2On_id

/-- The product `u (σ · x)` is integrable on the unit disc. -/
theorem integrableOn_mul_flux_dot
    (hmeas : ∀ i j : Fin 2, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec 2) 1)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec 2) 1, IsEllipticMatrix 1 Λ (a x))
    (u : H1Function (euclideanBall (0 : Vec 2) 1)) :
    IntegrableOn (fun x => u x * vecDot (matVecMul (a x) (u.grad x)) x)
      (euclideanBall (0 : Vec 2) 1) := by
  have hux : MemVectorL2On (euclideanBall (0 : Vec 2) 1) (fun x => u x • x) := by
    intro i
    simpa [mul_comm] using memL2On_continuous_mul (continuous_apply i) u.memL2
  have h := integrableOn_vecDot_of_memVectorL2On (memVectorL2On_flux hmeas hell u) hux
  refine h.congr_fun (fun x _ => ?_) (measurableSet_euclideanBall _ _)
  simp only [DGNM.vecDot_smul_right]

/-- The energy density is nonnegative on the unit disc. -/
theorem energy_nonneg
    (hell : ∀ x ∈ euclideanBall (0 : Vec 2) 1, IsEllipticMatrix 1 Λ (a x))
    (u : H1Function (euclideanBall (0 : Vec 2) 1)) {x : Vec 2}
    (hx : x ∈ euclideanBall (0 : Vec 2) 1) :
    0 ≤ vecDot (u.grad x) (matVecMul (a x) (u.grad x)) :=
  DGNM.vecDot_matVecMul_self_nonneg (hell x hx) _

/-- The tangential derivative `x⊥ · ∇u` is in `L²` of the unit disc. -/
theorem memL2On_perpDot_grad (u : H1Function (euclideanBall (0 : Vec 2) 1)) :
    MemL2On (euclideanBall (0 : Vec 2) 1) (fun x => perpDot x (u.grad x)) :=
  (memL2On_continuous_mul (continuous_apply 0) (u.grad_memL2 1)).sub
    (memL2On_continuous_mul (continuous_apply 1) (u.grad_memL2 0))

end Solution

end PDE.Ch4Spagnolo
