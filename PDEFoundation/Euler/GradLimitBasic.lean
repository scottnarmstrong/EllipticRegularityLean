module

public import PDEFoundation.Euler.L2Limit
public import PDEFoundation.Euler.SmoothIdentities

/-!
# Gradient matrices of smooth periodic fields and `L²(cube)` bookkeeping

`gradMat u x = (∂ⱼuᵢ(x))ᵢⱼ`, its Frobenius norm, the finite-measure instance for the cube, and the identity
`‖∇w‖_{L²(cube)} = ‖curl w‖_{L²(cube)}` for smooth periodic divergence-free `w` (from `integral_sq_gradient_eq_integral_sq_curl` in `PDEFoundation.Euler.SmoothIdentities`).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE

/-- The gradient matrix `(∂ⱼuᵢ)ᵢⱼ` of a planar field. -/
noncomputable def gradMat (u : Vec 2 → Vec 2) (x : Vec 2) : Fin 2 → Fin 2 → ℝ :=
  fun i j => pd j (fun y => u y i) x

/-- Frobenius norm of a `2 × 2` array. -/
noncomputable def matFrobNorm (A : Fin 2 → Fin 2 → ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, A i j ^ 2)

theorem matFrobNorm_nonneg (A : Fin 2 → Fin 2 → ℝ) : 0 ≤ matFrobNorm A := Real.sqrt_nonneg _

theorem continuous_matFrobNorm : Continuous matFrobNorm := by
  unfold matFrobNorm
  fun_prop

theorem abs_apply_le_matFrobNorm (A : Fin 2 → Fin 2 → ℝ) (i j : Fin 2) :
    |A i j| ≤ matFrobNorm A := by
  unfold matFrobNorm
  refine Real.abs_le_sqrt ?_
  have h1 : A i j ^ 2 ≤ ∑ j', A i j' ^ 2 :=
    Finset.single_le_sum (f := fun j' => A i j' ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', A i j' ^ 2 ≤ ∑ i', ∑ j', A i' j' ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', A i' j' ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  exact h1.trans h2

theorem norm_le_matFrobNorm (A : Fin 2 → Fin 2 → ℝ) : ‖A‖ ≤ matFrobNorm A := by
  refine (pi_norm_le_iff_of_nonneg (matFrobNorm_nonneg A)).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (matFrobNorm_nonneg A)).2 fun j => ?_
  simpa [Real.norm_eq_abs] using abs_apply_le_matFrobNorm A i j

instance isFiniteMeasure_restrict_torusCube : IsFiniteMeasure (volume.restrict torusCube) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_Icc : IsCompact torusCube).measure_lt_top⟩

theorem memLp_cube_of_continuous {E : Type*} [NormedAddCommGroup E] {f : Vec 2 → E}
    (hf : Continuous f) (p : ℝ≥0∞) :
    MemLp f p (volume.restrict torusCube) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact torusCube).exists_bound_of_continuousOn hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable.restrict C
    ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun x hx => hC x hx))

theorem continuous_pd_of_contDiff {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : Fin 2) :
    Continuous (pd j f) := (contDiff_pd_top hf j).continuous

theorem continuous_gradMat_apply {u : Vec 2 → Vec 2} (hu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => u x i))
    (i j : Fin 2) : Continuous fun x => gradMat u x i j :=
  continuous_pd_of_contDiff (hu i) j

theorem continuous_gradMat {u : Vec 2 → Vec 2} (hu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => u x i)) :
    Continuous (gradMat u) :=
  continuous_pi fun i => continuous_pi fun j => continuous_gradMat_apply hu i j

theorem continuous_torusCurl {u : Vec 2 → Vec 2} (hu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => u x i)) :
    Continuous (torusCurl u) :=
  (continuous_pd_of_contDiff (hu 1) 0).sub (continuous_pd_of_contDiff (hu 0) 1)

/-- For smooth periodic divergence-free `w`: `‖∇w‖_{L²(cube)} = ‖curl w‖_{L²(cube)}`. -/
theorem eLpNorm_matFrobNorm_gradMat_eq_curl {w : Vec 2 → Vec 2}
    (hw : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => w x i)) (hwp : IsTorusPeriodic w)
    (hdiv : ∀ x, torusDiv w x = 0) :
    eLpNorm (fun x => matFrobNorm (gradMat w x)) 2 (volume.restrict torusCube) =
      eLpNorm (torusCurl w) 2 (volume.restrict torusCube) := by
  have hg : MemLp (fun x => matFrobNorm (gradMat w x)) 2 (volume.restrict torusCube) :=
    memLp_cube_of_continuous (continuous_matFrobNorm.comp (continuous_gradMat hw)) 2
  have hc : MemLp (torusCurl w) 2 (volume.restrict torusCube) :=
    memLp_cube_of_continuous (continuous_torusCurl hw) 2
  rw [hg.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    hc.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  congr 2
  have key := integral_sq_gradient_eq_integral_sq_curl hw hwp hdiv
  have e1 : ∫ x in torusCube, ‖matFrobNorm (gradMat w x)‖ ^ ENNReal.toReal 2 =
      ∫ x in torusCube, ∑ i, ∑ j, pd j (fun y => w y i) x ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs, matFrobNorm, gradMat]
    exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have e2 : ∫ x in torusCube, ‖torusCurl w x‖ ^ ENNReal.toReal 2 =
      ∫ x in torusCube, torusCurl w x ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [e1, e2, key]

end PDE
