module

public import EllipticRegularity.Guerra.Field.All

/-!
# Guerra sharpness: gradient bound and `u ∈ H¹(B₁)`

For the profile `φ = phi γ` and `0 < α < 1`:
`|∂_i u|² ≤ |∇u|² ≤ (1 + 4γ²) r^{2α-2}` (also at the origin, where the formula gives `0`).
Since `2α - 2 > -2 > -d` for `d ≥ 3`, `r^{2α-2}` is integrable on `B₁`, so every gradient
component lies in `L²(B₁)`. With `u` continuous and bounded on `B₁`, the point-removal lemma
`hasWeakGradientOn_of_punctured_classicalGradient` gives `u ∈ H¹(B₁)` with weak gradient
`gradU`; the same holds for `c + u` for any constant `c`.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory

namespace PDE.Guerra

noncomputable section

variable {d : ℕ}

/-- The unit ball `B₁`. -/
abbrev ball1 (d : ℕ) : Set (Vec d) := euclideanBall (0 : Vec d) 1

/-- Almost every point of any domain is not the origin (`d > 0`). -/
theorem ae_ne_zero_restrict (hd : 0 < d) (U : Set (Vec d)) :
    ∀ᵐ x ∂(volume.restrict U), x ≠ (0 : Vec d) := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  rw [ae_iff]
  have hm : (volume.restrict U) {(0 : Vec d)} = 0 := le_zero_iff.mp <| calc
    (volume.restrict U) {(0 : Vec d)} ≤ volume {(0 : Vec d)} :=
      (Measure.restrict_le_self : volume.restrict U ≤ volume) {(0 : Vec d)}
    _ = 0 := measure_singleton (0 : Vec d)
  simpa only [not_ne_iff] using! hm

theorem sq_apply_le_vecNormSq (v : Vec d) (i : Fin d) : v i ^ 2 ≤ vecNormSq v := by
  rw [vecNormSq_eq_sum_sq]
  exact Finset.single_le_sum (f := fun k => v k ^ 2) (fun k _ => sq_nonneg (v k))
    (Finset.mem_univ i)

theorem gradU_zero {α : ℝ} (hα1 : α < 1) (φ : ℝ → ℝ) (j : Fin d) :
    gradU α φ j (0 : Vec d) = 0 := by
  funext i
  simp [gradU, rad_zero, Real.zero_rpow (show α - 1 ≠ 0 by linarith)]

/-- The pointwise gradient bound `|∂_i u|² ≤ (1 + 4γ²) r^{2α-2}`. -/
theorem sq_gradU_apply_le {γ α : ℝ} (hγ : 1 ≤ γ) (hα : 0 < α) (hα1 : α < 1) (j : Fin d)
    (x : Vec d) (i : Fin d) :
    gradU α (phi γ) j x i ^ 2 ≤ (1 + 4 * γ ^ 2) * rad x ^ (2 * α - 2) := by
  have hC : 0 ≤ 1 + 4 * γ ^ 2 := by positivity
  by_cases hx : x = 0
  · subst hx
    rw [gradU_zero hα1]
    simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg hC (Real.rpow_nonneg (vecEuclideanNorm_nonneg _) _)
  · refine (sq_apply_le_vecNormSq _ i).trans ?_
    rw [vecNormSq_gradU α j hx, mul_comm]
    have hr : 0 ≤ rad x ^ (2 * α - 2) := Real.rpow_nonneg (vecEuclideanNorm_nonneg _) _
    refine mul_le_mul_of_nonneg_right ?_ hr
    set t := lat j x
    have ht := abs_lat_le_one j x
    have ht2 := lat_sq_le_one j x
    have hφ := abs_phi_le_one hγ ht
    have hφ2 : phi γ t ^ 2 ≤ 1 := by
      have := sq_le_sq' (abs_le.mp hφ).1 (abs_le.mp hφ).2
      simpa using this
    rw [deriv_phi γ hγ]
    have hd0 := dphi_pos hγ t
    have hd1 := dphi_le_two_mul hγ t
    have hα2 : α ^ 2 ≤ 1 := by nlinarith
    have e1 : α ^ 2 * phi γ t ^ 2 ≤ 1 := by
      have := mul_le_mul hα2 hφ2 (sq_nonneg _) zero_le_one
      linarith
    have e2 : dphi γ t ^ 2 ≤ 4 * γ ^ 2 := by nlinarith
    have e3 : (1 - t ^ 2) * dphi γ t ^ 2 ≤ 4 * γ ^ 2 := by
      have h0 : 0 ≤ 1 - t ^ 2 := by linarith
      have h1 : 1 - t ^ 2 ≤ 1 := by nlinarith [sq_nonneg t]
      nlinarith [sq_nonneg (dphi γ t)]
    linarith

theorem measurable_gradU_apply {α : ℝ} {φ : ℝ → ℝ} (hφ : Continuous φ) (j i : Fin d) :
    Measurable (fun x : Vec d => gradU α φ j x i) := by
  simp only [gradU]
  refine (measurable_rad.pow_const _).mul ?_
  exact ((measurable_const.mul (hφ.measurable.comp (measurable_lat j))).mul
    (measurable_omega_apply i)).add
    (((measurable_deriv φ).comp (measurable_lat j)).mul (measurable_qvec_apply j i))

theorem measurable_gradU {α : ℝ} {φ : ℝ → ℝ} (hφ : Continuous φ) (j : Fin d) :
    Measurable (gradU α φ j) :=
  measurable_pi_iff.mpr fun i => measurable_gradU_apply hφ j i

theorem continuous_phi (γ : ℝ) (hγ : 1 ≤ γ) : Continuous (phi γ) :=
  (contDiff_phi γ hγ (n := 0)).continuous

/-- Every component of `∇u` lies in `L²(B₁)` (`d ≥ 3`). -/
theorem gradMemL2On_gradU (hd : 3 ≤ d) {γ α : ℝ} (hγ : 1 ≤ γ) (hα : 0 < α) (hα1 : α < 1)
    (j : Fin d) : GradMemL2On (ball1 d) (gradU α (phi γ) j) := by
  intro i
  have hmeas : AEStronglyMeasurable (fun x : Vec d => gradU α (phi γ) j x i)
      (volume.restrict (ball1 d)) :=
    (measurable_gradU_apply (continuous_phi γ hγ) j i).aestronglyMeasurable
  change MemLp (fun x : Vec d => gradU α (phi γ) j x i) 2 (volume.restrict (ball1 d))
  rw [memLp_two_iff_integrable_sq hmeas]
  have hint : IntegrableOn (fun x : Vec d => vecEuclideanNorm x ^ (2 * α - 2)) (ball1 d) := by
    rw [integrableOn_vecEuclideanNorm_rpow_euclideanBall_iff (by omega) one_pos]
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine (hint.const_mul (1 + 4 * γ ^ 2)).mono' (hmeas.pow 2) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_gradU_apply_le hγ hα hα1 j x i

/-- `c + u` is in `L²(B₁)`. -/
theorem memL2On_const_add_uProf {γ α : ℝ} (hγ : 1 ≤ γ) (hα : 0 < α) (j : Fin d) (c : ℝ) :
    MemL2On (ball1 d) (fun x => c + uProf j γ α x) := by
  have : IsFiniteMeasure (volume.restrict (ball1 d)) :=
    isFiniteMeasure_restrict.mpr (volume_euclideanBall_ne_top 0 zero_le_one)
  have hcont : Continuous (fun x => c + uProf j γ α x) :=
    continuous_const.add (continuous_uProf j hγ hα)
  refine MemLp.of_bound hcont.aestronglyMeasurable (|c| + 1) ?_
  refine ae_restrict_of_forall_mem (measurableSet_euclideanBall 0 1) fun x hx => ?_
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt one_pos, sub_zero] at hx
  have h1 := abs_uProf_le j hγ hα x
  have h2 : vecEuclideanNorm x ^ α ≤ 1 :=
    Real.rpow_le_one (vecEuclideanNorm_nonneg x) hx.le hα.le
  rw [Real.norm_eq_abs]
  calc |c + uProf j γ α x| ≤ |c| + |uProf j γ α x| := abs_add_le _ _
    _ ≤ |c| + 1 := by linarith

/-- `c + u ∈ H¹(B₁)` with weak gradient `gradU` (`d ≥ 3`). -/
theorem exists_h1Function_const_add (hd : 3 ≤ d) {γ α : ℝ} (hγ : 1 ≤ γ) (hα : 0 < α)
    (hα1 : α < 1) (j : Fin d) (c : ℝ) :
    ∃ v : H1Function (ball1 d), v.toFun = (fun x => c + uProf j γ α x) ∧
      v.grad = gradU α (phi γ) j := by
  have hG := gradMemL2On_gradU hd hγ hα hα1 j
  have hf := memL2On_const_add_uProf hγ hα j c
  have hP := profileData_guerra hd hγ
  have hu : uProf j γ α = uFun α (phi γ) j := (uFun_phi_eq_uProf j γ α).symm
  have hSmooth : ContDiffOn ℝ 1 (fun x => c + uProf j γ α x) (ball1 d \ {0}) := by
    rw [hu]
    exact contDiffOn_const.add (contDiffOn_uFun (contDiff_phi γ hγ) α j |>.mono
      fun _ hy => hy.2)
  have hGrad : ∀ x ∈ ball1 d \ {0},
      classicalGradient (fun x => c + uProf j γ α x) x = gradU α (phi γ) j x := by
    intro x hx
    have hdiff : DifferentiableAt ℝ (uFun α (phi γ) j) x :=
      (contDiffAt_uFun (n := 1) (contDiff_phi γ hγ) α j hx.2).differentiableAt one_ne_zero
    rw [← classicalGradient_uFun hP.differentiable α j hx.2, hu]
    funext i
    simp only [classicalGradient_apply]
    rw [fderiv_const_add]
  have hW : HasWeakGradientOn (ball1 d) (fun x => c + uProf j γ α x) (gradU α (phi γ) j) :=
    hasWeakGradientOn_of_punctured_classicalGradient (by omega) (isOpen_euclideanBall 0 1)
      hf hG hSmooth hGrad
  exact ⟨⟨fun x => c + uProf j γ α x, gradU α (phi γ) j, hf, hG, hW⟩, rfl, rfl⟩

end

end PDE.Guerra
