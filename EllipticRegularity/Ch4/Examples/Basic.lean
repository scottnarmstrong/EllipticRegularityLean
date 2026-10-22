module

public import PDEFoundation
public import PDEFoundation.PDE.DGNM.Restrict
public import PDEFoundation.PDE.DGNM.Bridge

/-!
# Smooth explicit examples: shared tools

Integration by parts for diagonal constant coefficients against smooth compactly
supported tests, the bridge from a smooth function on `ℝ^d` to a weak (sub)solution
on the unit ball, and essential-supremum computations for continuous functions.
-/

@[expose] public section

namespace PDE.Ch4Examples

open MeasureTheory

/-- The `i`-th coordinate derivative as a function. -/
noncomputable def D {d : ℕ} (i : Fin d) (g : Vec d → ℝ) : Vec d → ℝ :=
  fun x => fderiv ℝ g x (basisVec i)

theorem contDiff_D {d : ℕ} (i : Fin d) {g : Vec d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (D i g) := by
  unfold D
  exact (hg.fderiv_right (m := (⊤ : ℕ∞)) (by exact_mod_cast le_rfl)).clm_apply contDiff_const

/-- Integration by parts for a diagonal constant matrix against a smooth compactly supported
test on all of `ℝ^d`. -/
theorem integral_flux_diag {d : ℕ} (w : Fin d → ℝ) (A : Mat d)
    (hA : ∀ i j : Fin d, A i j = if i = j then w i else 0)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∫ x, vecDot (matVecMul A (fun i => fderiv ℝ f x (basisVec i)))
        (fun i => fderiv ℝ φ x (basisVec i)) =
      -∫ x, (∑ i, w i * D i (D i f) x) * φ x := by
  have hint : ∀ (g : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → ∀ i : Fin d,
      Integrable (fun x => g x * D i φ x) := by
    intro g hg i
    have h1 : Continuous g := hg.continuous
    have h2 : Continuous (D i φ) := (contDiff_D i hφ).continuous
    have h3 : HasCompactSupport (D i φ) := by
      unfold D
      simpa using hc.fderiv_apply (𝕜 := ℝ) (basisVec i)
    exact (h1.mul h2).integrable_of_hasCompactSupport h3.mul_left
  have hint2 : ∀ (g : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → 
      Integrable (fun x => g x * φ x) := by
    intro g hg
    exact (hg.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have key : ∀ i : Fin d, ∫ x, D i f x * D i φ x = -∫ x, D i (D i f) x * φ x := by
    intro i
    have := HasWeakPartialDerivOn.of_contDiff (U := (Set.univ : Set (Vec d))) (i := i)
      ((contDiff_D i hf).of_le (by simp))
    have h := this φ hφ hc (Set.subset_univ _)
    simpa [Measure.restrict_univ, D] using h
  have hL : ∀ x, vecDot (matVecMul A (fun i => fderiv ℝ f x (basisVec i)))
      (fun i => fderiv ℝ φ x (basisVec i)) = ∑ i, w i * (D i f x * D i φ x) := by
    intro x
    unfold vecDot
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [matVecMul_apply, hA, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true, D]
    ring
  simp_rw [hL]
  rw [integral_finsetSum]
  · rw [← integral_neg]
    have : ∀ x, -((∑ i, w i * D i (D i f) x) * φ x) =
        ∑ i, w i * (-(D i (D i f) x * φ x)) := by
      intro x
      rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    simp_rw [this]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul, integral_const_mul, integral_neg, key i]
    · intro i _
      exact ((hint2 _ (contDiff_D i (contDiff_D i hf))).neg).const_mul _
  · intro i _
    exact (hint _ (contDiff_D i hf) i).const_mul _


/-! ### Diagonal ellipticity -/

/-- A diagonal matrix with entries in `[1, Λ]` satisfies the ellipticity convention. -/
theorem isEllipticMatrix_diagonal {d : ℕ} (w : Fin d → ℝ) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hw : ∀ i, 1 ≤ w i ∧ w i ≤ Λ) :
    IsEllipticMatrix 1 Λ (Matrix.diagonal w) := by
  have hwpos : ∀ i, 0 < w i := fun i => lt_of_lt_of_le one_pos (hw i).1
  refine ⟨one_pos, hΛ, ?_, ?_⟩
  · intro ξ
    have : vecDot ξ (matVecMul (Matrix.diagonal w) ξ) = ∑ i, w i * ξ i ^ 2 := by
      unfold vecDot
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [matVecMul_apply, Matrix.diagonal_apply]
      ring
    rw [this, vecNormSq_eq_sum_sq, one_mul]
    exact Finset.sum_le_sum fun i _ => by nlinarith [(hw i).1, sq_nonneg (ξ i)]
  · intro ξ
    have hinv : (Matrix.diagonal w)⁻¹ = Matrix.diagonal (fun i => (w i)⁻¹) := by
      apply Matrix.inv_eq_right_inv
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      simp [(hwpos i).ne']
    have : vecDot ξ (matVecMul (Matrix.diagonal w)⁻¹ ξ) = ∑ i, (w i)⁻¹ * ξ i ^ 2 := by
      rw [hinv]
      unfold vecDot
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [matVecMul_apply, Matrix.diagonal_apply]
      ring
    rw [this, vecNormSq_eq_sum_sq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have : Λ⁻¹ ≤ (w i)⁻¹ := inv_anti₀ (hwpos i) (hw i).2
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

/-! ### From a smooth function to a weak (sub)solution -/

section Bridge

variable {d : ℕ} {U : Set (Vec d)}

theorem flux_integrable_and_eq (_hU : MeasurableSet U) (A : Mat d) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (φ : WeakTestFunction U) :
    Integrable (fun x => vecDot (matVecMul A (classicalGradient f x)) (φ.grad x)) ∧
      ∫ x in U, vecDot (matVecMul A (classicalGradient f x)) (φ.grad x) =
        ∫ x, vecDot (matVecMul A (classicalGradient f x)) (φ.grad x) := by
  have hcont : Continuous (fun x => vecDot (matVecMul A (classicalGradient f x)) (φ.grad x)) := by
    have h1 : Continuous (classicalGradient f) :=
      PDE.ContDiff.continuous_classicalGradient
        (hf.of_le (show (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by exact_mod_cast le_top))
    have h2 : Continuous φ.grad := by
      apply continuous_pi
      intro i
      simp only [WeakTestFunction.grad_apply, WeakTestFunction.partialDeriv]
      exact ((φ.contDiff.continuous_fderiv (by simp))).clm_apply continuous_const
    unfold vecDot matVecMul
    fun_prop
  have hvan : ∀ x ∉ U, vecDot (matVecMul A (classicalGradient f x)) (φ.grad x) = 0 := by
    intro x hx
    rw [DGNM.WeakTestFunction.grad_eq_zero_of_notMem φ hx, DGNM.vecDot_zero_right]
  have hsupp : HasCompactSupport
      (fun x => vecDot (matVecMul A (classicalGradient f x)) (φ.grad x)) := by
    refine HasCompactSupport.intro φ.hasCompactSupport ?_
    intro x hx
    have hxt : x ∉ tsupport φ.toFun := hx
    have : φ.grad x = 0 := by
      funext i
      simp only [WeakTestFunction.grad_apply, WeakTestFunction.partialDeriv]
      rw [fderiv_of_notMem_tsupport ℝ hxt]
      simp
    rw [this, DGNM.vecDot_zero_right]
  refine ⟨hcont.integrable_of_hasCompactSupport hsupp, ?_⟩
  exact setIntegral_eq_integral_of_forall_compl_eq_zero hvan

/-- A smooth function whose flux against every smooth compactly supported test on `ℝ^d` vanishes
is a weak solution on any measurable `U`, for constant coefficients. -/
theorem isWeakSolution_of_smooth (hU : MeasurableSet U) (A : Mat d) (u : H1Function U)
    (hg : u.grad = classicalGradient u.toFun) (hf : ContDiff ℝ (⊤ : ℕ∞) u.toFun)
    (h : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, vecDot (matVecMul A (fun i => fderiv ℝ u.toFun x (basisVec i)))
        (fun i => fderiv ℝ φ x (basisVec i)) = 0) :
    IsWeakDivergenceFormSolutionOn (fun _ => A) U u (0 : Vec d → ℝ) 0 := by
  intro φ
  obtain ⟨hI, hE⟩ := flux_integrable_and_eq hU A hf φ
  have h0 : ∀ x, vecDot ((0 : Vec d → Vec d) x) (φ.grad x) = 0 := fun x => by simp [vecDot]
  have h0' : ∀ x, vecDot (0 : Vec d) (φ.grad x) = 0 := fun x => by simp [vecDot]
  refine ⟨⟨?_, by simp, by simp only [h0]; exact integrableOn_zero⟩, ?_⟩
  · rw [hg]; exact hI.integrableOn
  · simp only [h0', Pi.zero_apply, zero_mul, integral_zero, sub_zero]
    rw [hg, hE]
    exact h φ.toFun φ.contDiff φ.hasCompactSupport

/-- A smooth function whose flux against every nonnegative smooth compactly supported test is
nonpositive is a weak subsolution, for constant coefficients. -/
theorem isWeakSubharmonic_of_smooth (hU : MeasurableSet U) (A : Mat d) (u : H1Function U)
    (hg : u.grad = classicalGradient u.toFun) (hf : ContDiff ℝ (⊤ : ℕ∞) u.toFun)
    (h : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) →
      ∫ x, vecDot (matVecMul A (fun i => fderiv ℝ u.toFun x (basisVec i)))
        (fun i => fderiv ℝ φ x (basisVec i)) ≤ 0) :
    IsWeakDivergenceFormSubharmonicOn (fun _ => A) U u := by
  intro φ hφ
  obtain ⟨hI, hE⟩ := flux_integrable_and_eq hU A hf φ
  have h0 : ∀ x, vecDot ((0 : Vec d → Vec d) x) (φ.grad x) = 0 := fun x => by simp [vecDot]
  have h0' : ∀ x, vecDot (0 : Vec d) (φ.grad x) = 0 := fun x => by simp [vecDot]
  refine ⟨⟨?_, by simp, by simp only [h0]; exact integrableOn_zero⟩, ?_⟩
  · rw [hg]; exact hI.integrableOn
  · simp only [h0', Pi.zero_apply, zero_mul, integral_zero, sub_zero]
    rw [hg, hE]
    exact h φ.toFun φ.contDiff φ.hasCompactSupport hφ

/-- A weak solution is a weak supersolution. -/
theorem superharmonic_of_solution {a : CoeffField d} {u : H1Function U}
    (h : IsWeakDivergenceFormSolutionOn a U u (0 : Vec d → ℝ) 0) :
    IsWeakDivergenceFormSuperharmonicOn a U u := by
  intro φ _
  obtain ⟨ht, he⟩ := h φ
  exact ⟨ht, he.ge⟩

end Bridge

/-! ### Essential suprema of continuous functions -/

theorem le_essSup_of_continuous {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U) {g : Vec d → ℝ}
    (hg : Continuous g) {x₀ : Vec d} (hx : x₀ ∈ U) :
    ENNReal.ofReal (g x₀) ≤ essSup (fun x => ENNReal.ofReal (g x)) (volumeOn U) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨b, hb1, hb2⟩ := exists_between hlt
  have hae := ae_lt_of_essSup_lt hb1
  rw [volumeOn, ae_restrict_iff' hU.measurableSet] at hae
  have hV : IsOpen {x | b < ENNReal.ofReal (g x)} :=
    isOpen_lt continuous_const (ENNReal.continuous_ofReal.comp hg)
  have hpos : 0 < volume ({x | b < ENNReal.ofReal (g x)} ∩ U) :=
    (hV.inter hU).measure_pos volume ⟨x₀, hb2, hx⟩
  have hzero : volume ({x | b < ENNReal.ofReal (g x)} ∩ U) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hae)
    intro x ⟨h1, h2⟩ h3
    exact absurd (h3 h2) (not_lt.2 h1.le)
  exact hpos.ne' hzero

theorem essInf_le_of_continuous {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U) {g : Vec d → ℝ}
    (hg : Continuous g) {x₀ : Vec d} (hx : x₀ ∈ U) :
    essInf (fun x => ENNReal.ofReal (g x)) (volumeOn U) ≤ ENNReal.ofReal (g x₀) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨b, hb1, hb2⟩ := exists_between hlt
  have hae := ae_lt_of_lt_essInf hb2
  rw [volumeOn, ae_restrict_iff' hU.measurableSet] at hae
  have hV : IsOpen {x | ENNReal.ofReal (g x) < b} :=
    isOpen_lt (ENNReal.continuous_ofReal.comp hg) continuous_const
  have hpos : 0 < volume ({x | ENNReal.ofReal (g x) < b} ∩ U) :=
    (hV.inter hU).measure_pos volume ⟨x₀, hb1, hx⟩
  have hzero : volume ({x | ENNReal.ofReal (g x) < b} ∩ U) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hae)
    intro x ⟨h1, h2⟩ h3
    exact absurd (h3 h2) (not_lt.2 h1.le)
  exact hpos.ne' hzero

/-! ### Points of the ball -/

theorem mem_euclideanBall_zero_iff {d : ℕ} (x : Vec d) (R : ℝ) :
    x ∈ euclideanBall (0 : Vec d) R ↔ vecNormSq x < R ^ 2 := by
  simp [euclideanBall, euclideanSqDist]

theorem abs_apply_lt_of_mem_ball {d : ℕ} {x : Vec d} {R : ℝ} (hR : 0 ≤ R)
    (h : x ∈ euclideanBall (0 : Vec d) R) (i : Fin d) : |x i| < R := by
  rw [mem_euclideanBall_zero_iff] at h
  exact abs_lt_of_sq_lt_sq ((sq_apply_le_vecNormSq x i).trans_lt h) hR

theorem smul_basisVec_mem_ball {d : ℕ} (i : Fin d) {t R : ℝ} (h : |t| < R) :
    t • basisVec i ∈ euclideanBall (0 : Vec d) R := by
  rw [mem_euclideanBall_zero_iff, vecNormSq_smul, vecNormSq_basisVec, mul_one]
  exact sq_lt_sq.2 (by rwa [abs_of_pos ((abs_nonneg t).trans_lt h)])

end PDE.Ch4Examples
