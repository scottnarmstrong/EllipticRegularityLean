module

public import EllipticRegularity.Ch4.Examples.CosProduct
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Sharpness of the Harnack inequality: the example (Proposition 4.20)

`u = exp(√Λ x₁) cos x₂` and `a = e₁⊗e₁ + Λ e₂⊗e₂ + Σ_{j ≥ 3} e_j⊗e_j`.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE.Ch4Examples

open MeasureTheory Filter

theorem limit_step {S I : ℝ≥0∞} (hI : I ≠ ⊤) (k : ℝ)
    (h : ∀ t ∈ Set.Ioo (0 : ℝ) (1 / 2), ENNReal.ofReal (Real.exp (2 * k * t)) * I ≤ S) :
    ENNReal.ofReal (Real.exp k) * I ≤ S := by
  have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal (Real.exp (2 * k * t)) * I) (𝓝[<] (1 / 2))
      (𝓝 (ENNReal.ofReal (Real.exp k) * I)) := by
    refine ENNReal.Tendsto.mul_const ?_ (Or.inr hI)
    have h1 : Tendsto (fun t : ℝ => Real.exp (2 * k * t)) (𝓝 (1 / 2)) (𝓝 (Real.exp k)) := by
      have hc : Continuous fun t : ℝ => Real.exp (2 * k * t) := by fun_prop
      have := hc.tendsto (1 / 2)
      rwa [show 2 * k * (1 / 2) = k by ring] at this
    exact (ENNReal.tendsto_ofReal h1).mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 / 2 by norm_num)] with t ht using h t ht

/-- Strong form of the Harnack-sharpness example, also recording the gradient representative
and two-sided bounds on the half ball. -/
theorem harnack_example_strong (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ A : Mat d,
      (∀ i j : Fin d, A i j = if i = j then (if i.val = 1 then Λ else 1) else 0) ∧
      IsEllipticMatrix 1 Λ A ∧
      ∃ u : H1Function (euclideanBall (0 : Vec d) 1),
        (∀ x : Vec d, u.toFun x =
          Real.exp (Real.sqrt Λ * x ⟨0, by omega⟩) * Real.cos (x ⟨1, by omega⟩)) ∧
        u.grad = classicalGradient u.toFun ∧
        ContDiff ℝ (⊤ : ℕ∞) u.toFun ∧
        (∀ x ∈ euclideanBall (0 : Vec d) 1, 0 < u.toFun x) ∧
        (∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          ∫ x, vecDot (matVecMul A (fun i => fderiv ℝ u.toFun x (basisVec i)))
            (fun i => fderiv ℝ φ x (basisVec i)) = 0) ∧
        (∀ x ∈ euclideanBall (0 : Vec d) (1 / 2),
          Real.exp (-(Real.sqrt Λ / 2)) * Real.cos (1 / 2) ≤ u.toFun x ∧
            u.toFun x ≤ Real.exp (Real.sqrt Λ / 2)) ∧
        ENNReal.ofReal (Real.exp (Real.sqrt Λ)) *
            essInf (fun x => ENNReal.ofReal (u.toFun x))
              (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
          essSup (fun x => ENNReal.ofReal (u.toFun x))
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) := by
  set k := Real.sqrt Λ with hk
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  have hG : ∀ t, HasDerivAt (fun t : ℝ => Real.exp (k * t)) (k * Real.exp (k * t)) t := by
    intro t
    have := (Real.hasDerivAt_exp (k * t)).comp t ((hasDerivAt_id t).const_mul k)
    exact this.congr_deriv (by simp [mul_comm])
  have hG1 : ∀ t, HasDerivAt (fun t : ℝ => k * Real.exp (k * t)) (k ^ 2 * Real.exp (k * t)) t := by
    intro t
    have := (hG t).const_mul k
    convert this using 1
    ring
  have hGs : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.exp (k * t)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  obtain ⟨A, hA, hell, u, hu, hgrad, hsm, hsol⟩ :=
    cosProd_example d hd Λ hΛ (G := fun t => Real.exp (k * t)) (G1 := fun t => k * Real.exp (k * t))
      hG hG1 hGs
  refine ⟨A, hA, hell, u, hu, hgrad, hsm, ?_, hsol, ?_, ?_⟩
  · intro x hx
    rw [hu]
    have h1 : |x ⟨1, by omega⟩| < 1 := abs_apply_lt_of_mem_ball zero_le_one hx _
    have : 0 < Real.cos (x ⟨1, by omega⟩) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> linarith [abs_lt.1 h1, Real.pi_gt_three]
    positivity
  · intro x hx
    rw [hu]
    have h0 : |x ⟨0, by omega⟩| < 1 / 2 := abs_apply_lt_of_mem_ball (by norm_num) hx _
    have h1 : |x ⟨1, by omega⟩| < 1 / 2 := abs_apply_lt_of_mem_ball (by norm_num) hx _
    have hc1 : Real.cos (1 / 2) ≤ Real.cos (x ⟨1, by omega⟩) := by
      rw [← Real.cos_abs (x ⟨1, by omega⟩)]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_gt_three])
        h1.le
    have hc2 : Real.cos (x ⟨1, by omega⟩) ≤ 1 := Real.cos_le_one _
    have hc3 : 0 < Real.cos (1 / 2) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> linarith [Real.pi_gt_three]
    have he1 : Real.exp (-(k / 2)) ≤ Real.exp (k * x ⟨0, by omega⟩) := by
      apply Real.exp_le_exp.2
      nlinarith [abs_lt.1 h0]
    have he2 : Real.exp (k * x ⟨0, by omega⟩) ≤ Real.exp (k / 2) := by
      apply Real.exp_le_exp.2
      nlinarith [abs_lt.1 h0]
    have hpos1 : 0 < Real.exp (-(k / 2)) := Real.exp_pos _
    have hpos2 := Real.exp_pos (k * x ⟨0, by omega⟩)
    constructor
    · exact mul_le_mul he1 hc1 hc3.le hpos2.le
    · calc Real.exp (k * x ⟨0, by omega⟩) * Real.cos (x ⟨1, by omega⟩)
          ≤ Real.exp (k / 2) * 1 := mul_le_mul he2 hc2 (by linarith) (Real.exp_pos _).le
        _ = _ := mul_one _
  · -- the essential supremum/infimum computation
    have hcont : Continuous u.toFun := hsm.continuous
    have hne : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    have hpt : ∀ s : ℝ, u.toFun (s • basisVec (⟨0, by omega⟩ : Fin d)) = Real.exp (k * s) := by
      intro s
      rw [hu]
      simp [basisVec_apply, hne.symm]
    have hI : essInf (fun x => ENNReal.ofReal (u.toFun x))
        (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≠ ⊤ := by
      have := essInf_le_of_continuous (isOpen_euclideanBall (0 : Vec d) (1 / 2)) hcont
        (smul_basisVec_mem_ball (⟨0, by omega⟩ : Fin d) (t := 0) (R := 1 / 2) (by simp))
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top this
    refine limit_step hI k ?_
    intro t ht
    have ht' : |t| < 1 / 2 := by rw [abs_of_pos ht.1]; exact ht.2
    have hS := le_essSup_of_continuous (isOpen_euclideanBall (0 : Vec d) (1 / 2)) hcont
      (smul_basisVec_mem_ball (⟨0, by omega⟩ : Fin d) ht')
    have hI' := essInf_le_of_continuous (isOpen_euclideanBall (0 : Vec d) (1 / 2)) hcont
      (smul_basisVec_mem_ball (⟨0, by omega⟩ : Fin d) (t := -t) (by simpa using ht'))
    rw [hpt] at hS hI'
    calc ENNReal.ofReal (Real.exp (2 * k * t)) * _
        ≤ ENNReal.ofReal (Real.exp (2 * k * t)) * ENNReal.ofReal (Real.exp (k * -t)) :=
          by gcongr
      _ = ENNReal.ofReal (Real.exp (k * t)) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          congr 2
          ring
      _ ≤ _ := hS

/-- **Sharpness of the Harnack inequality** (Proposition 4.20, first part). -/
theorem harnack_sharp_example_full (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ A : Mat d,
      (∀ i j : Fin d, A i j = if i = j then (if i.val = 1 then Λ else 1) else 0) ∧
      IsEllipticMatrix 1 Λ A ∧
      ∃ u : H1Function (euclideanBall (0 : Vec d) 1),
        (∀ x : Vec d, u.toFun x =
          Real.exp (Real.sqrt Λ * x ⟨0, by omega⟩) * Real.cos (x ⟨1, by omega⟩)) ∧
        ContDiff ℝ (⊤ : ℕ∞) u.toFun ∧
        (∀ x ∈ euclideanBall (0 : Vec d) 1, 0 < u.toFun x) ∧
        (∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          ∫ x, vecDot (matVecMul A (fun i => fderiv ℝ u.toFun x (basisVec i)))
            (fun i => fderiv ℝ φ x (basisVec i)) = 0) ∧
        ENNReal.ofReal (Real.exp (Real.sqrt Λ)) *
            essInf (fun x => ENNReal.ofReal (u.toFun x))
              (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
          essSup (fun x => ENNReal.ofReal (u.toFun x))
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) := by
  obtain ⟨A, hA, hell, u, hu, -, hsm, hpos, hsol, -, hess⟩ := harnack_example_strong d hd Λ hΛ
  exact ⟨A, hA, hell, u, hu, hsm, hpos, hsol, hess⟩

end PDE.Ch4Examples
