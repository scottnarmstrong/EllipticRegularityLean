module

public import EllipticRegularity.Ch4.Examples.CosProduct
public import EllipticRegularity.Ch4.Examples.Slab
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Lower bound for the density estimate: the example (Proposition 4.22)

`u = cosh(√Λ x₁) cos x₂ / (cosh(√Λ θ/C⋆) cos 1)`.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE.Ch4Examples

open MeasureTheory Filter

theorem cos_one_pos : 0 < Real.cos 1 := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_gt_three]

theorem cos_one_gt_half : 1 / 2 < Real.cos 1 := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 1) (y := Real.pi / 3) zero_le_one
    (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three])
  rwa [Real.cos_pi_div_three] at h

/-- The slab estimate turned into the density statement. -/
theorem density_of_slab (n : ℕ) (Cstar l θ : ℝ) (hθ : 0 < θ) (hθ' : θ ≤ 1 / 2)
    (hC : ENNReal.ofReal Cstar * volume (euclideanBall (0 : Vec (n + 1)) 1) =
      2 * volume (euclideanBall (0 : Vec n) 1))
    (hl : l * Cstar = θ) (hlpos : 0 ≤ l) (f : Vec (n + 1) → ℝ)
    (hf : ∀ x ∈ euclideanBall (0 : Vec (n + 1)) 1, l ≤ |x 0| → 1 ≤ f x) :
    ENNReal.ofReal (1 - θ) * volume (euclideanBall (0 : Vec (n + 1)) 1) ≤
      volume {x ∈ euclideanBall (0 : Vec (n + 1)) 1 | 1 ≤ f x} := by
  set B := euclideanBall (0 : Vec (n + 1)) 1 with hB
  have hBtop : volume B ≠ ⊤ := volume_euclideanBall_ne_top _ zero_le_one
  have hslab : volume {x ∈ B | |x 0| < l} ≤ ENNReal.ofReal θ * volume B := by
    refine (slab_measure_le n l).trans_eq ?_
    have h2 : ENNReal.ofReal (2 * l) * volume (euclideanBall (0 : Vec n) 1) =
        ENNReal.ofReal l * (2 * volume (euclideanBall (0 : Vec n) 1)) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      ring
    rw [h2, ← hC, ← mul_assoc, ← ENNReal.ofReal_mul hlpos, hl]
  have hcover : B ⊆ {x ∈ B | 1 ≤ f x} ∪ {x ∈ B | |x 0| < l} := by
    intro x hx
    by_cases h : l ≤ |x 0|
    · exact Or.inl ⟨hx, hf x hx h⟩
    · exact Or.inr ⟨hx, not_le.1 h⟩
  have h1 : volume B ≤ volume {x ∈ B | 1 ≤ f x} + ENNReal.ofReal θ * volume B :=
    (measure_mono hcover).trans ((measure_union_le _ _).trans (by gcongr))
  have hsum : volume B = ENNReal.ofReal (1 - θ) * volume B + ENNReal.ofReal θ * volume B := by
    rw [← add_mul, ← ENNReal.ofReal_add (by linarith) hθ.le]
    simp
  have htop : ENNReal.ofReal θ * volume B ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBtop
  refine ENNReal.le_of_add_le_add_right htop ?_
  rw [← hsum]
  exact h1

/-- Strong form of the `cosh` example. -/
theorem cosh_example_strong (d : ℕ) (hd : 3 ≤ d) (Cstar : ℝ)
    (hC : ENNReal.ofReal Cstar * volume (euclideanBall (0 : Vec d) 1) =
      2 * volume (euclideanBall (0 : Vec (d - 1)) 1))
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (θ : ℝ) (hθ : 0 < θ) (hθ' : θ ≤ 1 / 2) :
    ∃ A : Mat d,
      (∀ i j : Fin d, A i j = if i = j then (if i.val = 1 then Λ else 1) else 0) ∧
      IsEllipticMatrix 1 Λ A ∧
      ∃ u : H1Function (euclideanBall (0 : Vec d) 1),
        (∀ x : Vec d, u.toFun x =
          Real.cosh (Real.sqrt Λ * x ⟨0, by omega⟩) * Real.cos (x ⟨1, by omega⟩) /
            (Real.cosh (Real.sqrt Λ * (θ / Cstar)) * Real.cos 1)) ∧
        u.grad = classicalGradient u.toFun ∧
        ContDiff ℝ (⊤ : ℕ∞) u.toFun ∧
        (∀ x ∈ euclideanBall (0 : Vec d) 1, 0 < u.toFun x) ∧
        (∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          ∫ x, vecDot (matVecMul A (fun i => fderiv ℝ u.toFun x (basisVec i)))
            (fun i => fderiv ℝ φ x (basisVec i)) = 0) ∧
        ENNReal.ofReal (1 - θ) * volume (euclideanBall (0 : Vec d) 1) ≤
          volume {x ∈ euclideanBall (0 : Vec d) 1 | 1 ≤ u.toFun x} ∧
        essInf (fun x => ENNReal.ofReal (u.toFun x))
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
          ENNReal.ofReal (4 * Real.exp (-(θ * Real.sqrt Λ / Cstar))) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hC' : ENNReal.ofReal Cstar * volume (euclideanBall (0 : Vec (n + 1)) 1) =
      2 * volume (euclideanBall (0 : Vec n) 1) := hC
  have hEpos : 0 < volume (euclideanBall (0 : Vec n) 1) := volume_euclideanBall_pos _ one_pos
  have hCpos : 0 < Cstar := by
    have : ENNReal.ofReal Cstar ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hC'
      exact (mul_ne_zero two_ne_zero hEpos.ne') hC'.symm
    exact ENNReal.ofReal_pos.1 (pos_iff_ne_zero.2 this)
  set k := Real.sqrt Λ with hk
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  set l := θ / Cstar with hl
  have hlpos : 0 < l := div_pos hθ hCpos
  have hlC : l * Cstar = θ := by rw [hl]; field_simp
  set D := Real.cosh (k * l) * Real.cos 1 with hD
  have hDpos : 0 < D := mul_pos (Real.cosh_pos _) cos_one_pos
  have hG : ∀ t, HasDerivAt (fun t : ℝ => Real.cosh (k * t) / D) (k * Real.sinh (k * t) / D) t := by
    intro t
    have := ((Real.hasDerivAt_cosh (k * t)).comp t ((hasDerivAt_id t).const_mul k)).div_const D
    exact this.congr_deriv (by simp [mul_comm])
  have hG1 : ∀ t, HasDerivAt (fun t : ℝ => k * Real.sinh (k * t) / D)
      (k ^ 2 * (Real.cosh (k * t) / D)) t := by
    intro t
    have := (((Real.hasDerivAt_sinh (k * t)).comp t ((hasDerivAt_id t).const_mul k)).const_mul
      k).div_const D
    exact this.congr_deriv (by simp; ring)
  have hGs : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.cosh (k * t) / D) :=
    (Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id)).div_const D
  obtain ⟨A, hA, hell, u, hu, hgrad, hsm, hsol⟩ :=
    cosProd_example (n + 1) (by omega) Λ hΛ (G := fun t => Real.cosh (k * t) / D)
      (G1 := fun t => k * Real.sinh (k * t) / D) hG hG1 hGs
  have hu' : ∀ x : Vec (n + 1), u.toFun x =
      Real.cosh (k * x ⟨0, by omega⟩) * Real.cos (x ⟨1, by omega⟩) / D := by
    intro x
    rw [hu]
    ring
  have hcos : ∀ x ∈ euclideanBall (0 : Vec (n + 1)) 1, Real.cos 1 ≤ Real.cos (x ⟨1, by omega⟩) := by
    intro x hx
    have h1 : |x ⟨1, by omega⟩| < 1 := abs_apply_lt_of_mem_ball zero_le_one hx _
    rw [← Real.cos_abs (x ⟨1, by omega⟩)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_gt_three])
      h1.le
  refine ⟨A, hA, hell, u, hu', hgrad, hsm, ?_, hsol, ?_, ?_⟩
  · intro x hx
    rw [hu']
    have h1 : 0 < Real.cos (x ⟨1, by omega⟩) := lt_of_lt_of_le cos_one_pos (hcos x hx)
    have := Real.cosh_pos (k * x ⟨0, by omega⟩)
    positivity
  · refine density_of_slab n Cstar l θ hθ hθ' hC' hlC hlpos.le u.toFun ?_
    intro x hx hlx
    rw [hu']
    rw [le_div_iff₀ hDpos, one_mul, hD]
    have h1 : Real.cosh (k * l) ≤ Real.cosh (k * x ⟨0, by omega⟩) := by
      rw [Real.cosh_le_cosh, abs_of_nonneg (mul_nonneg hk0 hlpos.le), abs_mul,
        abs_of_nonneg hk0]
      exact mul_le_mul_of_nonneg_left hlx hk0
    exact mul_le_mul h1 (hcos x hx) cos_one_pos.le (Real.cosh_pos _).le
  · have h0 := essInf_le_of_continuous (isOpen_euclideanBall (0 : Vec (n + 1)) (1 / 2))
      hsm.continuous
      (smul_basisVec_mem_ball (⟨0, by omega⟩ : Fin (n + 1)) (t := 0) (R := 1 / 2) (by simp))
    refine h0.trans (ENNReal.ofReal_le_ofReal ?_)
    have hu0 : u.toFun ((0 : ℝ) • basisVec (⟨0, by omega⟩ : Fin (n + 1))) = 1 / D := by
      rw [hu']
      simp
    rw [hu0]
    have hcosh : Real.exp (k * l) / 2 ≤ Real.cosh (k * l) := by
      rw [Real.cosh_eq]
      linarith [Real.exp_pos (-(k * l))]
    have hDge : Real.exp (k * l) / 4 ≤ D := by
      rw [hD]
      calc Real.exp (k * l) / 4 = Real.exp (k * l) / 2 * (1 / 2) := by ring
        _ ≤ Real.cosh (k * l) * Real.cos 1 :=
          mul_le_mul hcosh cos_one_gt_half.le (by norm_num) (Real.cosh_pos _).le
    have hexp : Real.exp (-(θ * k / Cstar)) = (Real.exp (k * l))⁻¹ := by
      rw [← Real.exp_neg, hl]
      congr 1
      ring
    rw [hexp, div_le_iff₀ hDpos]
    have hpe := Real.exp_pos (k * l)
    calc 1 = 4 * (Real.exp (k * l))⁻¹ * (Real.exp (k * l) / 4) := by field_simp
      _ ≤ 4 * (Real.exp (k * l))⁻¹ * D := by gcongr

/-- **Lower bound for the density estimate** (Proposition 4.22, first part). -/
theorem cosh_lower_example_full (d : ℕ) (hd : 3 ≤ d) (Cstar : ℝ)
    (hC : ENNReal.ofReal Cstar * volume (euclideanBall (0 : Vec d) 1) =
      2 * volume (euclideanBall (0 : Vec (d - 1)) 1))
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (θ : ℝ) (hθ : 0 < θ) (hθ' : θ ≤ 1 / 2) :
    ∃ A : Mat d,
      (∀ i j : Fin d, A i j = if i = j then (if i.val = 1 then Λ else 1) else 0) ∧
      IsEllipticMatrix 1 Λ A ∧
      ∃ u : H1Function (euclideanBall (0 : Vec d) 1),
        (∀ x : Vec d, u.toFun x =
          Real.cosh (Real.sqrt Λ * x ⟨0, by omega⟩) * Real.cos (x ⟨1, by omega⟩) /
            (Real.cosh (Real.sqrt Λ * (θ / Cstar)) * Real.cos 1)) ∧
        ContDiff ℝ (⊤ : ℕ∞) u.toFun ∧
        (∀ x ∈ euclideanBall (0 : Vec d) 1, 0 < u.toFun x) ∧
        (∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          ∫ x, vecDot (matVecMul A (fun i => fderiv ℝ u.toFun x (basisVec i)))
            (fun i => fderiv ℝ φ x (basisVec i)) = 0) ∧
        ENNReal.ofReal (1 - θ) * volume (euclideanBall (0 : Vec d) 1) ≤
          volume {x ∈ euclideanBall (0 : Vec d) 1 | 1 ≤ u.toFun x} ∧
        essInf (fun x => ENNReal.ofReal (u.toFun x))
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
          ENNReal.ofReal (4 * Real.exp (-(θ * Real.sqrt Λ / Cstar))) := by
  obtain ⟨A, hA, hell, u, hu, -, hsm, hpos, hsol, hdens, hess⟩ :=
    cosh_example_strong d hd Cstar hC Λ hΛ θ hθ hθ'
  exact ⟨A, hA, hell, u, hu, hsm, hpos, hsol, hdens, hess⟩

end PDE.Ch4Examples
