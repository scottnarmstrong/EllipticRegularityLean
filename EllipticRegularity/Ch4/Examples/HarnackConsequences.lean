module

public import EllipticRegularity.Ch4.Examples.HarnackSharp

/-!
# Consequences of the Harnack-sharpness example (Proposition 4.20)
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE.Ch4Examples

open MeasureTheory Filter

/-- If a Harnack constant `M` works for ellipticity `Λ`, then `exp √Λ ≤ M`. -/
theorem harnack_core (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (M : ℝ) (hM : 0 < M)
    (h : ∀ a : CoeffField d,
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j)
        (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ v : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < v.toFun x) →
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) v (0 : Vec d → ℝ) 0 →
        essSup (fun x => ENNReal.ofReal (v.toFun x))
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
          ENNReal.ofReal M *
            essInf (fun x => ENNReal.ofReal (v.toFun x))
              (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) :
    Real.exp (Real.sqrt Λ) ≤ M := by
  obtain ⟨A, hA, hell, u, hu, hgrad, hsm, hpos, hsol, hbd, hess⟩ :=
    harnack_example_strong d hd Λ hΛ
  have hU : MeasurableSet (euclideanBall (0 : Vec d) 1) := (isOpen_euclideanBall _ _).measurableSet
  have H := h (fun _ => A) (fun i j => aemeasurable_const) (fun x _ => hell) u
    ((ae_restrict_iff' hU).2 (Filter.Eventually.of_forall hpos))
    (isWeakSolution_of_smooth hU A u hgrad hsm hsol)
  have hm : 0 < Real.exp (-(Real.sqrt Λ / 2)) * Real.cos (1 / 2) := by
    have : 0 < Real.cos (1 / 2) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> linarith [Real.pi_gt_three]
    positivity
  have hI0 : essInf (fun x => ENNReal.ofReal (u.toFun x))
      (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≠ 0 := by
    have hlow : ENNReal.ofReal (Real.exp (-(Real.sqrt Λ / 2)) * Real.cos (1 / 2)) ≤
        essInf (fun x => ENNReal.ofReal (u.toFun x))
          (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) := by
      refine le_essInf_of_ae_le _ ?_
      rw [volumeOn, EventuallyLE, ae_restrict_iff' (isOpen_euclideanBall _ _).measurableSet]
      exact Filter.Eventually.of_forall fun x hx => ENNReal.ofReal_le_ofReal (hbd x hx).1
    exact (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hm) hlow).ne'
  have hItop : essInf (fun x => ENNReal.ofReal (u.toFun x))
      (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≠ ⊤ := by
    have := essInf_le_of_continuous (isOpen_euclideanBall (0 : Vec d) (1 / 2)) hsm.continuous
      (smul_basisVec_mem_ball (⟨0, by omega⟩ : Fin d) (t := 0) (R := 1 / 2) (by simp))
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top this
  have h2 := hess.trans H
  have h3 := (ENNReal.mul_le_mul_iff_left hI0 hItop).1 h2
  exact (ENNReal.ofReal_le_ofReal_iff hM.le).1 h3

/-- **Consequence of Proposition 4.20**: `log C_H ≥ √Λ`. -/
theorem harnack_constant_lower_bound_full (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (CH : ℝ) (hCH : 1 ≤ CH)
    (h : ∀ a : CoeffField d,
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j)
        (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ v : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < v.toFun x) →
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) v (0 : Vec d → ℝ) 0 →
        essSup (fun x => ENNReal.ofReal (v.toFun x))
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
          ENNReal.ofReal CH *
            essInf (fun x => ENNReal.ofReal (v.toFun x))
              (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) :
    Real.sqrt Λ ≤ Real.log CH := by
  have := harnack_core d hd Λ hΛ CH (by linarith) h
  exact (Real.le_log_iff_exp_le (by linarith)).2 this

/-- **Consequence of Proposition 4.20**: the exponent `β` in `exp (C Λ^β)` is at least `1/2`. -/
theorem harnack_exponent_lower_bound_full (d : ℕ) (hd : 2 ≤ d) (β C : ℝ)
    (h : ∀ Λ : ℝ, 1 ≤ Λ → ∀ a : CoeffField d,
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j)
        (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ v : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < v.toFun x) →
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) v (0 : Vec d → ℝ) 0 →
        essSup (fun x => ENNReal.ofReal (v.toFun x))
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
          ENNReal.ofReal (Real.exp (C * Λ ^ β)) *
            essInf (fun x => ENNReal.ofReal (v.toFun x))
              (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) :
    (1 : ℝ) / 2 ≤ β := by
  by_contra hβ
  push Not at hβ
  have hy : 0 < (1 / 2 : ℝ) - β := by linarith
  have hev : ∀ᶠ Λ : ℝ in atTop, 1 ≤ Λ ∧ C < Λ ^ ((1 / 2 : ℝ) - β) :=
    (eventually_ge_atTop 1).and ((tendsto_rpow_atTop hy).eventually_gt_atTop C)
  obtain ⟨Λ, hΛ1, hΛC⟩ := hev.exists
  have hcore := harnack_core d hd Λ hΛ1 (Real.exp (C * Λ ^ β)) (Real.exp_pos _) (h Λ hΛ1)
  rw [Real.exp_le_exp] at hcore
  have hΛpos : 0 < Λ := by linarith
  have hsplit : Λ ^ ((1 / 2 : ℝ) - β) * Λ ^ β = Real.sqrt Λ := by
    rw [← Real.rpow_add hΛpos, sub_add_cancel, Real.sqrt_eq_rpow]
  have hpos : 0 < Λ ^ β := Real.rpow_pos_of_pos hΛpos _
  have : C * Λ ^ β < Λ ^ ((1 / 2 : ℝ) - β) * Λ ^ β := mul_lt_mul_of_pos_right hΛC hpos
  linarith

/-- **Consequence of Proposition 4.20**: the constant `C` in `exp (C √Λ)` is at least `1`. -/
theorem harnack_constant_ge_one_full (d : ℕ) (hd : 2 ≤ d) (C : ℝ)
    (h : ∀ Λ : ℝ, 1 ≤ Λ → ∀ a : CoeffField d,
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j)
        (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ v : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < v.toFun x) →
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) v (0 : Vec d → ℝ) 0 →
        essSup (fun x => ENNReal.ofReal (v.toFun x))
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
          ENNReal.ofReal (Real.exp (C * Real.sqrt Λ)) *
            essInf (fun x => ENNReal.ofReal (v.toFun x))
              (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) :
    1 ≤ C := by
  have hcore := harnack_core d hd 1 le_rfl (Real.exp (C * Real.sqrt 1)) (Real.exp_pos _)
    (h 1 le_rfl)
  rw [Real.exp_le_exp, Real.sqrt_one] at hcore
  linarith

end PDE.Ch4Examples
