module

public import EllipticRegularity.Ch4.GreenDecay.DirichletFull

/-!
# Weak maximum principle on `B_R` (Lemma 4.34)

The negative part `v₋` of `v ∈ H¹₀(B_R)` is an `H¹₀(B_R)` function with gradient `-1_{v<0} ∇v`
(`positivePartH10` applied to `-v`); testing with it and using coercivity and Poincaré
gives `v₋ = 0`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4GreenDecay

open MeasureTheory PDE PDE.Ch4Infra

noncomputable section

variable {d : ℕ}

/-- The negation of an `H¹₀` function, as a difference. -/
def negH10 {U : Set (Vec d)} (v : H10Function U) : H10Function U := h10Sub (h10Sub v v) v

theorem negH10_toFun {U : Set (Vec d)} (v : H10Function U) (x : Vec d) :
    (negH10 v).toH1Function.toFun x = -v.toH1Function.toFun x := by
  change v.toH1Function.toFun x - v.toH1Function.toFun x - v.toH1Function.toFun x = _
  ring

theorem negH10_grad {U : Set (Vec d)} (v : H10Function U) (x : Vec d) :
    (negH10 v).toH1Function.grad x = -v.toH1Function.grad x := by
  change v.toH1Function.grad x - v.toH1Function.grad x - v.toH1Function.grad x = _
  rw [sub_self, zero_sub]

/-- Negative part of `v ∈ H¹₀(B_R)`: an `H¹₀` function with value `max (-v) 0` and gradient
`-1_{v<0} ∇v`. -/
theorem exists_negativePart_h10 {U : Set (Vec d)} (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (v : H10Function U) :
    ∃ φ : H10Function U,
      (∀ x, φ.toH1Function.toFun x = max (-v.toH1Function.toFun x) 0) ∧
      (∀ x, φ.toH1Function.grad x =
        {y | v.toH1Function.toFun y < 0}.indicator (fun x => -v.toH1Function.grad x) x) := by
  refine ⟨positivePartH10 hU hfin (negH10 v) (le_refl 0), fun x => ?_, fun x => ?_⟩
  · change max ((negH10 v).toH1Function.toFun x - 0) 0 = _
    rw [negH10_toFun, sub_zero]
  · change {y | (0 : ℝ) < (negH10 v).toH1Function.toFun y}.indicator
      (negH10 v).toH1Function.grad x = _
    by_cases h : v.toH1Function.toFun x < 0
    · have h' : (0 : ℝ) < (negH10 v).toH1Function.toFun x := by rw [negH10_toFun]; linarith
      rw [Set.indicator_of_mem (show x ∈ {y | (0 : ℝ) < (negH10 v).toH1Function.toFun y} from h'),
        Set.indicator_of_mem (show x ∈ {y | v.toH1Function.toFun y < 0} from h), negH10_grad]
    · have h' : ¬ (0 : ℝ) < (negH10 v).toH1Function.toFun x := by
        rw [negH10_toFun]; linarith [not_lt.1 h]
      rw [Set.indicator_of_notMem (show x ∉ {y | (0 : ℝ) < (negH10 v).toH1Function.toFun y} from h'),
        Set.indicator_of_notMem (show x ∉ {y | v.toH1Function.toFun y < 0} from h)]

/-- **Weak maximum principle** (first part), on a bounded open set with a Poincaré inequality. -/
theorem maxPrinciple_of_supersolution_of_poincare {U : Set (Vec d)} (hU : IsOpen U)
    (hfin : volume U ≠ ⊤) {P Λ : ℝ}
    (hP : ∀ u : H10Function U, (∫ x in U, u.toH1Function.toFun x ^ 2) ≤
      P * ∫ x in U, vecNormSq (u.toH1Function.grad x)) {b : CoeffField d}
    (hbell : ∀ x ∈ U, IsEllipticMatrix 1 Λ (b x))
    (v : H10Function U)
    (hv : ∀ φ : H10Function U,
      (∀ᵐ x ∂(volumeOn U), 0 ≤ φ.toH1Function.toFun x) →
        IntegrableOn (fun x => vecDot (φ.toH1Function.grad x)
            (matVecMul (b x) (v.toH1Function.grad x))) U ∧
          0 ≤ ∫ x in U,
            vecDot (φ.toH1Function.grad x) (matVecMul (b x) (v.toH1Function.grad x))) :
    ∀ᵐ x ∂(volumeOn U), 0 ≤ v.toH1Function.toFun x := by
  have hUm : MeasurableSet U := hU.measurableSet
  obtain ⟨φ, hφf, hφg⟩ := exists_negativePart_h10 hU hfin v
  have hφnn : ∀ᵐ x ∂(volumeOn U), 0 ≤ φ.toH1Function.toFun x :=
    Filter.Eventually.of_forall fun x => by rw [hφf]; exact le_max_right _ _
  have h0 := (hv φ hφnn).2
  have hmem : ∀ᵐ x ∂ volumeOn U, x ∈ U :=
    (MeasureTheory.ae_restrict_iff' hUm).2 (Filter.Eventually.of_forall fun x hx => hx)
  have hint := integrableOn_vecNormSq_of_memVectorL2On φ.toH1Function.gradMemL2
  have hint2 := (hv φ hφnn).1
  have hle : (∫ x in U, vecNormSq (φ.toH1Function.grad x)) ≤
      -∫ x in U, vecDot (φ.toH1Function.grad x) (matVecMul (b x) (v.toH1Function.grad x)) := by
    rw [← integral_neg]
    refine integral_mono_ae hint hint2.neg ?_
    filter_upwards [hmem] with x hx
    by_cases h : v.toH1Function.toFun x < 0
    · rw [hφg, Set.indicator_of_mem (show x ∈ {y | v.toH1Function.toFun y < 0} from h)]
      have := (hbell x hx).coercive (v.toH1Function.grad x)
      rw [one_mul] at this
      have e : vecDot (-v.toH1Function.grad x) (matVecMul (b x) (v.toH1Function.grad x)) =
          -vecDot (v.toH1Function.grad x) (matVecMul (b x) (v.toH1Function.grad x)) := by
        simp [vecDot, Finset.sum_neg_distrib]
      rw [vecNormSq_neg, e, neg_neg]
      exact this
    · rw [hφg, Set.indicator_of_notMem (show x ∉ {y | v.toH1Function.toFun y < 0} from h)]
      simp [vecNormSq, vecDot]
  have hint0 : (∫ x in U, vecNormSq (φ.toH1Function.grad x)) = 0 :=
    le_antisymm (by linarith) (integral_nonneg fun x => vecNormSq_nonneg _)
  have hpoinc := hP φ
  rw [hint0, mul_zero] at hpoinc
  have hu2 : (∫ x in U, φ.toH1Function.toFun x ^ 2) = 0 :=
    le_antisymm hpoinc (integral_nonneg fun x => sq_nonneg _)
  have hu2ae : (fun x => φ.toH1Function.toFun x ^ 2) =ᵐ[volumeOn U] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _)
      (φ.toH1Function.memL2.integrable_sq)).1 hu2
  filter_upwards [hu2ae] with x hx
  have hx' : φ.toH1Function.toFun x ^ 2 = 0 := hx
  have hz := (pow_eq_zero_iff (two_ne_zero)).1 hx'
  rw [hφf] at hz
  have := le_max_left (-v.toH1Function.toFun x) 0
  linarith

/-- **Weak maximum principle** on `B_R`: a weak supersolution in `H¹₀(B_R)` is nonnegative. -/
theorem maxPrinciple_of_supersolution (hd : 0 < d) {Λ R : ℝ} (hR : 0 < R) {b : CoeffField d}
    (hbell : ∀ x ∈ euclideanBall (0 : Vec d) R, IsEllipticMatrix 1 Λ (b x))
    (v : H10Function (euclideanBall (0 : Vec d) R))
    (hv : ∀ φ : H10Function (euclideanBall (0 : Vec d) R),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), 0 ≤ φ.toH1Function.toFun x) →
        IntegrableOn (fun x => vecDot (φ.toH1Function.grad x)
            (matVecMul (b x) (v.toH1Function.grad x))) (euclideanBall (0 : Vec d) R) ∧
          0 ≤ ∫ x in euclideanBall (0 : Vec d) R,
            vecDot (φ.toH1Function.grad x) (matVecMul (b x) (v.toH1Function.grad x))) :
    ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), 0 ≤ v.toH1Function.toFun x :=
  maxPrinciple_of_supersolution_of_poincare (isOpen_euclideanBall 0 R)
    (volume_euclideanBall_ne_top 0 hR.le)
    (fun u => h10_setIntegral_sq_le_four_mul_radius_sq_setIntegral_vecNormSq_grad_on_euclideanBall
      hd hR u) hbell v hv

/-- A solution of `-div (b ∇v) = g` with `g ≥ 0` is a weak supersolution. -/
theorem supersolution_of_source_nonneg {U : Set (Vec d)} {b : CoeffField d} {g : Vec d → ℝ}
    (hg : ∀ᵐ x ∂(volumeOn U), 0 ≤ g x) {v : H10Function U}
    (hv : IsWeakDivergenceFormH10SolutionOn b U v.toH1Function g (0 : Vec d → Vec d))
    (φ : H10Function U) (hφ : ∀ᵐ x ∂(volumeOn U), 0 ≤ φ.toH1Function.toFun x) :
    IntegrableOn (fun x => vecDot (φ.toH1Function.grad x)
        (matVecMul (b x) (v.toH1Function.grad x))) U ∧
      0 ≤ ∫ x in U, vecDot (φ.toH1Function.grad x) (matVecMul (b x) (v.toH1Function.grad x)) := by
  obtain ⟨htest, heq⟩ := hv φ
  have hcomm : (fun x => vecDot (φ.toH1Function.grad x) (matVecMul (b x) (v.toH1Function.grad x))) =
      fun x => vecDot (matVecMul (b x) (v.toH1Function.grad x)) (φ.toH1Function.grad x) := by
    funext x; exact vecDot_comm _ _
  rw [hcomm]
  refine ⟨htest.flux_integrable, ?_⟩
  rw [heq]
  simp only [Pi.zero_apply, vecDot, zero_mul, Finset.sum_const_zero, integral_zero, sub_zero]
  exact integral_nonneg_of_ae (by
    filter_upwards [hg, hφ] with x h1 h2
    exact mul_nonneg h1 h2)

end

end PDE.Ch4GreenDecay
