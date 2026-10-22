module

public import EllipticRegularity.Ch4.Meyers.ExamProfile

/-!
# The flux of Meyers' example is divergence free off the origin
-/

@[expose] public section

namespace PDE.Ch4Meyers

open MeasureTheory Set

variable {d : ℕ}

theorem sumProj_apply_basisVec (c : Fin d → ℝ) (i : Fin d) :
    (∑ j : Fin d, c j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j)
      (basisVec i) = c i := by
  simp [basisVec, Pi.single_apply]

/-- The partial derivative `∂_i` of the `i`th flux component (weights `w ≡ 1`). -/
theorem partial_profFlux_apply {x : Vec d} (hs : 0 < axisSq (fun _ => (1 : ℝ)) x) (Λ γ : ℝ)
    (i0 i : Fin d) :
    classicalGradient (fun y => profFlux (fun _ => (1 : ℝ)) Λ γ i0 y i) x i =
      (if i0 = i then 1 else 0) *
          (γ * axisSq (fun _ => (1 : ℝ)) x ^ (γ - 1) * (2 * x i)) +
        (Λ - 1 + 2 * γ * Λ) *
          (axisSq (fun _ => (1 : ℝ)) x ^ (γ - 1) * (x i0 + x i * (if i0 = i then 1 else 0)) +
            x i0 * x i * ((γ - 1) * axisSq (fun _ => (1 : ℝ)) x ^ (γ - 1 - 1) * (2 * x i))) := by
  have hw : ∀ j, (fun _ : Fin d => (1 : ℝ)) j = 0 ∨ (fun _ : Fin d => (1 : ℝ)) j = 1 :=
    fun _ => Or.inr rfl
  set κ := Λ - 1 + 2 * γ * Λ with hκ
  have hfun : (fun y : Vec d => profFlux (fun _ => (1 : ℝ)) Λ γ i0 y i) = fun y =>
      (axisSq (fun _ => (1 : ℝ)) y ^ γ * (1 : ℝ)) * (if i0 = i then 1 else 0) +
        κ * (axisSq (fun _ => (1 : ℝ)) y ^ (γ - 1) * (y i0 * y i)) := by
    funext y; simp only [profFlux]; ring
  have h1 : HasFDerivAt (fun y : Vec d => axisSq (fun _ => (1 : ℝ)) y ^ γ * (1 : ℝ))
      ((axisSq (fun _ => (1 : ℝ)) x ^ γ) • (0 : Vec d →L[ℝ] ℝ) + (1 : ℝ) • ((γ *
        axisSq (fun _ => (1 : ℝ)) x ^ (γ - 1)) •
        ∑ j : Fin d, (2 * (fun _ : Fin d => (1 : ℝ)) j * x j) • ContinuousLinearMap.proj
          (R := ℝ) (φ := fun _ : Fin d => ℝ) j)) x :=
    hasFDerivAt_rpow_mul_coord hw hs γ (fun _ => (1 : ℝ)) (hasFDerivAt_const _ _)
  have h2 : HasFDerivAt (fun y : Vec d => y i0 * y i)
      ((x i0) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i +
        (x i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i0) x :=
    (hasFDerivAt_coord x i0).mul (hasFDerivAt_coord x i)
  have h3 := hasFDerivAt_rpow_mul_coord hw hs (γ - 1) _ h2
  have h4 := (h1.mul_const (if i0 = i then (1 : ℝ) else 0)).fun_add (h3.const_mul κ)
  rw [hfun, classicalGradient_apply, h4.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, sumProj_apply_basisVec,
    ContinuousLinearMap.proj_apply, basisVec_apply, zero_apply]
  simp only [↓reduceIte]
  ring

/-- The divergence of the flux `a ∇u` off the origin. -/
theorem div_profFlux {x : Vec d} (hs : 0 < axisSq (fun _ => (1 : ℝ)) x) (Λ γ : ℝ) (i0 : Fin d) :
    ∑ i, classicalGradient (fun y => profFlux (fun _ => (1 : ℝ)) Λ γ i0 y i) x i =
      axisSq (fun _ => (1 : ℝ)) x ^ (γ - 1) * x i0 *
        (2 * γ + (Λ - 1 + 2 * γ * Λ) * ((d : ℝ) - 1 + 2 * γ)) := by
  have hsum := sum_wx_sq (w := fun _ : Fin d => (1 : ℝ)) (fun _ => Or.inr rfl) x
  simp only [one_mul] at hsum
  have hr : axisSq (fun _ => (1 : ℝ)) x ^ (γ - 1 - 1) =
      axisSq (fun _ => (1 : ℝ)) x ^ (γ - 1) / axisSq (fun _ => (1 : ℝ)) x :=
    Real.rpow_sub_one hs.ne' (γ - 1)
  simp_rw [partial_profFlux_apply hs Λ γ i0, hr]
  generalize axisSq (fun _ => (1 : ℝ)) x ^ (γ - 1) = P at *
  generalize hS : axisSq (fun _ => (1 : ℝ)) x = S at *
  set κ := Λ - 1 + 2 * γ * Λ
  have hterm : ∀ i : Fin d, (if i0 = i then (1 : ℝ) else 0) * (γ * P * (2 * x i)) +
      κ * (P * (x i0 + x i * (if i0 = i then 1 else 0)) +
        x i0 * x i * ((γ - 1) * (P / S) * (2 * x i))) =
      (if i0 = i then 1 else 0) * (2 * γ * P * x i) + κ * P * x i0 +
        κ * P * ((if i0 = i then 1 else 0) * x i) + κ * (2 * (γ - 1) * P / S * x i0) * x i ^ 2 := by
    intro i; ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum,
    hsum]
  field_simp
  ring

end PDE.Ch4Meyers
