module

public import PDEFoundation.Monotonicity.ACF.WeightedFlux
public import PDEFoundation.Monotonicity.ACF.WeightedKernelBound

/-!
# Integrability on the ball and a.e. slice integrability

For `u ∈ H¹(B_R)` and its gradient `G = u.grad`, the functions `u²`, `|G|²`, `(∂_r u)²`,
`u ∂_r u`, `u (x · G)` are integrable on `B_R`; by the polar decomposition this yields, for a.e.
`ρ ∈ (0, R)`, integrability of the corresponding slices.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace PDE

noncomputable section

variable {d : ℕ} {R : ℝ}

/-- `SphereIntegrable` only depends on the integrand on the ball containing the sphere. -/
theorem sphereIntegrable_congr_ball {f g : Vec d → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R)
    (h : ∀ x ∈ euclideanBall (0 : Vec d) R, f x = g x) (hf : SphereIntegrable ρ f) :
    SphereIntegrable ρ g := by
  unfold SphereIntegrable at *
  refine hf.congr (Filter.Eventually.of_forall fun ω => ?_)
  apply h
  have hn : ‖(ω : HilbertVec d)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
  rw [mem_euclideanBall_zero_iff]
  have e : ((0 : Vec d) + ρ • (ω : HilbertVec d).toVec) = ρ • (ω : HilbertVec d).toVec := by
    ext i; simp
  rw [e, vecNormSq_smul, BallDivergence.vecNormSq_toVec, hn]
  nlinarith

section Measurability

variable (u : H1Function (euclideanBall (0 : Vec d) R))

theorem aesm_grad_coord (i : Fin d) :
    AEStronglyMeasurable (fun x => u.grad x i) (volume.restrict (euclideanBall (0 : Vec d) R)) :=
  (show MemLp (fun x => u.grad x i) 2 (volume.restrict (euclideanBall (0 : Vec d) R)) from
    u.gradMemL2 i).aestronglyMeasurable

theorem aesm_vecDot_grad :
    AEStronglyMeasurable (fun x => vecDot x (u.grad x))
      (volume.restrict (euclideanBall (0 : Vec d) R)) := by
  unfold vecDot
  exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
    ((continuous_apply i).aestronglyMeasurable).mul (aesm_grad_coord u i)

theorem aesm_vecNormSq_grad :
    AEStronglyMeasurable (fun x => vecNormSq (u.grad x))
      (volume.restrict (euclideanBall (0 : Vec d) R)) := by
  unfold vecNormSq vecDot
  exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
    (aesm_grad_coord u i).mul (aesm_grad_coord u i)

theorem aesm_radialDeriv :
    AEStronglyMeasurable (radialDeriv u.grad)
      (volume.restrict (euclideanBall (0 : Vec d) R)) := by
  unfold radialDeriv
  simp only [div_eq_mul_inv]
  exact (aesm_vecDot_grad u).mul
    ((Real.continuous_sqrt.comp continuous_vecNormSq).measurable.inv).aestronglyMeasurable

theorem integrableOn_sq_u : IntegrableOn (fun x => u.toFun x ^ 2) (euclideanBall (0 : Vec d) R) :=
  (show MemLp u.toFun 2 (volume.restrict (euclideanBall (0 : Vec d) R)) from
    u.memL2).integrable_sq

theorem integrableOn_vecNormSq_grad :
    IntegrableOn (fun x => vecNormSq (u.grad x)) (euclideanBall (0 : Vec d) R) := by
  unfold vecNormSq vecDot
  exact integrable_finsetSum _ fun i _ =>
    (show MemLp (fun x => u.grad x i) 2 (volume.restrict (euclideanBall (0 : Vec d) R)) from
      u.gradMemL2 i).integrable_sq.congr (Filter.Eventually.of_forall fun x => by ring)

theorem sq_radialDeriv_le (x : Vec d) (G : Vec d → Vec d) :
    radialDeriv G x ^ 2 ≤ vecNormSq (G x) := by
  unfold radialDeriv
  rcases (vecEuclideanNorm_nonneg x).eq_or_lt with h0 | hpos
  · rw [← h0]; simp [vecNormSq_nonneg]
  · rw [div_pow, div_le_iff₀ (by positivity), vecEuclideanNorm_sq, mul_comm]
    exact sq_vecDot_le_vecNormSq_mul_vecNormSq x (G x)

theorem integrableOn_sq_radialDeriv :
    IntegrableOn (fun x => radialDeriv u.grad x ^ 2) (euclideanBall (0 : Vec d) R) := by
  refine (integrableOn_vecNormSq_grad u).mono' ((aesm_radialDeriv u).pow 2)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_radialDeriv_le x u.grad

theorem integrableOn_mul_radialDeriv :
    IntegrableOn (fun x => u.toFun x * radialDeriv u.grad x) (euclideanBall (0 : Vec d) R) := by
  have hb : IntegrableOn (fun x => (u.toFun x ^ 2 + vecNormSq (u.grad x)) / 2)
      (euclideanBall (0 : Vec d) R) :=
    ((integrableOn_sq_u u).add (integrableOn_vecNormSq_grad u)).div_const 2
  refine hb.mono' ((u.memL2.aestronglyMeasurable).mul (aesm_radialDeriv u))
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 := sq_radialDeriv_le x u.grad
  nlinarith [sq_nonneg (|u.toFun x| - |radialDeriv u.grad x|), sq_abs (u.toFun x),
    sq_abs (radialDeriv u.grad x), abs_nonneg (u.toFun x), abs_nonneg (radialDeriv u.grad x)]

theorem integrableOn_flux :
    IntegrableOn (fun x => u.toFun x * vecDot x (u.grad x)) (euclideanBall (0 : Vec d) R) := by
  have hb : IntegrableOn (fun x => |R| * ((u.toFun x ^ 2 + vecNormSq (u.grad x)) / 2))
      (euclideanBall (0 : Vec d) R) :=
    (((integrableOn_sq_u u).add (integrableOn_vecNormSq_grad u)).div_const 2).const_mul |R|
  refine hb.mono' ((u.memL2.aestronglyMeasurable).mul (aesm_vecDot_grad u)) ?_
  rw [ae_restrict_iff' (isOpen_euclideanBall (0 : Vec d) R).measurableSet]
  refine Filter.Eventually.of_forall fun x hx => ?_
  have hxR : vecEuclideanNorm x ≤ |R| := by
    have hx' : vecNormSq x < R ^ 2 := mem_euclideanBall_zero_iff.mp hx
    unfold vecEuclideanNorm
    calc Real.sqrt (vecNormSq x) ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt hx'.le
      _ = |R| := Real.sqrt_sq_eq_abs R
  have hdot := abs_vecDot_le_vecEuclideanNorm_mul x (u.grad x)
  have hG : vecEuclideanNorm (u.grad x) ^ 2 = vecNormSq (u.grad x) := vecEuclideanNorm_sq _
  have hb0 := vecEuclideanNorm_nonneg (u.grad x)
  rw [Real.norm_eq_abs, abs_mul]
  set a := |u.toFun x| with ha
  set b := vecEuclideanNorm (u.grad x) with hbb
  have ha2 : a ^ 2 = u.toFun x ^ 2 := sq_abs _
  have h1 : |vecDot x (u.grad x)| ≤ |R| * b :=
    hdot.trans (mul_le_mul_of_nonneg_right hxR hb0)
  calc a * |vecDot x (u.grad x)| ≤ a * (|R| * b) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |R| * (a * b) := by ring
    _ ≤ |R| * ((u.toFun x ^ 2 + vecNormSq (u.grad x)) / 2) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [← ha2, ← hG]
        nlinarith [sq_nonneg (a - b)]

end Measurability

/-- A.e. slice integrability of an integrable function on the ball. -/
theorem ae_sphereIntegrable_of_integrableOn [NeZero d] {f : Vec d → ℝ}
    (hf : IntegrableOn f (euclideanBall (0 : Vec d) R)) :
    ∀ᵐ ρ ∂(volume.restrict (Ioo (0 : ℝ) R)), SphereIntegrable ρ f := by
  have hmeas : MeasurableSet (euclideanBall (0 : Vec d) R) :=
    (isOpen_euclideanBall (0 : Vec d) R).measurableSet
  have hg : Integrable ((euclideanBall (0 : Vec d) R).indicator f) :=
    (integrable_indicator_iff hmeas).mpr hf
  obtain ⟨h1, -, -⟩ := polar_package hg
  have h2 : ∀ᵐ ρ ∂(volume.restrict (Ioo (0 : ℝ) R)),
      SphereIntegrable ρ ((euclideanBall (0 : Vec d) R).indicator f) :=
    ae_restrict_of_ae_restrict_of_subset (fun ρ hρ => hρ.1) h1
  filter_upwards [h2, ae_restrict_mem measurableSet_Ioo] with ρ hρ hρm
  exact sphereIntegrable_congr_ball hρm.1.le hρm.2
    (fun x hx => by simp [hx]) hρ

/-- Integrability of the slice-integral profile on `(0, R)`. -/
theorem integrableOn_slice_of_integrableOn [NeZero d] {f : Vec d → ℝ}
    (hf : IntegrableOn f (euclideanBall (0 : Vec d) R)) :
    IntegrableOn (fun ρ => sphereIntegral (0 : Vec d) ρ f) (Ioo (0 : ℝ) R) := by
  have hmeas : MeasurableSet (euclideanBall (0 : Vec d) R) :=
    (isOpen_euclideanBall (0 : Vec d) R).measurableSet
  have hg : Integrable ((euclideanBall (0 : Vec d) R).indicator f) :=
    (integrable_indicator_iff hmeas).mpr hf
  obtain ⟨-, h2, -⟩ := polar_package hg
  refine (h2.mono_set (fun ρ hρ => hρ.1)).congr_fun (fun ρ hρ => ?_) measurableSet_Ioo
  exact sphereIntegral_congr_ball hρ.1.le hρ.2 (fun x hx => by simp [hx])

end

end PDE
