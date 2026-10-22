module

public import PDEFoundation.Monotonicity.ACF.WeightedIdentity
public import PDEFoundation.Monotonicity.ACF.WeightedPolar

/-!
# Polar form of the radial integrals

`∫_{B_R} K(|x|²) h = ∫_{ρ>0} K(ρ²) sphereIntegral 0 ρ h` for radial weights `K` supported inside
`B_R`, with the slice quantities of the interface.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace PDE

noncomputable section

variable {d : ℕ}

theorem sphereIntegral_radial_mul (c : ℝ → ℝ) (g : Vec d → ℝ) (ρ : ℝ) :
    sphereIntegral (0 : Vec d) ρ (fun x => c (vecNormSq x) * g x) =
      c (ρ ^ 2) * sphereIntegral (0 : Vec d) ρ g := by
  unfold sphereIntegral
  have h : ∀ ω : Metric.sphere (0 : HilbertVec d) 1,
      c (vecNormSq ((0 : Vec d) + ρ • (ω : HilbertVec d).toVec)) *
          g ((0 : Vec d) + ρ • (ω : HilbertVec d).toVec) =
        c (ρ ^ 2) * g ((0 : Vec d) + ρ • (ω : HilbertVec d).toVec) := by
    intro ω
    have hn : ‖(ω : HilbertVec d)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
    have : vecNormSq ((0 : Vec d) + ρ • (ω : HilbertVec d).toVec) = ρ ^ 2 := by
      have e : ((0 : Vec d) + ρ • (ω : HilbertVec d).toVec) = ρ • (ω : HilbertVec d).toVec := by
        ext i; simp
      rw [e, vecNormSq_smul, BallDivergence.vecNormSq_toVec, hn]; ring
    rw [this]
  simp only [h]
  rw [integral_const_mul]
  ring

theorem sphereIntegral_congr_ball {R : ℝ} {f g : Vec d → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R)
    (h : ∀ x ∈ euclideanBall (0 : Vec d) R, f x = g x) :
    sphereIntegral (0 : Vec d) ρ f = sphereIntegral (0 : Vec d) ρ g := by
  unfold sphereIntegral
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  apply h
  have hn : ‖(ω : HilbertVec d)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
  rw [mem_euclideanBall_zero_iff]
  have e : ((0 : Vec d) + ρ • (ω : HilbertVec d).toVec) = ρ • (ω : HilbertVec d).toVec := by
    ext i; simp
  rw [e, vecNormSq_smul, BallDivergence.vecNormSq_toVec, hn]
  nlinarith

theorem sphereIntegral_eq_zero_of_not_mem_ball {R : ℝ} {f : Vec d → ℝ} {ρ : ℝ} (hρ : R ≤ ρ)
    (hR : 0 ≤ R) (h : ∀ x, x ∉ euclideanBall (0 : Vec d) R → f x = 0) :
    sphereIntegral (0 : Vec d) ρ f = 0 := by
  unfold sphereIntegral
  have : ∀ ω : Metric.sphere (0 : HilbertVec d) 1,
      f ((0 : Vec d) + ρ • (ω : HilbertVec d).toVec) = 0 := by
    intro ω
    apply h
    have hn : ‖(ω : HilbertVec d)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
    rw [mem_euclideanBall_zero_iff, not_lt]
    have e : ((0 : Vec d) + ρ • (ω : HilbertVec d).toVec) = ρ • (ω : HilbertVec d).toVec := by
      ext i; simp
    rw [e, vecNormSq_smul, BallDivergence.vecNormSq_toVec, hn]
    nlinarith
  simp only [this, integral_zero, mul_zero]

/-- Polar form of a radially weighted integral over the ball (with integrability of the radial
profile). -/
theorem ball_polar_radial [NeZero d] {R : ℝ} (hR : 0 ≤ R) {K : ℝ → ℝ} {ρ₂ : ℝ}
    (hρ₂ : 0 ≤ ρ₂) (hρ₂R : ρ₂ < R) (hK0 : ∀ s, ρ₂ ^ 2 < s → K s = 0) {h : Vec d → ℝ}
    (hint : IntegrableOn (fun x => K (vecNormSq x) * h x) (euclideanBall (0 : Vec d) R)) :
    IntegrableOn (fun ρ => K (ρ ^ 2) * sphereIntegral (0 : Vec d) ρ h) (Ioi (0 : ℝ)) ∧
    ∫ x in euclideanBall (0 : Vec d) R, K (vecNormSq x) * h x =
      ∫ ρ in Ioi (0 : ℝ), K (ρ ^ 2) * sphereIntegral (0 : Vec d) ρ h := by
  have hmeas : MeasurableSet (euclideanBall (0 : Vec d) R) :=
    (isOpen_euclideanBall (0 : Vec d) R).measurableSet
  set g : Vec d → ℝ := (euclideanBall (0 : Vec d) R).indicator
    (fun x => K (vecNormSq x) * h x) with hg
  have hgint : Integrable g := (integrable_indicator_iff hmeas).mpr hint
  obtain ⟨-, hpi, hpol⟩ := polar_package hgint
  have h1 : ∫ x, g x = ∫ x in euclideanBall (0 : Vec d) R, K (vecNormSq x) * h x :=
    integral_indicator hmeas
  have hcongr : ∀ ρ ∈ Ioi (0 : ℝ), sphereIntegral (0 : Vec d) ρ g =
      K (ρ ^ 2) * sphereIntegral (0 : Vec d) ρ h := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hρ
    by_cases hρR : ρ < R
    · have e1 : sphereIntegral (0 : Vec d) ρ g =
          sphereIntegral (0 : Vec d) ρ (fun x => K (vecNormSq x) * h x) :=
        sphereIntegral_congr_ball (R := R) hρ0.le hρR (fun x hx => by simp [hg, hx])
      rw [e1, sphereIntegral_radial_mul]
    · rw [not_lt] at hρR
      have e1 : sphereIntegral (0 : Vec d) ρ g = 0 :=
        sphereIntegral_eq_zero_of_not_mem_ball hρR hR (fun x hx => by simp [hg, hx])
      have e2 : K (ρ ^ 2) = 0 := hK0 _ (by nlinarith [hρ₂R, hρ₂])
      rw [e1, e2, zero_mul]
  refine ⟨hpi.congr_fun hcongr measurableSet_Ioi, ?_⟩
  rw [← h1, hpol]
  exact setIntegral_congr_fun measurableSet_Ioi hcongr

/-- Integrability of the radially weighted flux integrand. -/
theorem integrableOn_radial_flux {R : ℝ} (u : H1Function (euclideanBall (0 : Vec d) R))
    {K : ℝ → ℝ} (hKc : Continuous K) {ρ₂ : ℝ} (hρ₂ : 0 ≤ ρ₂)
    (hK0 : ∀ s, ρ₂ ^ 2 < s → K s = 0) :
    IntegrableOn (fun x => K (vecNormSq x) * (u.toFun x * vecDot x (u.grad x)))
      (euclideanBall (0 : Vec d) R) := by
  have hφc : ∀ i : Fin d, Continuous (fun x : Vec d => K (vecNormSq x) * x i) := fun i =>
    (hKc.comp continuous_vecNormSq).mul (continuous_apply i)
  have hφcs : ∀ i : Fin d, HasCompactSupport (fun x : Vec d => K (vecNormSq x) * x i) := by
    intro i
    refine HasCompactSupport.intro (isCompact_euclideanClosedBall (0 : Vec d) hρ₂) ?_
    intro x hx
    rw [mem_euclideanClosedBall_zero_iff, not_le] at hx
    simp [hK0 _ hx]
  have hterm : ∀ i : Fin d, IntegrableOn (fun x => (u.toFun x * u.grad x i) *
      (K (vecNormSq x) * x i)) (euclideanBall (0 : Vec d) R) := by
    intro i
    obtain ⟨C, hC⟩ := (hφc i).bounded_above_of_compact_support (hφcs i)
    have h1 : MemLp u.toFun 2 (volume.restrict (euclideanBall (0 : Vec d) R)) := u.memL2
    have h2 : MemLp (fun x => u.grad x i) 2 (volume.restrict (euclideanBall (0 : Vec d) R)) :=
      u.gradMemL2 i
    exact Integrable.mul_bdd (c := C) (h1.integrable_mul h2) (hφc i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa using hC x)
  have hsum := integrable_finsetSum (Finset.univ : Finset (Fin d)) (fun i _ => hterm i)
  refine hsum.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [vecDot, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end

end PDE
