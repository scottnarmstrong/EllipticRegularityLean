module

public import PDEFoundation.Sobolev.Trace.Smooth.ChainRule

/-!
# Pointwise bounds for the pullback

For `y = Ψ z ∈ Ω`, the pullback `v = (ζ u) ∘ Ψ` and its model derivatives are bounded by a
constant (depending only on the chart and `ζ`) times `|u (y)| + |∇u (y)|`; at points of the open
half-space whose image is outside `Ω`, everything vanishes.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

/-- `|u| + |∇u|`. -/
noncomputable def gAbs (u : Vec (n + 1) → ℝ) (y : Vec (n + 1)) : ℝ :=
  |u y| + vecEuclideanNorm (classicalGradient u y)

theorem classicalGradient_mul_apply {f g : Vec (n + 1) → ℝ} {y : Vec (n + 1)}
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    classicalGradient (fun x => f x * g x) y =
      f y • classicalGradient g y + g y • classicalGradient f y := by
  funext i
  have h := (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv
  rw [classicalGradient_apply, show (fun x => f x * g x) = f * g from rfl, h]
  simp [classicalGradient]

theorem vecEuclideanNorm_classicalGradient_mul_le {f g : Vec (n + 1) → ℝ} {y : Vec (n + 1)}
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    vecEuclideanNorm (classicalGradient (fun x => f x * g x) y) ≤
      |f y| * vecEuclideanNorm (classicalGradient g y) +
        |g y| * vecEuclideanNorm (classicalGradient f y) := by
  rw [classicalGradient_mul_apply hf hg]
  refine (vecEuclideanNorm_add_le _ _).trans ?_
  rw [vecEuclideanNorm_smul, vecEuclideanNorm_smul]

/-- Bounds of a smooth compactly supported cutoff and its gradient. -/
theorem exists_cutoff_bounds {ζ : Vec (n + 1) → ℝ} (hζ : ContDiff ℝ 1 ζ)
    (hζc : HasCompactSupport ζ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y, |ζ y| ≤ B ∧ vecEuclideanNorm (classicalGradient ζ y) ≤ B := by
  obtain ⟨C₁, hC₁⟩ := hζ.continuous.bounded_above_of_compact_support hζc
  obtain ⟨C₂, hC₂⟩ := (hζ.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hζc.fderiv (𝕜 := ℝ))
  refine ⟨|C₁| + (n + 1) * |C₂|, by positivity, fun y => ⟨?_, ?_⟩⟩
  · have := hC₁ y
    rw [Real.norm_eq_abs] at this
    have : 0 ≤ ((n : ℝ) + 1) * |C₂| := by positivity
    linarith [le_abs_self C₁]
  · refine (vecEuclideanNorm_le_sum_abs _).trans ?_
    calc ∑ i, |classicalGradient ζ y i| ≤ ∑ _i : Fin (n + 1), |C₂| := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [classicalGradient_apply, ← Real.norm_eq_abs]
          calc _ ≤ ‖fderiv ℝ ζ y‖ * ‖basisVec i‖ := (fderiv ℝ ζ y).le_opNorm _
            _ ≤ C₂ * 1 := by
              refine mul_le_mul (hC₂ y) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hC₂ y))
              exact (norm_le_vecEuclideanNorm _).trans (vecEuclideanNorm_basisVec i).le
            _ ≤ |C₂| := by rw [mul_one]; exact le_abs_self _
      _ = (n + 1) * |C₂| := by simp
      _ ≤ _ := by linarith [abs_nonneg C₁]

/-- Pointwise bounds of the pullback and its model derivatives at points mapped into `Ω`. -/
theorem exists_pullback_bound (hΩo : IsOpen Ω) (φ : GraphChart Ω) {ζ : Vec (n + 1) → ℝ}
    (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ u : Vec (n + 1) → ℝ, ContDiffOn ℝ 1 u (closure Ω) →
      ∀ z : Vec n × ℝ, φ.map z ∈ Ω →
        |pullback φ ζ u z| ≤ Kc * gAbs u (φ.map z) ∧
        |normDeriv (pullback φ ζ u) z| ≤ Kc * gAbs u (φ.map z) ∧
        modelGradNorm (pullback φ ζ u) z ≤ Kc * gAbs u (φ.map z) := by
  obtain ⟨B, hB0, hB⟩ := exists_cutoff_bounds hζ hζc
  have hL := φ.L_nonneg
  set M : ℝ := (n : ℝ) * (1 + φ.L) + 1 with hM
  have hM1 : 1 ≤ M := by
    have : 0 ≤ (n : ℝ) * (1 + φ.L) := by positivity
    linarith
  refine ⟨M * B, by positivity, fun u hu z hz => ?_⟩
  set y := φ.map z with hy
  have hn : closure Ω ∈ 𝓝 y := mem_of_superset (hΩo.mem_nhds hz) subset_closure
  have hud : DifferentiableAt ℝ u y :=
    ((hu.differentiableOn one_ne_zero) y (subset_closure hz)).differentiableAt hn
  have hζd : DifferentiableAt ℝ ζ y := (hζ.differentiable (by simp)) y
  have hFd : DifferentiableAt ℝ (fun x => ζ x * u x) y := hζd.mul hud
  have hG : vecEuclideanNorm (classicalGradient (fun x => ζ x * u x) y) ≤ B * gAbs u y := by
    refine (vecEuclideanNorm_classicalGradient_mul_le hζd hud).trans ?_
    have h1 := (hB y).1
    have h2 := (hB y).2
    have h3 := vecEuclideanNorm_nonneg (classicalGradient u y)
    unfold gAbs
    nlinarith [abs_nonneg (u y), abs_nonneg (ζ y), vecEuclideanNorm_nonneg
      (classicalGradient ζ y), mul_nonneg (abs_nonneg (u y)) hB0, mul_nonneg h3 hB0]
  have hg0 : 0 ≤ gAbs u y := by
    unfold gAbs; have := vecEuclideanNorm_nonneg (classicalGradient u y); positivity
  have hcomp : pullback φ ζ u = (fun x => ζ x * u x) ∘ φ.map := rfl
  refine ⟨?_, ?_, ?_⟩
  · unfold pullback
    rw [abs_mul]
    have h1 := (hB y).1
    have h2 : |u y| ≤ gAbs u y := by
      unfold gAbs; have := vecEuclideanNorm_nonneg (classicalGradient u y); linarith
    calc |ζ y| * |u y| ≤ B * gAbs u y := mul_le_mul h1 h2 (abs_nonneg _) hB0
      _ ≤ M * B * gAbs u y := by nlinarith [mul_nonneg hB0 hg0]
  · rw [hcomp]
    refine (normDeriv_comp_le φ hFd).trans (hG.trans ?_)
    nlinarith [mul_nonneg hB0 hg0]
  · rw [hcomp]
    refine (modelGradNorm_comp_le φ hFd).trans ?_
    calc M * vecEuclideanNorm (classicalGradient (fun x => ζ x * u x) y) ≤ M * (B * gAbs u y) :=
          mul_le_mul_of_nonneg_left hG (by linarith)
      _ = M * B * gAbs u y := by ring

/-- Outside the image of `Ω`, the pullback and its model derivatives vanish at points of the open
half-space. -/
theorem pullback_deriv_eq_zero (φ : GraphChart Ω) {ζ u : Vec (n + 1) → ℝ}
    (hts : tsupport ζ ⊆ φ.dom) {z : Vec n × ℝ} (hz : 0 < z.2) (hzΩ : φ.map z ∉ Ω) :
    pullback φ ζ u z = 0 ∧ normDeriv (pullback φ ζ u) z = 0 ∧
      modelGradNorm (pullback φ ζ u) z = 0 := by
  have hev := pullback_eventuallyEq_zero φ (u := u) hts hz hzΩ
  have hf : fderiv ℝ (pullback φ ζ u) z = 0 := by
    rw [hev.fderiv_eq]; simp
  refine ⟨hev.self_of_nhds |>.trans rfl, ?_, ?_⟩
  · simp [normDeriv, hf]
  · have : tanGrad (pullback φ ζ u) z = 0 := by funext i; simp [tanGrad, hf]
    simp [modelGradNorm, this, normDeriv, hf, vecNormSq_eq_sum_sq]

end PDE.TraceLane
