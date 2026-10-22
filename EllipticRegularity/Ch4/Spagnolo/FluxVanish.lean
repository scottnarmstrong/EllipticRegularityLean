module

public import EllipticRegularity.Ch4.Spagnolo.Flux
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# The circle flux vanishes

Manuscript Theorem 4.24, Step 2, `F = 0`. Write `σ = a ∇u` and
`F(ρ) = ρ ∫_{-π}^{π} (σ · x)(ρ e(θ)) dθ` (the flux of `σ` through the circle
of radius `ρ`, times `ρ`). The radial flux identity
`∫_{B₁} X'(|x|²) σ · x = 0` of `Flux.lean`, written in polar coordinates, says
`∫ ζ F = 0` for every smooth `ζ` compactly supported in `(0, 1)`; hence
`F = 0` a.e. on `(0, 1)`, and therefore `∫_{B₁} R(|x|) σ · x = 0` for every
continuous radial profile `R`.
-/

@[expose] public section

namespace PDE.Ch4Spagnolo

open MeasureTheory Set

/-- A smooth primitive of a smooth function vanishing on `[s₀, ∞)`, itself
vanishing on `[s₀, ∞)`. -/
theorem exists_primitive_vanishing {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {s0 : ℝ}
    (hs : ∀ t, s0 ≤ t → χ t = 0) :
    ∃ X : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) X ∧ (∀ t, deriv X t = χ t) ∧
      ∀ t, s0 ≤ t → X t = 0 := by
  refine ⟨fun t => ∫ s in s0..t, χ s, ?_, ?_, ?_⟩
  · have hderiv : deriv (fun t => ∫ s in s0..t, χ s) = χ := by
      funext t
      exact (hχ.continuous.integral_hasStrictDerivAt s0 t).hasDerivAt.deriv
    refine contDiff_infty_iff_deriv.2 ⟨fun t =>
      (hχ.continuous.integral_hasStrictDerivAt s0 t).hasDerivAt.differentiableAt, ?_⟩
    rw [hderiv]
    exact hχ
  · intro t
    exact (hχ.continuous.integral_hasStrictDerivAt s0 t).hasDerivAt.deriv
  · intro t ht
    have : ∀ s ∈ uIcc s0 t, χ s = 0 := by
      intro s hs'
      rw [uIcc_of_le ht] at hs'
      exact hs s hs'.1
    show ∫ s in s0..t, χ s = 0
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) this]
    simp

/-- A function with compact support inside `(0, 1)` vanishes near `0` and near
`1`. -/
theorem exists_vanishing_bounds {ζ : ℝ → ℝ} (hζc : HasCompactSupport ζ)
    (hζU : tsupport ζ ⊆ Ioo 0 1) :
    ∃ α β : ℝ, 0 < α ∧ 0 ≤ β ∧ β < 1 ∧ (∀ t, t ≤ α → ζ t = 0) ∧
      (∀ t, β ≤ t → ζ t = 0) := by
  rcases (tsupport ζ).eq_empty_or_nonempty with hK | hK
  · have hz : ∀ t, ζ t = 0 := fun t =>
      image_eq_zero_of_notMem_tsupport (by rw [hK]; exact notMem_empty t)
    exact ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, fun t _ => hz t,
      fun t _ => hz t⟩
  have hmin := hζc.isCompact.sInf_mem hK
  have hmax := hζc.isCompact.sSup_mem hK
  have hm0 : 0 < sInf (tsupport ζ) := (hζU hmin).1
  have hM1 : sSup (tsupport ζ) < 1 := (hζU hmax).2
  have hM0 : 0 < sSup (tsupport ζ) := (hζU hmax).1
  refine ⟨sInf (tsupport ζ) / 2, (sSup (tsupport ζ) + 1) / 2, by positivity, by positivity,
    by linarith, fun t ht => ?_, fun t ht => ?_⟩
  · refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
    have := csInf_le hζc.isCompact.bddBelow hmem
    linarith
  · refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
    have := le_csSup hζc.isCompact.bddAbove hmem
    linarith

/-- The profile `t ↦ ζ(√t)` of a smooth function vanishing on `(-∞, α]`,
`α > 0`, is smooth. -/
theorem contDiff_comp_sqrt {ζ : ℝ → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) {α : ℝ} (hα : 0 < α)
    (hζα : ∀ t, t ≤ α → ζ t = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t => ζ (Real.sqrt t)) := by
  refine contDiff_iff_contDiffAt.2 fun t => ?_
  rcases lt_or_ge t (α ^ 2) with ht | ht
  · have hev : (fun s => ζ (Real.sqrt s)) =ᶠ[nhds t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      refine hζα _ ?_
      rcases lt_or_ge s 0 with hs0 | hs0
      · rw [Real.sqrt_eq_zero'.2 hs0.le]; exact hα.le
      · exact (Real.sqrt_lt' hα).2 hs |>.le
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have ht0 : t ≠ 0 := (lt_of_lt_of_le (by positivity) ht).ne'
    exact hζ.contDiffAt.comp t (Real.contDiffAt_sqrt ht0)

section Solution

variable {Λ : ℝ} {a : CoeffField 2}

/-- The circle flux `F(ρ) = ∫_{-π}^{π} ρ (1_{B₁} σ · x)(ρ e(θ)) dθ`. -/
noncomputable def circleFlux (a : CoeffField 2) (u : H1Function (euclideanBall (0 : Vec 2) 1))
    (ρ : ℝ) : ℝ :=
  ∫ θ in Ioo (-Real.pi) Real.pi, ρ * (euclideanBall (0 : Vec 2) 1).indicator
    (fun x => vecDot (matVecMul (a x) (u.grad x)) x) (polarVec ρ θ)

/-- Polar form of a radially weighted flux integral. -/
theorem integral_radial_flux_dot_eq_polar
    (hmeas : ∀ i j : Fin 2, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec 2) 1)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec 2) 1, IsEllipticMatrix 1 Λ (a x))
    (u : H1Function (euclideanBall (0 : Vec 2) 1))
    {W : Vec 2 → ℝ} (hW : Continuous W) {R : ℝ → ℝ}
    (hWR : ∀ ρ θ, 0 < ρ → W (polarVec ρ θ) = R ρ) :
    ∫ x in euclideanBall (0 : Vec 2) 1, W x * vecDot (matVecMul (a x) (u.grad x)) x =
      ∫ ρ in Ioi (0 : ℝ), R ρ * circleFlux a u ρ := by
  have hint := integrableOn_continuous_mul hW (integrableOn_flux_dot hmeas hell u)
  rw [setIntegral_ball_eq_polar hint]
  refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
  simp only [circleFlux]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp only
  by_cases hmem : polarVec ρ θ ∈ euclideanBall (0 : Vec 2) 1
  · simp only [indicator_of_mem hmem, hWR ρ θ hρ]; ring
  · simp [indicator_of_notMem hmem]

theorem integrableOn_circleFlux
    (hmeas : ∀ i j : Fin 2, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec 2) 1)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec 2) 1, IsEllipticMatrix 1 Λ (a x))
    (u : H1Function (euclideanBall (0 : Vec 2) 1)) :
    IntegrableOn (circleFlux a u) (Ioi 0) :=
  integrableOn_polar_radial ((integrable_indicator_iff (measurableSet_euclideanBall _ _)).2
    (integrableOn_flux_dot hmeas hell u))

theorem circleFlux_eq_zero_of_one_le (u : H1Function (euclideanBall (0 : Vec 2) 1))
    {ρ : ℝ} (hρ : 1 ≤ ρ) : circleFlux a u ρ = 0 := by
  unfold circleFlux
  rw [integral_polar_indicator_ball (by linarith)]
  simp [not_lt.2 hρ]

/-- **The circle flux vanishes** for a.e. radius in `(0, 1)`. -/
theorem circleFlux_ae_eq_zero
    (hmeas : ∀ i j : Fin 2, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec 2) 1)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec 2) 1, IsEllipticMatrix 1 Λ (a x))
    (u : H1Function (euclideanBall (0 : Vec 2) 1))
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec 2) 1) u
      (0 : Vec 2 → ℝ) 0) :
    ∀ᵐ ρ, ρ ∈ Ioo (0 : ℝ) 1 → circleFlux a u ρ = 0 := by
  refine isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (((integrableOn_circleFlux hmeas hell u).mono_set Ioo_subset_Ioi_self).locallyIntegrableOn)
    ?_
  intro ζ hζ hζc hζU
  obtain ⟨α, β, hα, hβ0, hβ1, hζα, hζβ⟩ := exists_vanishing_bounds hζc hζU
  have hχ := contDiff_comp_sqrt hζ hα hζα
  have hχs : ∀ t, β ^ 2 ≤ t → ζ (Real.sqrt t) = 0 := by
    intro t ht
    refine hζβ _ ?_
    rw [← Real.sqrt_sq hβ0]
    exact Real.sqrt_le_sqrt ht
  obtain ⟨X, hX, hXd, hXs⟩ := exists_primitive_vanishing hχ hχs
  have hβsq : β ^ 2 < 1 := by nlinarith
  have hF1 := integral_deriv_radial_mul_flux_dot_eq_zero hmeas hell u hsol hX hβsq hXs
  simp only [hXd] at hF1
  have hpolar := integral_radial_flux_dot_eq_polar hmeas hell u
    (W := fun x => ζ (Real.sqrt (vecNormSq x))) (R := ζ)
    (hχ.continuous.comp continuous_vecNormSq)
    (fun ρ θ hρ => by simp only [vecNormSq_polarVec, Real.sqrt_sq hρ.le])
  rw [hF1] at hpolar
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ))]
  · simpa only [smul_eq_mul] using hpolar.symm
  · intro ρ hρ
    simp only [mem_Ioi, not_lt] at hρ
    simp [hζα ρ (hρ.trans hα.le)]

/-- **Orthogonality of radial profiles to the flux.** For every continuous `R`,
`∫_{B₁} R(|x|) σ · x = 0`. -/
theorem integral_radial_mul_flux_dot_eq_zero
    (hmeas : ∀ i j : Fin 2, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec 2) 1)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec 2) 1, IsEllipticMatrix 1 Λ (a x))
    (u : H1Function (euclideanBall (0 : Vec 2) 1))
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec 2) 1) u
      (0 : Vec 2 → ℝ) 0)
    {R : ℝ → ℝ} (hR : Continuous R) :
    ∫ x in euclideanBall (0 : Vec 2) 1,
      R (vecEuclideanNorm x) * vecDot (matVecMul (a x) (u.grad x)) x = 0 := by
  rw [integral_radial_flux_dot_eq_polar hmeas hell u (R := R)
    (W := fun x => R (vecEuclideanNorm x)) (hR.comp continuous_vecEuclideanNorm)
    (fun ρ θ hρ => by simp only [vecEuclideanNorm_polarVec hρ.le])]
  refine setIntegral_eq_zero_of_ae_eq_zero ?_
  filter_upwards [circleFlux_ae_eq_zero hmeas hell u hsol] with ρ hρ hρpos
  rcases lt_or_ge ρ 1 with h1 | h1
  · rw [hρ ⟨hρpos, h1⟩, mul_zero]
  · rw [circleFlux_eq_zero_of_one_le u h1, mul_zero]

end Solution

end PDE.Ch4Spagnolo
