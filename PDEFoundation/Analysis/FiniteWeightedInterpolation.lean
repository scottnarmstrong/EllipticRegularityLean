module

public import PDEFoundation.Analysis.FiniteExponentialPairing
public import PDEFoundation.Analysis.FiniteExponentialThreeLines
public import PDEFoundation.Analysis.FiniteInterpolationBoundary

@[expose] public section

open scoped BigOperators

namespace PDE

variable {ι κ : Type*}

private theorem analyticPowerFamilyTerm_eq_exponential
    (x a b : ℝ) (z : ℂ) :
    analyticPowerFamilyTerm x a b z =
      (((SignType.sign x : ℝ) : ℂ) *
        Complex.exp (((Real.log |x| * a : ℝ) : ℂ) * z +
          ((Real.log |x| * b : ℝ) : ℂ))) := by
  rw [analyticPowerFamilyTerm]
  congr 2
  push_cast
  ring

/-- Finite weighted interpolation between quadratic and fourth-power real
operator bounds, in normalized bilinear form. -/
theorem abs_weighted_pairing_le_of_two_four
    [Fintype ι] [Fintype κ]
    (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ))
    (w : ι → ℝ) (v : κ → ℝ) (hw : ∀ i, 0 ≤ w i) (hv : ∀ j, 0 ≤ v j)
    (p M : ℝ) (hp : 2 ≤ p) (hpFour : p ≤ 4) (hM : 1 ≤ M)
    (hTwo : ∀ x : ι → ℝ,
      ∑ j, v j * (T x j) ^ 2 ≤ M ^ 2 * ∑ i, w i * (x i) ^ 2)
    (hFour : ∀ x : ι → ℝ,
      ∑ j, v j * (T x j) ^ 4 ≤ M ^ 4 * ∑ i, w i * (x i) ^ 4)
    (f : ι → ℝ) (g : κ → ℝ)
    (hf : ∑ i, w i * |f i| ^ p = 1)
    (hg : ∑ j, v j * |g j| ^ (p / (p - 1)) = 1) :
    |∑ j, v j * T f j * g j| ≤ M := by
  classical
  let p' : ℝ := p / (p - 1)
  let c : ι → ℂ := fun i => ((SignType.sign (f i) : ℝ) : ℂ)
  let a : ι → ℝ := fun i => Real.log |f i| * (-(p / 4))
  let b : ι → ℂ := fun i => ((Real.log |f i| * (p / 2) : ℝ) : ℂ)
  let e : κ → ℂ := fun j => ((SignType.sign (g j) : ℝ) : ℂ)
  let k : κ → ℝ := fun j => Real.log |g j| * (p' / 4)
  let h : κ → ℂ := fun j => ((Real.log |g j| * (p' / 2) : ℝ) : ℂ)
  let C : ι × κ → ℂ := fun r =>
    (v r.2 : ℂ) * (T (Pi.single r.1 1) r.2 : ℂ) * c r.1 * e r.2
  let A : ι × κ → ℝ := fun r => a r.1 + k r.2
  let B : ι × κ → ℂ := fun r => b r.1 + h r.2
  let pairing : ℂ → ℂ := fun z =>
    ∑ j, (v j : ℂ) *
      coordinatewiseComplexification T
        (fun i => analyticPowerFamilyTerm (f i) (-(p / 4)) (p / 2) z) j *
      analyticPowerFamilyTerm (g j) (p' / 4) (p' / 2) z
  have hrepresentation (z : ℂ) : pairing z = finiteExponentialSum C B A z := by
    have hpair := exponentialPairing_eq_finiteExponentialSum T v c a b e k h z
    rw [← hpair]
    dsimp only [pairing]
    apply Finset.sum_congr rfl
    intro j _
    have hinput :
        (fun i => analyticPowerFamilyTerm (f i) (-(p / 4)) (p / 2) z) =
          fun i => c i * Complex.exp ((a i : ℂ) * z + b i) := by
      funext i
      rw [analyticPowerFamilyTerm_eq_exponential]
    have htest : analyticPowerFamilyTerm (g j) (p' / 4) (p' / 2) z =
        e j * Complex.exp ((k j : ℂ) * z + h j) := by
      rw [analyticPowerFamilyTerm_eq_exponential]
    rw [hinput, htest]
  have hzero : ∀ z : ℂ, z.re = 0 → ‖finiteExponentialSum C B A z‖ ≤ M := by
    intro z hz
    rw [← hrepresentation]
    exact norm_powerFamilyPairing_zero_le T w v hw hv p M hp hM hTwo f g hf
      (by simpa only [p'] using hg) z hz
  have hone : ∀ z : ℂ, z.re = 1 → ‖finiteExponentialSum C B A z‖ ≤ M := by
    intro z hz
    rw [← hrepresentation]
    exact norm_powerFamilyPairing_one_le T w v hw hv p M hp hM hFour f g hf
      (by simpa only [p'] using hg) z hz
  let θ : ℝ := 2 - 4 / p
  have hθ := two_four_interpolation_weight_mem_Icc hp hpFour
  have hinterp : ‖finiteExponentialSum C B A (θ : ℂ)‖ ≤ M :=
    norm_finiteExponentialSum_le_of_boundary C B A M hM hzero hone (θ : ℂ)
      (by simpa only [Complex.ofReal_re, θ] using hθ.1)
      (by simpa only [Complex.ofReal_re, θ] using hθ.2)
  rw [← hrepresentation] at hinterp
  have hpairing : pairing (θ : ℂ) = ((∑ j, v j * T f j * g j : ℝ) : ℂ) := by
    dsimp only [pairing]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    rw [show p' = p / (p - 1) by rfl]
    rw [analyticPowerFamilyTerm_dual_interpolation (g j) p hp]
    have hinput :
        (fun i => analyticPowerFamilyTerm (f i) (-(p / 4)) (p / 2) (θ : ℂ)) =
          fun i => (f i : ℂ) := by
      funext i
      exact analyticPowerFamilyTerm_input_interpolation (f i) p hp
    rw [hinput]
    rw [show coordinatewiseComplexification T (fun i => (f i : ℂ)) j = (T f j : ℂ) by
      apply Complex.ext
      · rfl
      · simp only [coordinatewiseComplexification_im, Complex.ofReal_im]
        rw [show (fun _ : ι => (0 : ℝ)) = 0 by rfl, map_zero]
        rfl]
  rw [hpairing, Complex.norm_real, Real.norm_eq_abs] at hinterp
  exact hinterp

end PDE
