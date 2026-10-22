module

public import EllipticRegularity.Parabolic.Cauchy.Weights.ThresholdSplit
public import EllipticRegularity.Parabolic.WeakSlice.Product
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Integrated weighted `L²` estimate

The Nash threshold split is applied to the integrated weighted energy
identity.  The remaining term is an explicit time weighted integral of the
ordinary `L²` slice energy; no pointwise derivative of that energy is assumed.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Weights

open MeasureTheory Set

variable {d : ℕ}

/-- The integrated weighted estimate before sending the mollification scale
to zero.  The time moment is kept as an input so the theorem cleanly separates
the Gaussian algebra from the diagonal Nash estimate. -/
theorem nashPolynomialGaussian_weightedEndpoint_bound {H Lam : ℝ}
    {K : Set (Vec d)} (hK : K.Nonempty) {R A σ s : ℝ}
    (hH : 0 < H) (hLam : 1 ≤ Lam) (hR : 0 ≤ R)
    (hA : Lam < A) (hσ : 0 < σ) (n : ℕ)
    {a : ParCoeffField d}
    (ha : IsParabolicCoeff 1 Lam a univ (Icc s (s + H)))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s (s + H)))
    (hu : IsCauchySolution a s (s + H) f u)
    {D : ℝ}
    (hMomentInt : IntegrableOn
      (fun z : Vec d × ℝ =>
        (nashPositiveTimeShift σ (z.2 - s)) ^ ((((d : ℝ) + 2) / 2) - 1) *
          u.toFun z ^ 2)
      ((univ : Set (Vec d)) ×ˢ Ioc s (s + H)))
    (hMomentBound : ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s (s + H),
      (nashPositiveTimeShift σ (z.2 - s)) ^ ((((d : ℝ) + 2) / 2) - 1) *
        u.toFun z ^ 2 ≤ D) :
    ∫ x : Vec d,
      nashPolynomialGaussianWeight (d := d) H K R A σ s n (x, s + H) ^ 2 *
      u.toFun (x, s + H) ^ 2 ≤
      (∫ x : Vec d,
        nashPolynomialGaussianWeight (d := d) H K R A σ s n (x, s) ^ 2 * f x ^ 2) +
        (((d : ℝ) + 2) / 2) *
          Real.exp (2 * ((((d : ℝ) + 2) / 2) /
            (2 * (1 - Lam / A)))) * D := by
  let Q : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s (s + H)
  let κ : ℝ := ((d : ℝ) + 2) / 2
  let δ : ℝ := 1 - Lam / A
  let m : ℝ := κ / (2 * δ)
  let C : ℝ := κ * Real.exp (2 * m)
  let cLoss := nashPolynomialGaussianLossCoefficient
    (d := d) H K R Lam A σ s n
  let moment : Vec d × ℝ → ℝ := fun z =>
    (nashPositiveTimeShift σ (z.2 - s)) ^ (κ - 1) * u.toFun z ^ 2
  have hApos : 0 < A := lt_of_le_of_lt (by linarith) hA
  have hδpos : 0 < δ := by
    have hratio : Lam / A < 1 := (div_lt_one₀ hApos).2 hA
    dsimp [δ]
    linarith
  have hCnonneg : 0 ≤ C := by dsimp [C, κ]; positivity
  have hloss := nashPolynomialGaussianLoss_integrableOn
    (d := d) (s := s) hK hH hLam hR hA hσ n (u := u)
  have hloss' : IntegrableOn (fun z => -2 * (cLoss z * u.toFun z ^ 2)) Q := by
    dsimp [Q, cLoss]
    exact hloss.const_mul (-2)
  have hcmp : ∀ᵐ z ∂(volume.restrict Q),
      -2 * (cLoss z * u.toFun z ^ 2) ≤ C * moment z := by
    filter_upwards [ae_restrict_mem
      (MeasurableSet.prod MeasurableSet.univ measurableSet_Ioc)] with z hz
    have hpt := nashPolynomialGaussianLoss_split_pointwise
      (d := d) (s := s) hK hH hLam hA hσ hR n z hz.2.1.le hz.2.2
    have hu2 : 0 ≤ u.toFun z ^ 2 := sq_nonneg _
    have hscaled := mul_le_mul_of_nonneg_right hpt hu2
    dsimp [cLoss, C, moment, κ, m, δ]
    calc
      -2 * (nashPolynomialGaussianLossCoefficient (d := d)
          H K R Lam A σ s n z * u.toFun z ^ 2) =
          (-2 * nashPolynomialGaussianLossCoefficient (d := d)
            H K R Lam A σ s n z) * u.toFun z ^ 2 := by ring
      _ ≤ ((((d : ℝ) + 2) / 2) *
          Real.exp (2 * ((((d : ℝ) + 2) / 2) /
            (2 * (1 - Lam / A)))) *
            (nashPositiveTimeShift σ (z.2 - s)) ^ ((((d : ℝ) + 2) / 2) - 1)) *
            u.toFun z ^ 2 := hscaled
      _ = C * moment z := by ring
  have hrightInt : IntegrableOn (fun z => C * moment z) Q := by
    dsimp [Q, moment]
    exact hMomentInt.const_mul C
  have hIntegralCmp : ∫ z in Q, -2 * (cLoss z * u.toFun z ^ 2) ≤
      C * (∫ z in Q, moment z) := by
    have hmono := integral_mono_ae hloss' hrightInt hcmp
    simpa only [integral_const_mul] using hmono
  have hMomentBound' : ∫ z in Q, moment z ≤ D := by
    simpa [Q, moment, κ] using hMomentBound
  have henergy := nashPolynomialGaussian_energy_dissipation
    (d := d) (s := s) hK hH hLam hR hA hσ n ha f hf u hu
  have hendpoint :
      ∫ x : Vec d,
        nashPolynomialGaussianWeight (d := d) H K R A σ s n
          (x, s + H) ^ 2 * u.toFun (x, s + H) ^ 2 ≤
        (∫ x : Vec d,
          nashPolynomialGaussianWeight (d := d) H K R A σ s n (x, s) ^ 2 * f x ^ 2) +
          ∫ z in Q, -2 * (cLoss z * u.toFun z ^ 2) := by
    have hE' :
        (∫ x : Vec d,
          nashPolynomialGaussianWeight (d := d) H K R A σ s n
            (x, s + H) ^ 2 * u.toFun (x, s + H) ^ 2) +
          2 * ∫ z in Q, cLoss z * u.toFun z ^ 2 ≤
          ∫ x : Vec d,
            nashPolynomialGaussianWeight (d := d) H K R A σ s n (x, s) ^ 2 * f x ^ 2 := by
      simpa [Q, cLoss] using henergy
    have hneg : ∫ z in Q, -2 * (cLoss z * u.toFun z ^ 2) =
        -(2 * ∫ z in Q, cLoss z * u.toFun z ^ 2) := by
      rw [integral_const_mul]
      ring
    calc
      _ ≤ (∫ x : Vec d,
          nashPolynomialGaussianWeight (d := d) H K R A σ s n (x, s) ^ 2 *
            f x ^ 2) -
          2 * ∫ z in Q, cLoss z * u.toFun z ^ 2 := by linarith [hE']
      _ = _ := by rw [hneg]; ring
  calc
    ∫ x : Vec d,
        nashPolynomialGaussianWeight (d := d) H K R A σ s n
          (x, s + H) ^ 2 * u.toFun (x, s + H) ^ 2 ≤
        (∫ x : Vec d,
          nashPolynomialGaussianWeight (d := d) H K R A σ s n (x, s) ^ 2 * f x ^ 2) +
          ∫ z in Q, -2 * (cLoss z * u.toFun z ^ 2) := hendpoint
    _ ≤ (∫ x : Vec d,
          nashPolynomialGaussianWeight (d := d) H K R A σ s n (x, s) ^ 2 * f x ^ 2) +
          C * (∫ z in Q, moment z) := by
        calc
          _ = (∫ z in Q, -2 * (cLoss z * u.toFun z ^ 2)) +
              (∫ x : Vec d,
                nashPolynomialGaussianWeight (d := d) H K R A σ s n
                  (x, s) ^ 2 * f x ^ 2) := by ring
          _ ≤ C * (∫ z in Q, moment z) +
              (∫ x : Vec d,
                nashPolynomialGaussianWeight (d := d) H K R A σ s n
                  (x, s) ^ 2 * f x ^ 2) :=
            add_le_add_left hIntegralCmp _
          _ = _ := by ring
    _ ≤ (∫ x : Vec d,
          nashPolynomialGaussianWeight (d := d) H K R A σ s n (x, s) ^ 2 * f x ^ 2) +
          C * D := by
        calc
          _ = C * (∫ z in Q, moment z) +
              (∫ x : Vec d,
                nashPolynomialGaussianWeight (d := d) H K R A σ s n
                  (x, s) ^ 2 * f x ^ 2) := by ring
          _ ≤ C * D +
              (∫ x : Vec d,
                nashPolynomialGaussianWeight (d := d) H K R A σ s n
                  (x, s) ^ 2 * f x ^ 2) :=
            add_le_add_left (mul_le_mul_of_nonneg_left hMomentBound' hCnonneg) _
          _ = _ := by ring

end PDE.Parabolic.Cauchy.Weights
