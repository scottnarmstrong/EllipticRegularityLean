module

public import EllipticRegularity.Parabolic.Cauchy.Weights.WeightedL2
public import EllipticRegularity.Parabolic.Cauchy.Energy.Exhaustion
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Removing the spatial mollification in the weighted estimate

The initial slice converges to the unweighted datum when it is supported in
the set from which the distance is measured.  The final slice converges to the
Gaussian of the truncated distance by dominated convergence.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Weights

open MeasureTheory Set Filter Topology

variable {d : ℕ}

/-- Weighted endpoint estimate for the actual truncated distance, after the
standard mollification is removed. -/
theorem nashTruncatedDistance_weightedEndpoint_bound {H Lam : ℝ}
    {K : Set (Vec d)} (hK : K.Nonempty) {R A σ s : ℝ}
    (hH : 0 < H) (hLam : 1 ≤ Lam) (hR : 0 ≤ R)
    (hA : Lam < A) (hσ : 0 < σ)
    {a : ParCoeffField d}
    (ha : IsParabolicCoeff 1 Lam a univ (Icc s (s + H)))
    (f : Vec d → ℝ) (_hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (hfsupp : ∀ᵐ x : Vec d ∂volume, x ∉ K → f x = 0)
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
    (H + σ) ^ (((d : ℝ) + 2) / 2) *
        ∫ x : Vec d,
          Real.exp (truncatedEuclideanSetDistance K R x ^ 2 /
            (2 * A * (H + σ))) * u.toFun (x, s + H) ^ 2 ≤
      σ ^ (((d : ℝ) + 2) / 2) * (∫ x : Vec d, f x ^ 2) +
        (((d : ℝ) + 2) / 2) *
          Real.exp (2 * ((((d : ℝ) + 2) / 2) /
            (2 * (1 - Lam / A)))) * D := by
  let κ : ℝ := ((d : ℝ) + 2) / 2
  let cE : ℝ := 1 / (2 * A * (H + σ))
  let cS : ℝ := 1 / (2 * A * σ)
  let endpoint : ℕ → ℝ := fun n =>
    ∫ x : Vec d,
      nashPolynomialGaussianWeight (d := d) H K R A σ s n (x, s + H) ^ 2 *
        u.toFun (x, s + H) ^ 2
  let source : ℕ → ℝ := fun n =>
    ∫ x : Vec d,
      nashPolynomialGaussianWeight (d := d) H K R A σ s n (x, s) ^ 2 * f x ^ 2
  have hApos : 0 < A := lt_of_le_of_lt (by linarith) hA
  have hHσ : 0 < H + σ := by linarith
  have hcE : 0 ≤ cE := by dsimp [cE]; positivity
  have hcS : 0 ≤ cS := by dsimp [cS]; positivity
  have hUend : Integrable (fun x : Vec d => u.toFun (x, s + H) ^ 2) volume :=
    PDE.Parabolic.Cauchy.Energy.cauchy_slice_square_integrable
      (by linarith) ha f hf2 u hu ⟨by linarith, le_rfl⟩
  have hFint : Integrable (fun x : Vec d => f x ^ 2) volume := hf2.integrable_sq
  have hFzero : ∀ᵐ x : Vec d ∂volume, x ∉ K → f x ^ 2 = 0 := by
    filter_upwards [hfsupp] with x hx hxK
    simp [hx hxK]
  have hEndWeight := mollifiedTruncatedDistance_weight_integral_tendsto
    hK hR hcE hUend (fun x => sq_nonneg (u.toFun (x, s + H)))
  have hSourceWeight := mollifiedTruncatedDistance_source_integral_tendsto
    hK hR hcS hFint (fun x => sq_nonneg (f x)) hFzero
  have hτE : nashPositiveTimeShift σ ((s + H) - s) = H + σ := by
    rw [show (s + H) - s = H by ring]
    exact nashPositiveTimeShift_eq_add hσ hH.le
  have hτS : nashPositiveTimeShift σ (s - s) = σ := by
    rw [sub_self]
    simpa using nashPositiveTimeShift_eq_add (σ := σ) (t := 0) hσ (by norm_num)
  have hEndEq (n : ℕ) : endpoint n =
      (H + σ) ^ κ *
        ∫ x : Vec d,
          Real.exp (cE * truncatedDistanceMollify K R n x ^ 2) *
            u.toFun (x, s + H) ^ 2 := by
    change (∫ x : Vec d,
      nashPolynomialGaussianWeight (d := d) H K R A σ s n (x, s + H) ^ 2 *
        u.toFun (x, s + H) ^ 2) = _
    have hpoint : ∀ x : Vec d,
        nashPolynomialGaussianWeight (d := d) H K R A σ s n
            (x, s + H) ^ 2 * u.toFun (x, s + H) ^ 2 =
          (H + σ) ^ κ *
            (Real.exp (cE * truncatedDistanceMollify K R n x ^ 2) *
              u.toFun (x, s + H) ^ 2) := by
      intro x
      have hsq := nashPolynomialGaussianWeight_sq_on_forward_slab
        (d := d) (K := K) hH hσ hApos R n (x, s + H)
        (by linarith) le_rfl
      rw [hsq, hτE]
      have hExp : Real.exp
          (truncatedDistanceMollify K R n x ^ 2 / (2 * A * (H + σ))) =
          Real.exp (cE * truncatedDistanceMollify K R n x ^ 2) := by
        congr 1
        dsimp [cE]
        field_simp [ne_of_gt hApos, ne_of_gt hHσ]
      rw [hExp]
      dsimp [κ]
      ring
    calc
      _ = ∫ x : Vec d,
          (H + σ) ^ κ *
            (Real.exp (cE * truncatedDistanceMollify K R n x ^ 2) *
              u.toFun (x, s + H) ^ 2) := by
            apply integral_congr_ae
            exact ae_of_all _ hpoint
      _ = (H + σ) ^ κ *
          ∫ x : Vec d,
            Real.exp (cE * truncatedDistanceMollify K R n x ^ 2) *
              u.toFun (x, s + H) ^ 2 := by rw [integral_const_mul]
  have hSourceEq (n : ℕ) : source n =
      σ ^ κ * ∫ x : Vec d,
        Real.exp (cS * truncatedDistanceMollify K R n x ^ 2) * f x ^ 2 := by
    change (∫ x : Vec d,
      nashPolynomialGaussianWeight (d := d) H K R A σ s n (x, s) ^ 2 * f x ^ 2) = _
    have hpoint : ∀ x : Vec d,
        nashPolynomialGaussianWeight (d := d) H K R A σ s n (x, s) ^ 2 * f x ^ 2 =
          σ ^ κ *
            (Real.exp (cS * truncatedDistanceMollify K R n x ^ 2) * f x ^ 2) := by
      intro x
      have hsq := nashPolynomialGaussianWeight_sq_on_forward_slab
        (d := d) (K := K) hH hσ hApos R n (x, s) le_rfl (by linarith)
      rw [hsq, hτS]
      have hExp : Real.exp
          (truncatedDistanceMollify K R n x ^ 2 / (2 * A * σ)) =
          Real.exp (cS * truncatedDistanceMollify K R n x ^ 2) := by
        congr 1
        dsimp [cS]
        field_simp [ne_of_gt hApos, hσ.ne']
      rw [hExp]
      dsimp [κ]
      ring
    calc
      _ = ∫ x : Vec d,
          σ ^ κ *
            (Real.exp (cS * truncatedDistanceMollify K R n x ^ 2) * f x ^ 2) := by
            apply integral_congr_ae
            exact ae_of_all _ hpoint
      _ = σ ^ κ * ∫ x : Vec d,
          Real.exp (cS * truncatedDistanceMollify K R n x ^ 2) * f x ^ 2 := by
            rw [integral_const_mul]
  have hEndLim : Tendsto endpoint atTop (𝓝 <|
      (H + σ) ^ κ *
        ∫ x : Vec d,
          Real.exp (cE * truncatedEuclideanSetDistance K R x ^ 2) *
            u.toFun (x, s + H) ^ 2) := by
    have h := hEndWeight.const_mul ((H + σ) ^ κ)
    exact h.congr' (Filter.Eventually.of_forall fun n => (hEndEq n).symm)
  have hSourceLim : Tendsto source atTop (𝓝 <|
      σ ^ κ * (∫ x : Vec d, f x ^ 2)) := by
    have h := hSourceWeight.const_mul (σ ^ κ)
    exact h.congr' (Filter.Eventually.of_forall fun n => (hSourceEq n).symm)
  have hFinite (n : ℕ) : endpoint n ≤ source n +
      (((d : ℝ) + 2) / 2) *
        Real.exp (2 * ((((d : ℝ) + 2) / 2) /
          (2 * (1 - Lam / A)))) * D := by
    exact nashPolynomialGaussian_weightedEndpoint_bound
      (d := d) (s := s) hK hH hLam hR hA hσ n ha f hf2 u hu hMomentInt hMomentBound
  have hRhsLim : Tendsto (fun n => source n +
      (((d : ℝ) + 2) / 2) *
        Real.exp (2 * ((((d : ℝ) + 2) / 2) /
          (2 * (1 - Lam / A)))) * D) atTop
      (𝓝 <| σ ^ κ * (∫ x : Vec d, f x ^ 2) +
        (((d : ℝ) + 2) / 2) *
          Real.exp (2 * ((((d : ℝ) + 2) / 2) /
            (2 * (1 - Lam / A)))) * D) := by
    let C : ℝ := (((d : ℝ) + 2) / 2) *
        Real.exp (2 * ((((d : ℝ) + 2) / 2) /
          (2 * (1 - Lam / A)))) * D
    have hconst : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) := tendsto_const_nhds
    simpa [C] using hSourceLim.add hconst
  have hlimIneq := le_of_tendsto_of_tendsto hEndLim hRhsLim
    (Filter.Eventually.of_forall hFinite)
  have htrunc :
      ∫ x : Vec d,
          Real.exp (cE * truncatedEuclideanSetDistance K R x ^ 2) *
            u.toFun (x, s + H) ^ 2 =
        ∫ x : Vec d,
          Real.exp (truncatedEuclideanSetDistance K R x ^ 2 /
            (2 * A * (H + σ))) * u.toFun (x, s + H) ^ 2 := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by dsimp [cE]; congr 2; ring
  rw [htrunc] at hlimIneq
  simpa [κ] using hlimIneq

end PDE.Parabolic.Cauchy.Weights
