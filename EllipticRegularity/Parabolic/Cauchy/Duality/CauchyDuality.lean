module

public import EllipticRegularity.Parabolic.Cauchy.Duality.PairFluxEstimate
public import EllipticRegularity.Parabolic.Cauchy.Duality.PairEndpointLimit
public import EllipticRegularity.Parabolic.Cauchy.Energy.Exhaustion

@[expose] public section

namespace PDE.Parabolic.Duality

open MeasureTheory Set Filter Topology
open PDE.Parabolic.Cauchy.Energy
open PDE.Parabolic.Energy

/-- The whole-space adjoint duality identity, proved by the compact cutoff product rule
and the vanishing mixed-flux tail. -/
theorem cauchyDuality_core (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d)
    (s t : ℝ) (hst : s < t)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s t)) (f g : Vec d → ℝ)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s t))
    (hu : IsCauchySolution a s t f u)
    (w : ParH1Function (univ : Set (Vec d)) (Icc s t))
    (hw : IsCauchySolution (parAdjCoeff a (s + t)) s t g w) :
    Integrable (fun x => g x * u.toFun (x, t)) volume ∧
      Integrable (fun x => f x * w.toFun (x, t)) volume ∧
      ∫ x, g x * u.toFun (x, t) = ∫ x, f x * w.toFun (x, t) := by
  have hpairs := cauchy_duality_endpoint_products_integrable hst ha f g hf hg u hu w hw
  rcases hpairs with ⟨hgu, hfw⟩
  let χ : ℕ → ParCutoff (univ : Set (Vec d)) (Icc s t) :=
    fun n => cauchyExhaustionCutoff s t n
  have hχtime (n : ℕ) (z : Vec d × ℝ) : parTimeDeriv (χ n).toFun z = 0 := by
    dsimp [χ, cauchyExhaustionCutoff]
    exact cauchyParabolicCutoff_timeDeriv_eq_zero s t ((n : ℝ) + 2) (by positivity)
      z.1 z.2
  have hχindep (n : ℕ) (x : Vec d) (τ₁ τ₂ : ℝ) :
      (χ n).toFun (x, τ₁) = (χ n).toFun (x, τ₂) := by
    simp [χ, cauchyExhaustionCutoff, cauchyParabolicCutoff]
  have hloc (n : ℕ) :=
    cauchy_duality_compact_cutoff_identity hst ha f g u w hu hw (χ n) (hχtime n)
  choose K δ0 hKc hδpos hδle hχsupport hlocal using hloc
  let φ : ℕ → Vec d → ℝ := fun n x => (χ n).toFun (x, t)
  have hφcont : ∀ n, Continuous (φ n) := by
    intro n
    exact ((χ n).contDiff.continuous.comp (continuous_id.prodMk continuous_const))
  have hφbound : ∀ n x, |φ n x| ≤ 1 := by
    intro n x
    have hcut := cauchyParabolicCutoff_nonneg_le_one s t ((n : ℝ) + 2) (by positivity)
      (x, t)
    simpa [φ, χ, cauchyExhaustionCutoff] using
      (abs_le.mpr ⟨by linarith [hcut.1], hcut.2⟩)
  have hφtendsto : ∀ x, Tendsto (fun n => φ n x) atTop (𝓝 1) := by
    intro x
    have hev : ∀ᶠ n : ℕ in atTop, φ n x = 1 := by
      simpa [φ, χ] using cauchyExhaustionCutoff_eventually_one s t x t
    exact tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)
  let A : ℕ → ℝ := fun n => ∫ x : Vec d, (φ n x) ^ 2 * (g x * u.toFun (x, t))
  let B : ℕ → ℝ := fun n => ∫ x : Vec d, (φ n x) ^ 2 * (f x * w.toFun (x, t))
  have hA : Tendsto A atTop (𝓝 (∫ x : Vec d, g x * u.toFun (x, t))) := by
    simpa [A] using cauchy_duality_endpoint_cutoff_tendsto hgu φ hφcont hφbound hφtendsto
  have hB : Tendsto B atTop (𝓝 (∫ x : Vec d, f x * w.toFun (x, t))) := by
    simpa [B] using cauchy_duality_endpoint_cutoff_tendsto hfw φ hφcont hφbound hφtendsto
  let err : ℕ → ℝ := fun n =>
    ∫ z in K n ×ˢ Ioc s t,
      2 * (χ n).toFun z * ∑ i : Fin d,
        (flux a u z i * w.toFun (z.1, s + t - z.2) -
          flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z) *
            parSpaceGrad (χ n).toFun z i
  have hfirst (n : ℕ) :
      (∫ x in K n, (χ n).toFun (x, t) ^ 2 * u.toFun (x, t) * w.toFun (x, s)) = A n := by
    let G : Vec d → ℝ := fun x => (χ n).toFun (x, t) ^ 2 * u.toFun (x, t) * w.toFun (x, s)
    let F : Vec d → ℝ := fun x => (φ n x) ^ 2 * (g x * u.toFun (x, t))
    have hpoint : (fun x : Vec d => (K n).indicator G x) =ᵐ[volume] F := by
      filter_upwards [hw.2] with x hx
      by_cases hKx : x ∈ K n
      · simp [G, F, hKx, φ, χ, hx]
        ring
      · have hzero := hχsupport n x t ⟨hst.le, le_rfl⟩ hKx
        change (χ n).toFun (x, t) = 0 at hzero
        simp [G, F, hKx, φ, χ, hzero]
    rw [← integral_indicator (hKc n).measurableSet]
    simpa [G, F, A] using integral_congr_ae hpoint
  have hsecond (n : ℕ) :
      (∫ x in K n, (χ n).toFun (x, s) ^ 2 * u.toFun (x, s) * w.toFun (x, t)) = B n := by
    let G : Vec d → ℝ := fun x => (χ n).toFun (x, s) ^ 2 * u.toFun (x, s) * w.toFun (x, t)
    let F : Vec d → ℝ := fun x => (φ n x) ^ 2 * (f x * w.toFun (x, t))
    have hpoint : (fun x : Vec d => (K n).indicator G x) =ᵐ[volume] F := by
      filter_upwards [hu.2] with x hx
      by_cases hKx : x ∈ K n
      · simp [G, F, hKx, φ, χ, hx]
        rw [hχindep n x s t]
        ring
      · have hzero := hχsupport n x s ⟨le_rfl, hst.le⟩ hKx
        have hzeroT : (χ n).toFun (x, t) = 0 := by
          calc
            (χ n).toFun (x, t) = (χ n).toFun (x, s) := (hχindep n x s t).symm
            _ = 0 := hzero
        change (cauchyExhaustionCutoff s t n).toFun (x, t) = 0 at hzeroT
        simp [G, F, hKx, φ, χ, hzeroT]
    rw [← integral_indicator (hKc n).measurableSet]
    simpa [G, F, B] using integral_congr_ae hpoint
  have hsequence (n : ℕ) : A n - B n = -err n := by
    rw [← hfirst n, ← hsecond n]
    simpa [err] using hlocal n
  let M : Vec d × ℝ → ℝ := cauchyDualityMixedFluxMajorant a u w
  let Ω : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s t
  let C : ℝ := ∫ z in Ω, M z
  have hMint : IntegrableOn M Ω := by
    simpa [M, Ω] using cauchyDualityMixedFluxMajorant_integrable ha u w
  have hMnonneg : ∀ᵐ z ∂(volume.restrict Ω), 0 ≤ M z := by
    filter_upwards [] with z
    exact Finset.sum_nonneg fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hCnonneg : 0 ≤ C := by
    exact integral_nonneg_of_ae hMnonneg
  have hErrBound (n : ℕ) : |err n| ≤ (64 / ((n : ℝ) + 2)) * C := by
    have hχboundN : ∀ z, |(χ n).toFun z| ≤ 1 := by
      intro z
      have hcut := cauchyParabolicCutoff_nonneg_le_one s t ((n : ℝ) + 2) (by positivity) z
      simpa [χ, cauchyExhaustionCutoff] using
        (abs_le.mpr ⟨by linarith [hcut.1], hcut.2⟩)
    have hgradN : ∀ z i, |parSpaceGrad (χ n).toFun z i| ≤ 32 / ((n : ℝ) + 2) := by
      intro z i
      have hcoord := abs_apply_le_vecEuclideanNorm
        (parSpaceGrad (χ n).toFun z) i
      have hnorm := cauchyParabolicCutoff_spatialGrad_bound s t ((n : ℝ) + 2)
        (by positivity) z.1 z.2
      simpa [χ, cauchyExhaustionCutoff] using hcoord.trans hnorm
    have hbound := cauchy_duality_cutoff_flux_integral_bound
      (R := (n : ℝ) + 2) (by positivity) ha u w (χ n) hχboundN hgradN
      (K := K n)
    simpa [err, M, C, Ω] using hbound
  have hscale : Tendsto (fun n : ℕ => (64 / ((n : ℝ) + 2)) * C) atTop (𝓝 0) := by
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hden
    have hrew : (fun n : ℕ => (64 / ((n : ℝ) + 2)) * C) =
        fun n : ℕ => (64 * C) * ((n : ℝ) + 2)⁻¹ := by
      funext n
      field_simp
    rw [hrew]
    simpa using hinv.const_mul (64 * C)
  have herrAbs : Tendsto (fun n : ℕ => |err n|) atTop (𝓝 0) :=
    squeeze_zero (fun n => abs_nonneg (err n)) hErrBound hscale
  have herr : Tendsto err atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Real.norm_eq_abs] using herrAbs
  have hleft := hA.sub hB
  have hleft' : Tendsto (fun n => -err n) atTop
      (𝓝 ((∫ x : Vec d, g x * u.toFun (x, t)) -
        ∫ x : Vec d, f x * w.toFun (x, t))) := by
    have heq : (fun n => A n - B n) =ᶠ[atTop] fun n => -err n :=
      Filter.Eventually.of_forall hsequence
    exact hleft.congr' heq
  have hright : Tendsto (fun n => -err n) atTop (𝓝 0) := by
    simpa only [neg_zero] using herr.neg
  have hmass :
      (∫ x : Vec d, g x * u.toFun (x, t)) -
        ∫ x : Vec d, f x * w.toFun (x, t) = 0 := tendsto_nhds_unique hleft' hright
  exact ⟨hgu, hfw, by linarith⟩

end PDE.Parabolic.Duality
