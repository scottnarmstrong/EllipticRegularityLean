module

public import EllipticRegularity.Parabolic.Cauchy.Lions.MollifiedEnergyData
public import EllipticRegularity.Parabolic.Cauchy.Lions.MollifiedLp
public import PDEFoundation.Measure.LpPower

/-! # Uniform slice estimates for fixed spatial mollifications -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.Lions

/-- The integral of a product of two `L²` functions is bounded by the product of their `L²`
norms. -/
private theorem integral_abs_mul_le_lpNorm
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {F G : α → ℝ}
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    (∫ x, |F x| * |G x| ∂μ) ≤
      (eLpNorm F 2 μ).toReal * (eLpNorm G 2 μ).toReal := by
  let F' : α → ℝ := fun x => |F x|
  let G' : α → ℝ := fun x => |G x|
  have hF' : MemLp F' 2 μ := hF.abs
  have hG' : MemLp G' 2 μ := hG.abs
  have hprod : Integrable (fun x => F' x * G' x) μ := hF'.integrable_mul hG'
  have hinner : (∫ x, F' x * G' x ∂μ) =
      inner ℝ (hF'.toLp F') (hG'.toLp G') := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hF'.coeFn_toLp, hG'.coeFn_toLp] with x hx hy
    rw [hx, hy]
    simp [inner]
    ring
  have hnormF : eLpNorm F' 2 μ = eLpNorm F 2 μ :=
    eLpNorm_congr_norm_ae hF'.aestronglyMeasurable hF.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simp [F'])
  have hnormG : eLpNorm G' 2 μ = eLpNorm G 2 μ :=
    eLpNorm_congr_norm_ae hG'.aestronglyMeasurable hG.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simp [G'])
  rw [hinner]
  calc
    inner ℝ (hF'.toLp F') (hG'.toLp G') ≤
        ‖hF'.toLp F'‖ * ‖hG'.toLp G'‖ := le_abs_self _ |>.trans
          (abs_real_inner_le_norm _ _)
    _ = (eLpNorm F 2 μ).toReal * (eLpNorm G 2 μ).toReal := by
      rw [Lp.norm_toLp, Lp.norm_toLp, hnormF, hnormG]

/-- A bounded scalar weight can be pulled out of an `L²` product estimate. -/
private theorem abs_integral_bounded_weight_mul_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {F G b : α → ℝ}
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ)
    (hb : AEStronglyMeasurable b μ) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᵐ x ∂μ, |b x| ≤ M) :
    |∫ x, b x * F x * G x ∂μ| ≤
      M * (eLpNorm F 2 μ).toReal * (eLpNorm G 2 μ).toReal := by
  have hFG : Integrable (fun x => F x * G x) μ := hF.integrable_mul hG
  have hterm : Integrable (fun x => b x * F x * G x) μ := by
    have hb' : ∀ᵐ x ∂μ, ‖b x‖ ≤ M := by
      filter_upwards [hbound] with x hx
      simpa only [Real.norm_eq_abs] using hx
    have hmul := hFG.bdd_mul hb (c := M) hb'
    refine hmul.congr ?_
    filter_upwards [] with x
    ring
  have hmajor : Integrable (fun x => M * (|F x| * |G x|)) μ := by
    exact (hF.abs.integrable_mul hG.abs).const_mul M
  have hmono : ∫ x, ‖b x * F x * G x‖ ∂μ ≤
      ∫ x, M * (|F x| * |G x|) ∂μ := by
    apply integral_mono_ae hterm.norm hmajor
    filter_upwards [hbound] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc
      |b x| * |F x| * |G x| ≤ M * (|F x| * |G x|) := by
        calc
          |b x| * |F x| * |G x| = |b x| * (|F x| * |G x|) := by ring
          _ ≤ M * (|F x| * |G x|) :=
            mul_le_mul_of_nonneg_right hx (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = M * (|F x| * |G x|) := rfl
  have hnorm := norm_integral_le_integral_norm (μ := μ)
    (fun x => b x * F x * G x)
  calc
    |∫ x, b x * F x * G x ∂μ| =
        ‖∫ x, b x * F x * G x ∂μ‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ x, ‖b x * F x * G x‖ ∂μ := hnorm
    _ ≤ ∫ x, M * (|F x| * |G x|) ∂μ := hmono
    _ = M * ∫ x, |F x| * |G x| ∂μ := by rw [integral_const_mul]
    _ ≤ M * ((eLpNorm F 2 μ).toReal * (eLpNorm G 2 μ).toReal) :=
      mul_le_mul_of_nonneg_left (integral_abs_mul_le_lpNorm hF hG) hM
    _ = M * (eLpNorm F 2 μ).toReal * (eLpNorm G 2 μ).toReal := by ring

/-- The abstract cutoff identity bounds the endpoint slice energy by the initial energy, the
space-time value/gradient products, and a cross term that vanishes as the cutoff radius grows. -/
theorem cauchyEnergyData_cutoff_slice_bound {d : ℕ}
    (D : PDE.Parabolic.Energy.Data d) {R : ℝ} (hR : 0 < R)
    (htime : ∀ z, PDE.parTimeDeriv D.φ z = 0)
    (hphi : ∀ z, |D.φ z| ≤ 1)
    (hcross : ∀ z i, |2 * D.φ z * PDE.parSpaceGrad D.φ z i| ≤ 64 / R) :
    (∫ x in D.K, D.φ (x, D.t) ^ 2 * D.u (x, D.t) ^ 2) ≤
      (∫ x in D.K, D.φ (x, D.s) ^ 2 * D.u (x, D.s) ^ 2) +
        2 * ∑ i : Fin d,
          ((eLpNorm (fun z => D.G z i) 2 D.μP).toReal *
              (eLpNorm (fun z => D.Du z i) 2 D.μP).toReal +
            (64 / R) * (eLpNorm (fun z => D.G z i) 2 D.μP).toReal *
              (eLpNorm D.u 2 D.μP).toReal) := by
  let b : Vec d × ℝ → ℝ := fun z => D.φ z ^ 2
  let c : Fin d → Vec d × ℝ → ℝ := fun i z =>
    2 * D.φ z * PDE.parSpaceGrad D.φ z i
  have hbcont : Continuous b := (D.hφ.continuous).pow 2
  have hccont (i : Fin d) : Continuous (c i) := by
    have hg : Continuous (fun z => PDE.parSpaceGrad D.φ z i) := by
      exact (continuous_apply i).comp (continuous_parSpaceGrad D.hφ)
    exact (continuous_const.mul D.hφ.continuous).mul hg
  have hbmeas : AEStronglyMeasurable b D.μP := hbcont.aestronglyMeasurable
  have hcmeas (i : Fin d) : AEStronglyMeasurable (c i) D.μP := (hccont i).aestronglyMeasurable
  have hbnd : ∀ᵐ z ∂D.μP, |b z| ≤ 1 := by
    filter_upwards [] with z
    dsimp [b]
    have h0 : 0 ≤ |D.φ z| := abs_nonneg _
    have h1 := hphi z
    rw [abs_pow]
    nlinarith [sq_nonneg (1 - |D.φ z|)]
  have hcnd (i : Fin d) : ∀ᵐ z ∂D.μP, |c i z| ≤ 64 / R := by
    filter_upwards [] with z
    exact hcross z i
  have hμ : D.μP ≤ volume.restrict (D.K1 ×ˢ Ioc D.s D.t) := by
    apply Measure.restrict_mono
    · exact prod_mono D.K_subset_K1 (subset_rfl)
    · exact le_rfl
  have hG2 (i : Fin d) : MemLp (fun z => D.G z i) 2 D.μP := by
    exact (D.hG2 i).mono_measure hμ
  have hDu2 (i : Fin d) : MemLp (fun z => D.Du z i) 2 D.μP := by
    exact (D.hDu2 i).mono_measure hμ
  have hu2 : MemLp D.u 2 D.μP := by
    exact D.hu2.mono_measure hμ
  have hterm₁ (i : Fin d) :
      Integrable (fun z => b z * D.G z i * D.Du z i) D.μP := by
    have hprod : Integrable (fun z => D.G z i * D.Du z i) D.μP :=
      (hG2 i).integrable_mul (hDu2 i)
    have hbnd' : ∀ᵐ z ∂D.μP, ‖b z‖ ≤ 1 := by
      filter_upwards [hbnd] with z hz
      simpa only [Real.norm_eq_abs] using hz
    have h := hprod.bdd_mul hbmeas (c := 1) hbnd'
    convert h using 1
    funext z
    dsimp [b]
    ring
  have hterm₂ (i : Fin d) :
      Integrable (fun z => c i z * D.G z i * D.u z) D.μP := by
    have hprod : Integrable (fun z => D.G z i * D.u z) D.μP :=
      (hG2 i).integrable_mul hu2
    have hcnd' : ∀ᵐ z ∂D.μP, ‖c i z‖ ≤ 64 / R := by
      filter_upwards [hcnd i] with z hz
      simpa only [Real.norm_eq_abs] using hz
    have h := hprod.bdd_mul (hcmeas i) (c := 64 / R) hcnd'
    convert h using 1
    funext z
    ring
  have htimeInt :
      (∫ z, D.u z ^ 2 * D.φ z * PDE.parTimeDeriv D.φ z ∂D.μP) = 0 := by
    calc
      (∫ z, D.u z ^ 2 * D.φ z * PDE.parTimeDeriv D.φ z ∂D.μP) =
          ∫ z, (0 : ℝ) ∂D.μP := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun z => by
              change D.u z ^ 2 * D.φ z * PDE.parTimeDeriv D.φ z = 0
              rw [htime z]
              ring
      _ = 0 := by simp
  have hsumInt :
      (∫ z, ∑ i : Fin d,
        D.G z i * (D.φ z ^ 2 * D.Du z i +
          2 * D.φ z * D.u z * PDE.parSpaceGrad D.φ z i) ∂D.μP) =
      ∑ i : Fin d,
        ((∫ z, b z * D.G z i * D.Du z i ∂D.μP) +
          ∫ z, c i z * D.G z i * D.u z ∂D.μP) := by
    calc
      _ = ∫ z, ∑ i : Fin d,
          (b z * D.G z i * D.Du z i + c i z * D.G z i * D.u z) ∂D.μP := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun z => by
              dsimp [b, c]
              congr 1
              ext i
              ring
      _ = ∑ i : Fin d,
          ∫ z, (b z * D.G z i * D.Du z i + c i z * D.G z i * D.u z) ∂D.μP :=
            integral_finsetSum _ fun i _ => (hterm₁ i).add (hterm₂ i)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        exact integral_add (hterm₁ i) (hterm₂ i)
  have hfirst (i : Fin d) :
      |∫ z, b z * D.G z i * D.Du z i ∂D.μP| ≤
        (eLpNorm (fun z => D.G z i) 2 D.μP).toReal *
          (eLpNorm (fun z => D.Du z i) 2 D.μP).toReal := by
    have h := abs_integral_bounded_weight_mul_le (hG2 i) (hDu2 i) hbmeas
      (M := 1) (by norm_num) hbnd
    simpa only [b, one_mul] using h
  have hsecond (i : Fin d) :
      |∫ z, c i z * D.G z i * D.u z ∂D.μP| ≤
        (64 / R) * (eLpNorm (fun z => D.G z i) 2 D.μP).toReal *
          (eLpNorm D.u 2 D.μP).toReal :=
    by
      have h := abs_integral_bounded_weight_mul_le (hG2 i) hu2 (hcmeas i)
        (M := 64 / R) (by positivity) (hcnd i)
      exact h
  have hIntAbs :
      |∫ z, ∑ i : Fin d,
        D.G z i * (D.φ z ^ 2 * D.Du z i +
          2 * D.φ z * D.u z * PDE.parSpaceGrad D.φ z i) ∂D.μP| ≤
      ∑ i : Fin d,
        ((eLpNorm (fun z => D.G z i) 2 D.μP).toReal *
            (eLpNorm (fun z => D.Du z i) 2 D.μP).toReal +
          (64 / R) * (eLpNorm (fun z => D.G z i) 2 D.μP).toReal *
            (eLpNorm D.u 2 D.μP).toReal) := by
    rw [hsumInt]
    calc
      |∑ i : Fin d,
          ((∫ z, b z * D.G z i * D.Du z i ∂D.μP) +
            ∫ z, c i z * D.G z i * D.u z ∂D.μP)| ≤
        ∑ i : Fin d,
          |(∫ z, b z * D.G z i * D.Du z i ∂D.μP) +
            ∫ z, c i z * D.G z i * D.u z ∂D.μP| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin d,
          (|(∫ z, b z * D.G z i * D.Du z i ∂D.μP)| +
            |∫ z, c i z * D.G z i * D.u z ∂D.μP|) := by
          apply Finset.sum_le_sum
          intro i hi
          exact abs_add_le _ _
      _ ≤ ∑ i : Fin d,
          ((eLpNorm (fun z => D.G z i) 2 D.μP).toReal *
              (eLpNorm (fun z => D.Du z i) 2 D.μP).toReal +
            (64 / R) * (eLpNorm (fun z => D.G z i) 2 D.μP).toReal *
              (eLpNorm D.u 2 D.μP).toReal) := by
          apply Finset.sum_le_sum
          intro i hi
          exact add_le_add (hfirst i) (hsecond i)
  have hid := D.energy_identity
  rw [htimeInt] at hid
  have hlow :
      - (∑ i : Fin d,
        ((eLpNorm (fun z => D.G z i) 2 D.μP).toReal *
            (eLpNorm (fun z => D.Du z i) 2 D.μP).toReal +
          (64 / R) * (eLpNorm (fun z => D.G z i) 2 D.μP).toReal *
            (eLpNorm D.u 2 D.μP).toReal)) ≤
      (∫ z, ∑ i : Fin d,
        D.G z i * (D.φ z ^ 2 * D.Du z i +
          2 * D.φ z * D.u z * PDE.parSpaceGrad D.φ z i) ∂D.μP) :=
    (abs_le.mp hIntAbs).1
  nlinarith [hid, hlow]

end PDE.Parabolic.Lions
