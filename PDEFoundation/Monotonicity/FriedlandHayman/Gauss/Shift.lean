module

public import PDEFoundation.Monotonicity.FriedlandHayman.Gauss.GroundInt

/-!
# Friedland--Hayman: the shift bounds for `β`

Translating the ground state `ψ_τ` by `δ` and multiplying by `exp ((2 s δ - δ²)/4)` gives an
admissible test function on `(τ + δ, ∞)` whose Gaussian Rayleigh quotient is
`β(τ) + δ M(τ)/2 + δ²/4`.  Barta's inequality yields
`gaussBeta (τ + δ) ≤ gaussBeta τ + δ * gaussMean τ / 2 + δ ^ 2 / 4`.
-/

@[expose] public section

open Set MeasureTheory Filter Topology

namespace PDE.FHLane

noncomputable section

namespace BKP

theorem integral_Ioi_comp_sub (f : ℝ → ℝ) (a δ : ℝ) :
    ∫ s in Ioi (a + δ), f (s - δ) = ∫ s in Ioi a, f s := by
  have h1 : ∫ s in Ioi (a + δ), f (s - δ) =
      ∫ s in Ioi (a + δ), (Ioi a).indicator f (s - δ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have : s - δ ∈ Ioi a := by
      simp only [mem_Ioi] at hs ⊢
      linarith
    rw [indicator_of_mem this]
  have h2 : ∫ s in Ioi (a + δ), (Ioi a).indicator f (s - δ) =
      ∫ s, (Ioi a).indicator f (s - δ) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => ?_
    have : s - δ ∉ Ioi a := by
      simp only [mem_Ioi, not_lt] at hs ⊢
      linarith
    rw [indicator_of_notMem this]
  rw [h1, h2, integral_sub_right_eq_self (fun s => (Ioi a).indicator f s) δ,
    integral_indicator measurableSet_Ioi]

theorem integrableOn_Ioi_comp_sub {f : ℝ → ℝ} {a : ℝ} (h : IntegrableOn f (Ioi a)) (δ : ℝ) :
    IntegrableOn (fun s => f (s - δ)) (Ioi (a + δ)) := by
  have h1 : Integrable fun s => (Ioi a).indicator f (s - δ) :=
    ((integrable_indicator_iff measurableSet_Ioi).2 h).comp_sub_right δ
  refine h1.integrableOn.congr_fun (fun s hs => ?_) measurableSet_Ioi
  have : s - δ ∈ Ioi a := by
    simp only [mem_Ioi] at hs ⊢
    linarith
  simp only [indicator_of_mem this]

/-- The multiplier `exp ((2 s δ - δ²)/4)`. -/
def shiftE (δ s : ℝ) : ℝ := Real.exp ((2 * s * δ - δ ^ 2) / 4)

theorem shiftE_sq_mul (δ s : ℝ) : shiftE δ s ^ 2 * gaussW s = gaussW (s - δ) := by
  unfold shiftE gaussW
  rw [sq, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem hasDerivAt_shiftE (δ s : ℝ) : HasDerivAt (shiftE δ) (shiftE δ s * (δ / 2)) s := by
  have h : HasDerivAt (fun s : ℝ => (2 * s * δ - δ ^ 2) / 4) (δ / 2) s := by
    have := ((((hasDerivAt_id s).const_mul 2).mul_const δ).sub_const (δ ^ 2)).div_const 4
    refine this.congr_deriv ?_
    simp
    ring
  exact h.exp

theorem continuous_shiftE (δ : ℝ) : Continuous (shiftE δ) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_shiftE δ s).continuousAt

/-- The shifted test function. -/
def shiftG (τ δ s : ℝ) : ℝ := if s ≤ τ + δ then 0 else gpsi τ (s - δ) * shiftE δ s

/-- Its derivative on `(τ + δ, ∞)`. -/
def shiftG' (τ δ s : ℝ) : ℝ := (gdpsi τ (s - δ) + δ / 2 * gpsi τ (s - δ)) * shiftE δ s

/-- The expanded Rayleigh numerator density. -/
def shiftH (τ δ s : ℝ) : ℝ :=
  gdpsi τ s ^ 2 * gaussW s + δ * (gpsi τ s * gdpsi τ s * gaussW s) +
    δ ^ 2 / 4 * (gpsi τ s ^ 2 * gaussW s)

theorem shiftG_sq_mul (τ δ s : ℝ) : shiftG τ δ s ^ 2 * gaussW s =
    (Ioi τ).indicator (fun s => gpsi τ s ^ 2 * gaussW s) (s - δ) := by
  by_cases h : s ≤ τ + δ
  · have : s - δ ∉ Ioi τ := by
      simp only [mem_Ioi, not_lt]
      linarith
    simp [shiftG, h]
  · have : s - δ ∈ Ioi τ := by
      simp only [mem_Ioi]
      linarith
    rw [indicator_of_mem this]
    simp only [shiftG, h, ite_false]
    rw [mul_pow, mul_assoc, shiftE_sq_mul]

theorem shiftG'_sq_mul (τ δ s : ℝ) : shiftG' τ δ s ^ 2 * gaussW s = shiftH τ δ (s - δ) := by
  unfold shiftG' shiftH
  rw [mul_pow, mul_assoc, shiftE_sq_mul]
  ring

theorem continuous_shiftG' (τ δ : ℝ) : Continuous (shiftG' τ δ) := by
  unfold shiftG'
  have h1 : Continuous fun s => gdpsi τ (s - δ) :=
    (continuous_ouSolDeriv _ τ).comp (continuous_sub_right δ)
  have h2 : Continuous fun s => gpsi τ (s - δ) :=
    (continuous_ouSol _ τ).comp (continuous_sub_right δ)
  exact (h1.add (continuous_const.mul h2)).mul (continuous_shiftE δ)

theorem integrableOn_shiftH (τ δ a : ℝ) : IntegrableOn (shiftH τ δ) (Ioi a) :=
  (((integrableOn_gdpsi_sq τ a).add ((integrableOn_gpsi_gdpsi τ a).const_mul δ)).add
    ((integrableOn_gpsi_sq τ a).const_mul (δ ^ 2 / 4)))

theorem gaussTest_shift (τ δ : ℝ) : GaussTest (τ + δ) (shiftG τ δ) (shiftG' τ δ) where
  cont := by
    have h : Continuous fun s => gpsi τ (s - δ) * shiftE δ s :=
      ((continuous_ouSol _ τ).comp (continuous_sub_right δ)).mul (continuous_shiftE δ)
    exact Continuous.if_le (f := fun s => s) (g := fun _ => τ + δ)
      (f' := fun _ => (0 : ℝ)) (g' := fun s => gpsi τ (s - δ) * shiftE δ s)
      continuous_const h continuous_id continuous_const
      (fun x hx => by
        have hx' : x = τ + δ := hx
        subst hx'
        simp [ouSol_self])
  eq_zero s hs := by simp [shiftG, hs]
  hasDeriv s hs := by
    have hd : HasDerivAt (fun s => gpsi τ (s - δ) * shiftE δ s) (shiftG' τ δ s) s := by
      have := ((hasDerivAt_ouSol (gaussBeta τ) τ (s - δ)).comp_sub_const s δ).mul
        (hasDerivAt_shiftE δ s)
      refine this.congr_deriv ?_
      unfold shiftG'
      ring
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hs] with x hx
    have : ¬ x ≤ τ + δ := not_le.mpr hx
    simp [shiftG, this]
  cont' := (continuous_shiftG' τ δ).continuousOn
  int_sq := by
    have h : Integrable fun s => (Ioi τ).indicator (fun s => gpsi τ s ^ 2 * gaussW s) (s - δ) :=
      ((integrable_indicator_iff measurableSet_Ioi).2 (integrableOn_gpsi_sq τ τ)).comp_sub_right δ
    exact h.congr (Filter.Eventually.of_forall fun s => (shiftG_sq_mul τ δ s).symm)
  int_dsq := by
    have := integrableOn_Ioi_comp_sub (integrableOn_shiftH τ δ τ) δ
    exact this.congr_fun (fun s _ => (shiftG'_sq_mul τ δ s).symm) measurableSet_Ioi

theorem shift_integral_sq (τ δ : ℝ) :
    ∫ s, shiftG τ δ s ^ 2 * gaussW s = ∫ s in Ioi τ, gpsi τ s ^ 2 * gaussW s := by
  simp_rw [shiftG_sq_mul]
  rw [integral_sub_right_eq_self (fun s => (Ioi τ).indicator (fun s => gpsi τ s ^ 2 * gaussW s) s) δ,
    integral_indicator measurableSet_Ioi]

theorem shift_integral_dsq (τ δ : ℝ) :
    ∫ s in Ioi (τ + δ), shiftG' τ δ s ^ 2 * gaussW s =
      (∫ s in Ioi τ, gdpsi τ s ^ 2 * gaussW s) +
        δ * (∫ s in Ioi τ, gpsi τ s * gdpsi τ s * gaussW s) +
        δ ^ 2 / 4 * ∫ s in Ioi τ, gpsi τ s ^ 2 * gaussW s := by
  simp_rw [shiftG'_sq_mul]
  rw [integral_Ioi_comp_sub (shiftH τ δ) τ δ]
  unfold shiftH
  have i1 := integrableOn_gdpsi_sq τ τ
  have i2 : IntegrableOn (fun s => δ * (gpsi τ s * gdpsi τ s * gaussW s)) (Ioi τ) :=
    (integrableOn_gpsi_gdpsi τ τ).const_mul δ
  have i3 : IntegrableOn (fun s => δ ^ 2 / 4 * (gpsi τ s ^ 2 * gaussW s)) (Ioi τ) :=
    (integrableOn_gpsi_sq τ τ).const_mul (δ ^ 2 / 4)
  have i12 : IntegrableOn (fun s => gdpsi τ s ^ 2 * gaussW s +
      δ * (gpsi τ s * gdpsi τ s * gaussW s)) (Ioi τ) := i1.add i2
  rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul]

end BKP

open BKP

theorem gaussBeta_shift (τ δ : ℝ) :
    gaussBeta (τ + δ) ≤ gaussBeta τ + δ * gaussMean τ / 2 + δ ^ 2 / 4 := by
  have hb := gaussBeta_barta (gaussTest_shift τ δ)
  rw [shift_integral_sq, shift_integral_dsq, ground_energy] at hb
  have hI := ground_integral_pos τ
  have hm := gaussMean_mul τ
  have hi := ground_ibp τ
  refine le_of_mul_le_mul_right ?_ hI
  have e : (gaussBeta τ + δ * gaussMean τ / 2 + δ ^ 2 / 4) *
      (∫ s in Ioi τ, ouSol (gaussBeta τ) τ s ^ 2 * gaussW s) =
      gaussBeta τ * (∫ s in Ioi τ, ouSol (gaussBeta τ) τ s ^ 2 * gaussW s) +
        δ * (∫ s in Ioi τ, ouSol (gaussBeta τ) τ s * ouSolDeriv (gaussBeta τ) τ s * gaussW s) +
        δ ^ 2 / 4 * ∫ s in Ioi τ, ouSol (gaussBeta τ) τ s ^ 2 * gaussW s := by
    have : ∫ s in Ioi τ, ouSol (gaussBeta τ) τ s * ouSolDeriv (gaussBeta τ) τ s * gaussW s =
        gaussMean τ * (∫ s in Ioi τ, ouSol (gaussBeta τ) τ s ^ 2 * gaussW s) / 2 := by
      linarith
    rw [this]
    ring
  rw [e]
  exact hb

theorem gaussBeta_shift_upper {τ₁ τ₂ : ℝ} (_h : τ₁ ≤ τ₂) :
    gaussBeta τ₂ ≤ gaussBeta τ₁ + (τ₂ - τ₁) * gaussMean τ₁ / 2 + (τ₂ - τ₁) ^ 2 / 4 := by
  have := gaussBeta_shift τ₁ (τ₂ - τ₁)
  rwa [add_sub_cancel] at this

theorem gaussBeta_shift_lower {τ₁ τ₂ : ℝ} (_h : τ₁ ≤ τ₂) :
    gaussBeta τ₁ ≤ gaussBeta τ₂ - (τ₂ - τ₁) * gaussMean τ₂ / 2 + (τ₂ - τ₁) ^ 2 / 4 := by
  have := gaussBeta_shift τ₂ (-(τ₂ - τ₁))
  rw [show τ₂ + -(τ₂ - τ₁) = τ₁ by ring] at this
  linarith

end

end PDE.FHLane
