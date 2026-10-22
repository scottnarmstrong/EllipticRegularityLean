module

public import PDEFoundation.Monotonicity.FriedlandHayman.Gauss.Barta

/-!
# Friedland--Hayman: the Gaussian half-line Dirichlet eigenvalue `β(τ)`

`gaussBeta τ` is the supremum of the admissible parameters at `τ`.  We prove that it is finite
(Barta's inequality with a ramp test function), nonnegative, monotone in `τ`, bounded above by
the Rayleigh quotient of every test function, and `gaussBeta 0 = 1`.
-/

@[expose] public section

open Set MeasureTheory Filter Topology

namespace PDE.FHLane

noncomputable section

/-- Gaussian half-line Dirichlet eigenvalue `β(τ)`. -/
def gaussBeta (τ : ℝ) : ℝ := sSup {c | OUAdmissible τ c}

/-- The ramp `max (s - τ) 0` is an admissible test function with derivative `1`. -/
theorem gaussTest_ramp (τ : ℝ) : GaussTest τ (fun s => max (s - τ) 0) (fun _ => 1) where
  cont := by fun_prop
  eq_zero s hs := max_eq_right (by linarith)
  hasDeriv s hs := by
    have h : HasDerivAt (fun s : ℝ => s - τ) 1 s := (hasDerivAt_id s).sub_const τ
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hs] with x hx
    exact max_eq_left (by simp only [mem_Ioi] at hx; linarith)
  cont' := continuousOn_const
  int_sq := by
    refine ((integrable_exp_quarter.const_mul (8 + 2 * τ ^ 2))).mono'
      (by exact ((by fun_prop : Continuous fun s : ℝ => max (s - τ) 0 ^ 2).mul
        continuous_gaussW).aestronglyMeasurable) (Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (gaussW_pos s).le)]
    have h1 : max (s - τ) 0 ^ 2 ≤ 2 * s ^ 2 + 2 * τ ^ 2 := by
      rcases max_cases (s - τ) 0 with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]; nlinarith [sq_nonneg (s + τ)]
      · rw [h]; nlinarith [sq_nonneg τ, sq_nonneg s]
    have h2 := sq_mul_gaussW_le s
    have h3 := gaussW_le_exp_quarter s
    have h4 : 0 ≤ τ ^ 2 := sq_nonneg τ
    calc max (s - τ) 0 ^ 2 * gaussW s ≤ (2 * s ^ 2 + 2 * τ ^ 2) * gaussW s :=
          mul_le_mul_of_nonneg_right h1 (gaussW_pos s).le
      _ = 2 * (s ^ 2 * gaussW s) + 2 * τ ^ 2 * gaussW s := by ring
      _ ≤ 2 * (4 * Real.exp (-(1 / 4) * s ^ 2)) + 2 * τ ^ 2 * Real.exp (-(1 / 4) * s ^ 2) := by
          gcongr
      _ = (8 + 2 * τ ^ 2) * Real.exp (-(1 / 4) * s ^ 2) := by ring
  int_dsq := by
    simpa using integrable_gaussW.integrableOn

theorem integral_ramp_pos (τ : ℝ) : 0 < ∫ s, max (s - τ) 0 ^ 2 * gaussW s := by
  have hint := (gaussTest_ramp τ).int_sq
  have hnn : 0 ≤ fun s : ℝ => max (s - τ) 0 ^ 2 * gaussW s :=
    fun s => mul_nonneg (sq_nonneg _) (gaussW_pos s).le
  rw [integral_pos_iff_support_of_nonneg hnn hint]
  have hcont : Continuous fun s : ℝ => max (s - τ) 0 ^ 2 * gaussW s :=
    (by fun_prop : Continuous fun s : ℝ => max (s - τ) 0 ^ 2).mul continuous_gaussW
  have hopen : IsOpen (Function.support fun s : ℝ => max (s - τ) 0 ^ 2 * gaussW s) :=
    hcont.isOpen_support
  refine hopen.measure_pos volume ⟨τ + 1, ?_⟩
  simp only [Function.mem_support]
  have : max (τ + 1 - τ) 0 = 1 := by simp
  rw [this]
  simpa using (gaussW_pos _).ne'

theorem integral_ramp_dsq_nonneg (τ : ℝ) : 0 ≤ ∫ s in Ioi τ, (1 : ℝ) ^ 2 * gaussW s :=
  setIntegral_nonneg measurableSet_Ioi fun s _ => by simpa using (gaussW_pos s).le

theorem ouAdmissible_zero (τ : ℝ) : OUAdmissible τ 0 := by
  refine ⟨le_rfl, ?_⟩
  have hd : ∀ x, HasDerivAt (fun x => ouSolDeriv 0 τ x * gaussW x) 0 x := by
    intro x
    have := (hasDerivAt_ouSolDeriv 0 τ x).mul (hasDerivAt_gaussW x)
    convert this using 1
    ring
  have hconst : ∀ s, ouSolDeriv 0 τ s * gaussW s = ouSolDeriv 0 τ τ * gaussW τ := fun s =>
    is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) s τ
  have hD : ∀ s, 0 < ouSolDeriv 0 τ s := by
    intro s
    have h := hconst s
    rw [ouSolDeriv_self, one_mul] at h
    have := gaussW_pos s
    have := gaussW_pos τ
    by_contra hneg
    push Not at hneg
    nlinarith
  have hmono : StrictMono (ouSol 0 τ) :=
    strictMono_of_deriv_pos fun x => by rw [(hasDerivAt_ouSol 0 τ x).deriv]; exact hD x
  intro s hs
  have := hmono hs
  rwa [ouSol_self] at this

theorem bddAbove_ouAdmissible (τ : ℝ) : BddAbove {c | OUAdmissible τ c} := by
  refine ⟨(∫ s in Ioi τ, (1 : ℝ) ^ 2 * gaussW s) / ∫ s, max (s - τ) 0 ^ 2 * gaussW s,
    fun c hc => ?_⟩
  rw [le_div_iff₀ (integral_ramp_pos τ)]
  exact barta hc (gaussTest_ramp τ)

theorem ouAdmissible_nonempty (τ : ℝ) : ({c | OUAdmissible τ c} : Set ℝ).Nonempty :=
  ⟨0, ouAdmissible_zero τ⟩

theorem gaussBeta_nonneg (τ : ℝ) : 0 ≤ gaussBeta τ :=
  le_csSup (bddAbove_ouAdmissible τ) (ouAdmissible_zero τ)

theorem gaussBeta_barta {τ : ℝ} {g g' : ℝ → ℝ} (hg : GaussTest τ g g') :
    gaussBeta τ * ∫ s, g s ^ 2 * gaussW s ≤ ∫ s in Set.Ioi τ, g' s ^ 2 * gaussW s := by
  have hA : 0 ≤ ∫ s, g s ^ 2 * gaussW s :=
    integral_nonneg fun s => mul_nonneg (sq_nonneg _) (gaussW_pos s).le
  have hB : 0 ≤ ∫ s in Set.Ioi τ, g' s ^ 2 * gaussW s :=
    setIntegral_nonneg measurableSet_Ioi fun s _ => mul_nonneg (sq_nonneg _) (gaussW_pos s).le
  rcases hA.eq_or_lt with h0 | hpos
  · rw [← h0]; simpa using hB
  · rw [← le_div_iff₀ hpos]
    refine csSup_le (ouAdmissible_nonempty τ) fun c hc => ?_
    rw [le_div_iff₀ hpos]
    exact barta hc hg

theorem ouAdmissible_mono {τ₁ τ₂ c : ℝ} (h : τ₁ ≤ τ₂) (hc : OUAdmissible τ₁ c) :
    OUAdmissible τ₂ c :=
  ⟨hc.1, ouSol_pos_of_le h hc.2⟩

theorem gaussBeta_mono : Monotone gaussBeta := fun _ _ h =>
  csSup_le_csSup (bddAbove_ouAdmissible _) (ouAdmissible_nonempty _)
    fun _ hc => ouAdmissible_mono h hc

theorem le_gaussBeta {τ c : ℝ} (hc : OUAdmissible τ c) : c ≤ gaussBeta τ :=
  le_csSup (bddAbove_ouAdmissible τ) hc

/-- `ouSol 1 0 s = s`. -/
theorem ouSol_one_zero (s : ℝ) : ouSol 1 0 s = s := by
  have hy : ∀ s, HasDerivAt (fun s => ouSol 1 0 s - s) (ouSolDeriv 1 0 s - 1) s := fun s =>
    (hasDerivAt_ouSol 1 0 s).sub (hasDerivAt_id s)
  have hy' : ∀ s, HasDerivAt (fun s => ouSolDeriv 1 0 s - 1)
      (s * (ouSolDeriv 1 0 s - 1) - 1 * (ouSol 1 0 s - s)) s := by
    intro s
    have := (hasDerivAt_ouSolDeriv 1 0 s).sub_const 1
    convert this using 1
    ring
  have := ou_unique (c := 1) (a := 0) (y := fun s => ouSol 1 0 s - s)
    (y' := fun s => ouSolDeriv 1 0 s - 1) hy hy' (by simp [ouSol_self])
    (by simp [ouSolDeriv_self]) s
  linarith

theorem ouAdmissible_one_zero : OUAdmissible 0 1 :=
  ⟨zero_le_one, fun s hs => by rw [ouSol_one_zero]; exact hs⟩

theorem mul_gaussW_le (s : ℝ) : s * gaussW s ≤ Real.exp (-(1 / 4) * s ^ 2) := by
  have h1 : s ≤ Real.exp (s ^ 2 / 4) := by
    have := Real.add_one_le_exp (s ^ 2 / 4)
    nlinarith [sq_nonneg (s / 2 - 1)]
  have h2 : gaussW s = Real.exp (-(1 / 4) * s ^ 2) * Real.exp (-(1 / 4) * s ^ 2) := by
    unfold gaussW
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : Real.exp (s ^ 2 / 4) * Real.exp (-(1 / 4) * s ^ 2) = 1 := by
    rw [← Real.exp_add]
    rw [show s ^ 2 / 4 + -(1 / 4) * s ^ 2 = 0 by ring, Real.exp_zero]
  have h4 : 0 < Real.exp (-(1 / 4) * s ^ 2) := Real.exp_pos _
  calc s * gaussW s = s * Real.exp (-(1 / 4) * s ^ 2) * Real.exp (-(1 / 4) * s ^ 2) := by
        rw [h2]; ring
    _ ≤ Real.exp (s ^ 2 / 4) * Real.exp (-(1 / 4) * s ^ 2) * Real.exp (-(1 / 4) * s ^ 2) := by
        gcongr
    _ = Real.exp (-(1 / 4) * s ^ 2) := by rw [h3, one_mul]

theorem tendsto_mul_gaussW : Tendsto (fun s => s * gaussW s) atTop (𝓝 0) := by
  have hexp : Tendsto (fun s : ℝ => Real.exp (-(1 / 4) * s ^ 2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (Filter.Tendsto.const_mul_atTop_of_neg (by norm_num) (tendsto_pow_atTop two_ne_zero))
  refine squeeze_zero' ?_ ?_ hexp
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    exact mul_nonneg hs (gaussW_pos s).le
  · exact Eventually.of_forall mul_gaussW_le

/-- Integration by parts: `∫_0^∞ s² w = ∫_0^∞ w`. -/
theorem integral_Ioi_sq_mul_gaussW :
    ∫ s in Ioi (0 : ℝ), s ^ 2 * gaussW s = ∫ s in Ioi (0 : ℝ), gaussW s := by
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun s => s * gaussW s)
      (gaussW x - x ^ 2 * gaussW x) x := by
    intro x _
    have : HasDerivAt (fun s => s * gaussW s) (1 * gaussW x + x * (-x * gaussW x)) x :=
      (hasDerivAt_id' x).mul (hasDerivAt_gaussW x)
    convert this using 1
    ring
  have hint : IntegrableOn (fun s => gaussW s - s ^ 2 * gaussW s) (Ioi 0) :=
    (integrable_gaussW.sub integrable_sq_mul_gaussW).integrableOn
  have := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun s => s * gaussW s) (f' := fun s => gaussW s - s ^ 2 * gaussW s) (a := 0) (m := 0)
    (continuous_id.mul continuous_gaussW).continuousWithinAt hd hint tendsto_mul_gaussW
  rw [integral_sub integrable_gaussW.integrableOn integrable_sq_mul_gaussW.integrableOn] at this
  simp at this
  linarith

theorem gaussBeta_zero : gaussBeta 0 = 1 := by
  refine le_antisymm ?_ (le_gaussBeta ouAdmissible_one_zero)
  have hb := gaussBeta_barta (gaussTest_ramp 0)
  have hA : ∫ s, max (s - 0) 0 ^ 2 * gaussW s = ∫ s in Ioi (0 : ℝ), s ^ 2 * gaussW s := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ))]
    · refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
      simp only [sub_zero]
      rw [max_eq_left (le_of_lt hs)]
    · intro x hx
      have : x ≤ 0 := not_lt.mp hx
      simp [max_eq_right this]
  have hpos := integral_ramp_pos 0
  simp only [one_pow, one_mul] at hb
  rw [hA, integral_Ioi_sq_mul_gaussW] at hb hpos
  have := (mul_le_iff_le_one_left hpos).mp hb
  exact this

end

end PDE.FHLane
