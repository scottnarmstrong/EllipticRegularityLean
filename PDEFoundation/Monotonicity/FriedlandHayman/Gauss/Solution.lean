module

public import PDEFoundation.Monotonicity.FriedlandHayman.Gauss.Series
public import PDEFoundation.Monotonicity.FriedlandHayman.Gauss.Uniqueness

/-!
# Friedland--Hayman: the Hermite initial value problem

For every `c`, `τ` there is a solution `ouSol c τ` of `y'' - s y' + c y = 0` on all of `ℝ` with
`y τ = 0`, `y' τ = 1`, jointly continuous in `(c, s)` (together with its derivative `ouSolDeriv`).
It is built from the even and odd power series solutions `E`, `O` (with `E 0 = 1`, `E' 0 = 0`,
`O 0 = 0`, `O' 0 = 1`) and the Wronskian identity `E O' - E' O = exp (s² / 2)`:
`ouSol c τ s = exp (-τ²/2) (E τ O s - O τ E s)`.
-/

@[expose] public section

namespace PDE.FHLane

noncomputable section

/-- The power series solution with `y 0 = a₀`, `y' 0 = a₁`. -/
def ouY (c a₀ a₁ s : ℝ) : ℝ := ouSer (ouCoef c a₀ a₁) s

/-- The derivative of `ouY`. -/
def ouY' (c a₀ a₁ s : ℝ) : ℝ := ouSer (ouD (ouCoef c a₀ a₁)) s

theorem ouEntire_ouCoef (c a₀ a₁ : ℝ) : OuEntire (ouCoef c a₀ a₁) :=
  (ouUEntire_ouCoef a₀ a₁).entire c

theorem hasDerivAt_ouY (c a₀ a₁ s : ℝ) : HasDerivAt (ouY c a₀ a₁) (ouY' c a₀ a₁ s) s :=
  hasDerivAt_ouSer (ouEntire_ouCoef c a₀ a₁) s

theorem hasDerivAt_ouY' (c a₀ a₁ s : ℝ) :
    HasDerivAt (ouY' c a₀ a₁) (s * ouY' c a₀ a₁ s - c * ouY c a₀ a₁ s) s := by
  have h := hasDerivAt_ouSer (ouEntire_ouCoef c a₀ a₁).D s
  rw [ouSer_ouD_ouD (ouEntire_ouCoef c a₀ a₁) (ouD_ouD_ouCoef c a₀ a₁) s] at h
  exact h

theorem ouSer_zero (b : ℕ → ℝ) : ouSer b 0 = b 0 := by
  unfold ouSer
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

theorem ouY_zero (c a₀ a₁ : ℝ) : ouY c a₀ a₁ 0 = a₀ := by
  simp [ouY, ouSer_zero, ouCoef]

theorem ouY'_zero (c a₀ a₁ : ℝ) : ouY' c a₀ a₁ 0 = a₁ := by
  simp [ouY', ouSer_zero, ouD, ouCoef]

theorem continuous_ouY_uncurry (a₀ a₁ : ℝ) :
    Continuous fun p : ℝ × ℝ => ouY p.1 a₀ a₁ p.2 :=
  continuous_ouSer_uncurry (ouUEntire_ouCoef a₀ a₁) (continuous_ouCoef a₀ a₁)

theorem continuous_ouY'_uncurry (a₀ a₁ : ℝ) :
    Continuous fun p : ℝ × ℝ => ouY' p.1 a₀ a₁ p.2 :=
  continuous_ouSer_uncurry (ouUEntire_ouCoef a₀ a₁).D fun n =>
    (continuous_const.add continuous_const).mul (continuous_ouCoef a₀ a₁ (n + 1))

/-- The Wronskian of the even and odd series solutions. -/
theorem ou_wronskian_series (c s : ℝ) :
    (ouY' c 0 1 s * ouY c 1 0 s - ouY c 0 1 s * ouY' c 1 0 s) * Real.exp (-(s ^ 2) / 2) = 1 := by
  have hd := fun x => hasDerivAt_ouWronskian (c₁ := c) (c₂ := c)
    (hasDerivAt_ouY c 1 0) (hasDerivAt_ouY' c 1 0) (hasDerivAt_ouY c 0 1) (hasDerivAt_ouY' c 0 1) x
  have hconst := is_const_of_deriv_eq_zero (f := fun s => (ouY' c 0 1 s * ouY c 1 0 s
      - ouY c 0 1 s * ouY' c 1 0 s) * Real.exp (-(s ^ 2) / 2))
    (fun x => (hd x).differentiableAt) (fun x => by rw [(hd x).deriv]; ring) s 0
  rw [hconst]
  simp [ouY_zero, ouY'_zero]

/-- Value of the IVP solution `y'' - s y' + c y = 0`, `y τ = 0`, `y' τ = 1`. -/
def ouSol (c τ s : ℝ) : ℝ :=
  Real.exp (-(τ ^ 2) / 2) * (ouY c 1 0 τ * ouY c 0 1 s - ouY c 0 1 τ * ouY c 1 0 s)

/-- Its derivative in `s`. -/
def ouSolDeriv (c τ s : ℝ) : ℝ :=
  Real.exp (-(τ ^ 2) / 2) * (ouY c 1 0 τ * ouY' c 0 1 s - ouY c 0 1 τ * ouY' c 1 0 s)

theorem hasDerivAt_ouSol (c τ s : ℝ) : HasDerivAt (ouSol c τ) (ouSolDeriv c τ s) s := by
  have := (((hasDerivAt_ouY c 0 1 s).const_mul (ouY c 1 0 τ)).sub
    ((hasDerivAt_ouY c 1 0 s).const_mul (ouY c 0 1 τ))).const_mul (Real.exp (-(τ ^ 2) / 2))
  exact this

theorem hasDerivAt_ouSolDeriv (c τ s : ℝ) :
    HasDerivAt (ouSolDeriv c τ) (s * ouSolDeriv c τ s - c * ouSol c τ s) s := by
  have := (((hasDerivAt_ouY' c 0 1 s).const_mul (ouY c 1 0 τ)).sub
    ((hasDerivAt_ouY' c 1 0 s).const_mul (ouY c 0 1 τ))).const_mul (Real.exp (-(τ ^ 2) / 2))
  convert this using 1
  · rfl
  · simp only [ouSolDeriv, ouSol]
    ring

theorem ouSol_self (c τ : ℝ) : ouSol c τ τ = 0 := by
  simp only [ouSol]
  ring

theorem ouSolDeriv_self (c τ : ℝ) : ouSolDeriv c τ τ = 1 := by
  rw [← ou_wronskian_series c τ]
  simp only [ouSolDeriv]
  ring

theorem continuous_ouSol_uncurry (τ : ℝ) : Continuous fun p : ℝ × ℝ => ouSol p.1 τ p.2 := by
  unfold ouSol
  have h1 : Continuous fun p : ℝ × ℝ => ouY p.1 1 0 τ :=
    (continuous_ouY_uncurry 1 0).comp (continuous_fst.prodMk continuous_const)
  have h2 : Continuous fun p : ℝ × ℝ => ouY p.1 0 1 τ :=
    (continuous_ouY_uncurry 0 1).comp (continuous_fst.prodMk continuous_const)
  exact continuous_const.mul ((h1.mul (continuous_ouY_uncurry 0 1)).sub
    (h2.mul (continuous_ouY_uncurry 1 0)))

theorem continuous_ouSolDeriv_uncurry (τ : ℝ) :
    Continuous fun p : ℝ × ℝ => ouSolDeriv p.1 τ p.2 := by
  unfold ouSolDeriv
  have h1 : Continuous fun p : ℝ × ℝ => ouY p.1 1 0 τ :=
    (continuous_ouY_uncurry 1 0).comp (continuous_fst.prodMk continuous_const)
  have h2 : Continuous fun p : ℝ × ℝ => ouY p.1 0 1 τ :=
    (continuous_ouY_uncurry 0 1).comp (continuous_fst.prodMk continuous_const)
  exact continuous_const.mul ((h1.mul (continuous_ouY'_uncurry 0 1)).sub
    (h2.mul (continuous_ouY'_uncurry 1 0)))

end

end PDE.FHLane
