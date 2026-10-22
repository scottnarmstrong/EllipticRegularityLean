module

public import PDEFoundation.Monotonicity.FriedlandHayman.Gauss.Weight

/-!
# Friedland--Hayman: local pieces of Barta's inequality

For a positive solution `φ = ouSol c τ` and a test function `g`, the identity
`(g'² - c g²) w = (p g² w)' + (g' - p g)² w` with `p = φ'/φ` gives, on every compact interval
`[a, L] ⊂ (τ, ∞)`, the lower bound `∫_a^L (g'² - c g²) w ≥ F L - F a`, where `F = p g² w`.
We also prove the bound `φ ≥ (s - τ)/2` near `τ` and the Cauchy--Schwarz bound
`g(a)² ≤ (a - τ) ∫_τ^a g'²`.
-/

@[expose] public section

open Set MeasureTheory Filter Topology

namespace PDE.FHLane

noncomputable section

/-- The boundary quantity `F = (φ'/φ) g² w`. -/
def bartaF (c τ : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ouSolDeriv c τ x / ouSol c τ x * g x ^ 2 * gaussW x

theorem hasDerivAt_bartaF {c τ s d : ℝ} {g : ℝ → ℝ} (hφ : 0 < ouSol c τ s)
    (hg : HasDerivAt g d s) :
    HasDerivAt (bartaF c τ g)
      ((d ^ 2 * gaussW s - c * (g s ^ 2 * gaussW s))
        - (d - ouSolDeriv c τ s / ouSol c τ s * g s) ^ 2 * gaussW s) s := by
  have h := (((hasDerivAt_ouSolDeriv c τ s).div (hasDerivAt_ouSol c τ s) hφ.ne').mul
    (hg.pow 2)).mul (hasDerivAt_gaussW s)
  unfold bartaF
  convert h using 1
  have := hφ.ne'
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, Pi.div_apply, Pi.pow_apply, Pi.mul_apply]
  field_simp
  ring

theorem bartaF_le_integral {c τ a L : ℝ} {g g' : ℝ → ℝ} (hg : Continuous g)
    (hder : ∀ s, τ < s → HasDerivAt g (g' s) s) (hcont' : ContinuousOn g' (Ioi τ))
    (hτa : τ < a) (haL : a ≤ L) (hpos : ∀ s, τ < s → 0 < ouSol c τ s) :
    bartaF c τ g L - bartaF c τ g a ≤
      ∫ x in a..L, (g' x ^ 2 * gaussW x - c * (g x ^ 2 * gaussW x)) := by
  have hsub : Icc a L ⊆ Ioi τ := fun x hx => lt_of_lt_of_le hτa hx.1
  have hcontφ : Continuous (ouSol c τ) := (continuous_ouSol_uncurry τ).comp
    (continuous_const.prodMk continuous_id)
  have hcontφ' : Continuous (ouSolDeriv c τ) := (continuous_ouSolDeriv_uncurry τ).comp
    (continuous_const.prodMk continuous_id)
  have hcp : ContinuousOn (fun x => ouSolDeriv c τ x / ouSol c τ x) (Icc a L) :=
    hcontφ'.continuousOn.div hcontφ.continuousOn (fun x hx => (hpos x (hsub hx)).ne')
  have hc1 : ContinuousOn (fun x => g' x ^ 2 * gaussW x - c * (g x ^ 2 * gaussW x)) (Icc a L) :=
    (((hcont'.mono hsub).pow 2).mul continuous_gaussW.continuousOn).sub
      (continuous_const.continuousOn.mul
        (((hg.pow 2).mul continuous_gaussW).continuousOn))
  have hc2 : ContinuousOn (fun x => (g' x - ouSolDeriv c τ x / ouSol c τ x * g x) ^ 2 * gaussW x)
      (Icc a L) :=
    (((hcont'.mono hsub).sub (hcp.mul hg.continuousOn)).pow 2).mul continuous_gaussW.continuousOn
  have hD := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := L)
    (f := bartaF c τ g)
    (f' := fun x => (g' x ^ 2 * gaussW x - c * (g x ^ 2 * gaussW x))
        - (g' x - ouSolDeriv c τ x / ouSol c τ x * g x) ^ 2 * gaussW x)
    (fun x hx => by
      rw [uIcc_of_le haL] at hx
      exact hasDerivAt_bartaF (hpos x (hsub hx)) (hder x (hsub hx)))
    ((hc1.sub hc2).intervalIntegrable_of_Icc (μ := volume) haL)
  have hint1 := hc1.intervalIntegrable_of_Icc (μ := volume) haL
  have hint2 := hc2.intervalIntegrable_of_Icc (μ := volume) haL
  rw [intervalIntegral.integral_sub hint1 hint2] at hD
  have hnn : 0 ≤ ∫ x in a..L, (g' x - ouSolDeriv c τ x / ouSol c τ x * g x) ^ 2 * gaussW x :=
    intervalIntegral.integral_nonneg haL (fun x _ => mul_nonneg (sq_nonneg _) (gaussW_pos x).le)
  linarith

/-- Near `τ` the solution is bounded below by `(s - τ)/2` and its derivative lies in `[1/2, 2]`. -/
theorem ouSol_near (c τ : ℝ) : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ a, τ < a → a ≤ τ + δ →
    (a - τ) / 2 ≤ ouSol c τ a ∧ 1 / 2 ≤ ouSolDeriv c τ a ∧ ouSolDeriv c τ a ≤ 2 := by
  have hcontφ' : Continuous (ouSolDeriv c τ) := (continuous_ouSolDeriv_uncurry τ).comp
    (continuous_const.prodMk continuous_id)
  have hev : ∀ᶠ x in 𝓝 τ, ouSolDeriv c τ x ∈ Ioo (1 / 2 : ℝ) 2 :=
    hcontφ'.continuousAt.eventually (Ioo_mem_nhds (by rw [ouSolDeriv_self]; norm_num)
      (by rw [ouSolDeriv_self]; norm_num))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min (ε / 2) 1, by positivity, min_le_right _ _, ?_⟩
  have hδ : min (ε / 2) 1 ≤ ε / 2 := min_le_left _ _
  have hin : ∀ x, τ ≤ x → x ≤ τ + min (ε / 2) 1 → ouSolDeriv c τ x ∈ Ioo (1 / 2 : ℝ) 2 := by
    intro x h1 h2
    apply hball
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hdd : ∀ x, HasDerivAt (fun x => ouSol c τ x - x / 2) (ouSolDeriv c τ x - 1 / 2) x := by
    intro x
    exact (hasDerivAt_ouSol c τ x).sub ((hasDerivAt_id x).div_const 2)
  have hδpos : 0 < min (ε / 2) 1 := by positivity
  have hmono : MonotoneOn (fun x => ouSol c τ x - x / 2) (Icc τ (τ + min (ε / 2) 1)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · exact fun x _ => (hdd x).continuousAt.continuousWithinAt
    · exact fun x _ => (hdd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hdd x).deriv]
      have := (hin x hx.1.le hx.2.le).1
      linarith
  intro a h1 h2
  refine ⟨?_, (hin a h1.le h2).1.le, (hin a h1.le h2).2.le⟩
  have := hmono (a := τ) (b := a) ⟨le_rfl, by linarith⟩ ⟨h1.le, h2⟩ h1.le
  simp only [ouSol_self] at this
  linarith

end

end PDE.FHLane
