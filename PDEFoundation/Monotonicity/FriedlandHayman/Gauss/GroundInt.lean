module

public import PDEFoundation.Monotonicity.FriedlandHayman.Gauss.PolyBdd

/-!
# Friedland--Hayman: integrals of the ground state

Integrability of the ground state densities on half lines, positivity of `I(τ) = ∫ ψ_τ² w`, the
energy identity `∫ ψ'² w = β I`, the integration by parts identity `2 ∫ ψ ψ' w = ∫ s ψ² w`, and the
mean `gaussMean τ` of the density `ψ_τ² w`.
-/

@[expose] public section

open Set MeasureTheory Filter Topology

namespace PDE.FHLane

noncomputable section

namespace BKP

theorem integrableOn_gpsi_sq (τ a : ℝ) :
    IntegrableOn (fun s => gpsi τ s ^ 2 * gaussW s) (Ioi a) := by
  have := ((polyBdd_gpsi τ).mul (polyBdd_gpsi τ)).integrableOn_mul_gaussW
    ((continuous_ouSol _ τ).mul (continuous_ouSol _ τ)) a
  exact this.congr_fun (fun s _ => by ring) measurableSet_Ioi

theorem integrableOn_gpsi_mean (τ a : ℝ) :
    IntegrableOn (fun s => s * gpsi τ s ^ 2 * gaussW s) (Ioi a) := by
  have := (PolyBdd.id.mul ((polyBdd_gpsi τ).mul (polyBdd_gpsi τ))).integrableOn_mul_gaussW
    (continuous_id.mul ((continuous_ouSol _ τ).mul (continuous_ouSol _ τ))) a
  exact this.congr_fun (fun s _ => by ring) measurableSet_Ioi

theorem integrableOn_gdpsi_sq (τ a : ℝ) :
    IntegrableOn (fun s => gdpsi τ s ^ 2 * gaussW s) (Ioi a) := by
  have := ((polyBdd_gdpsi τ).mul (polyBdd_gdpsi τ)).integrableOn_mul_gaussW
    ((continuous_ouSolDeriv _ τ).mul (continuous_ouSolDeriv _ τ)) a
  exact this.congr_fun (fun s _ => by ring) measurableSet_Ioi

theorem integrableOn_gpsi_gdpsi (τ a : ℝ) :
    IntegrableOn (fun s => gpsi τ s * gdpsi τ s * gaussW s) (Ioi a) :=
  ((polyBdd_gpsi τ).mul (polyBdd_gdpsi τ)).integrableOn_mul_gaussW
    ((continuous_ouSol _ τ).mul (continuous_ouSolDeriv _ τ)) a

theorem integral_Ioi_eq_zero_of_hasDerivAt {F F' : ℝ → ℝ} {a : ℝ}
    (hd : ∀ s, HasDerivAt F (F' s) s) (h0 : F a = 0) (hint : IntegrableOn F' (Ioi a))
    (hlim : Tendsto F atTop (𝓝 0)) : ∫ s in Ioi a, F' s = 0 := by
  have := integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x) hint hlim
  simpa [h0] using this

end BKP

open BKP

theorem ground_integral_pos (τ : ℝ) :
    0 < ∫ s in Set.Ioi τ, ouSol (gaussBeta τ) τ s ^ 2 * gaussW s := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun s => mul_nonneg (sq_nonneg _) (gaussW_pos s).le)
    (integrableOn_gpsi_sq τ τ)]
  have hsub : Ioi τ ⊆ Function.support (fun s => ouSol (gaussBeta τ) τ s ^ 2 * gaussW s) ∩ Ioi τ := by
    intro s hs
    exact ⟨mul_ne_zero (pow_ne_zero 2 (gpsi_pos hs).ne') (gaussW_pos s).ne', hs⟩
  exact lt_of_lt_of_le (by simp) (measure_mono hsub)

theorem ground_energy (τ : ℝ) :
    ∫ s in Set.Ioi τ, ouSolDeriv (gaussBeta τ) τ s ^ 2 * gaussW s =
      gaussBeta τ * ∫ s in Set.Ioi τ, ouSol (gaussBeta τ) τ s ^ 2 * gaussW s := by
  have hd : ∀ s, HasDerivAt (fun s => gpsi τ s * gdpsi τ s * gaussW s)
      (gdpsi τ s ^ 2 * gaussW s - gaussBeta τ * (gpsi τ s ^ 2 * gaussW s)) s := fun s =>
    (((hasDerivAt_ouSol _ τ s).mul (hasDerivAt_ouSolDeriv _ τ s)).mul
      (hasDerivAt_gaussW s)).congr_deriv (by simp only [Pi.mul_apply]; ring)
  have h := integral_Ioi_eq_zero_of_hasDerivAt hd (by simp [ouSol_self])
    ((integrableOn_gdpsi_sq τ τ).sub ((integrableOn_gpsi_sq τ τ).const_mul _))
    (((polyBdd_gpsi τ).mul (polyBdd_gdpsi τ)).tendsto_mul_gaussW)
  rw [integral_sub (integrableOn_gdpsi_sq τ τ) ((integrableOn_gpsi_sq τ τ).const_mul _),
    integral_const_mul] at h
  linarith

/-- Integration by parts: `2 ∫ ψ ψ' w = ∫ s ψ² w`. -/
theorem ground_ibp (τ : ℝ) :
    2 * ∫ s in Set.Ioi τ, ouSol (gaussBeta τ) τ s * ouSolDeriv (gaussBeta τ) τ s * gaussW s =
      ∫ s in Set.Ioi τ, s * ouSol (gaussBeta τ) τ s ^ 2 * gaussW s := by
  have hd : ∀ s, HasDerivAt (fun s => gpsi τ s * gpsi τ s * gaussW s)
      (2 * (gpsi τ s * gdpsi τ s * gaussW s) - s * gpsi τ s ^ 2 * gaussW s) s := fun s =>
    (((hasDerivAt_ouSol _ τ s).mul (hasDerivAt_ouSol _ τ s)).mul
      (hasDerivAt_gaussW s)).congr_deriv (by simp only [Pi.mul_apply]; ring)
  have h := integral_Ioi_eq_zero_of_hasDerivAt hd (by simp [ouSol_self])
    (((integrableOn_gpsi_gdpsi τ τ).const_mul 2).sub (integrableOn_gpsi_mean τ τ))
    (((polyBdd_gpsi τ).mul (polyBdd_gpsi τ)).tendsto_mul_gaussW)
  rw [integral_sub ((integrableOn_gpsi_gdpsi τ τ).const_mul 2) (integrableOn_gpsi_mean τ τ),
    integral_const_mul] at h
  linarith

/-- Mean position of the ground-state density `ψ_τ² w` on `(τ, ∞)`. -/
def gaussMean (τ : ℝ) : ℝ :=
  (∫ s in Set.Ioi τ, s * ouSol (gaussBeta τ) τ s ^ 2 * gaussW s) /
    ∫ s in Set.Ioi τ, ouSol (gaussBeta τ) τ s ^ 2 * gaussW s

theorem gaussMean_mul (τ : ℝ) :
    gaussMean τ * ∫ s in Set.Ioi τ, ouSol (gaussBeta τ) τ s ^ 2 * gaussW s =
      ∫ s in Set.Ioi τ, s * ouSol (gaussBeta τ) τ s ^ 2 * gaussW s :=
  div_mul_cancel₀ _ (ground_integral_pos τ).ne'

end

end PDE.FHLane
