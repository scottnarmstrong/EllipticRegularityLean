module

public import PDEFoundation.Monotonicity.FriedlandHayman.Gauss.Ground

/-!
# Friedland--Hayman: polynomially bounded functions against the Gaussian weight

`PolyBdd F` says that `|F s| ≤ C s ^ K` for large `s` (real exponent).  Such functions are
integrable against `gaussW` on every half line (if continuous) and `F s * gaussW s → 0` at `∞`.
The ground state `ψ_τ = ouSol (gaussBeta τ) τ` and its derivative are polynomially bounded.
-/

@[expose] public section

open Set MeasureTheory Filter Topology

namespace PDE.FHLane

namespace BKP

noncomputable section

/-- Polynomial bound at `+∞`, with real exponent. -/
def PolyBdd (F : ℝ → ℝ) : Prop :=
  ∃ C K L : ℝ, 0 ≤ K ∧ 1 ≤ L ∧ ∀ s, L ≤ s → |F s| ≤ C * s ^ K

theorem PolyBdd.mul {F G : ℝ → ℝ} (hF : PolyBdd F) (hG : PolyBdd G) :
    PolyBdd fun s => F s * G s := by
  obtain ⟨C₁, K₁, L₁, hK₁, hL₁, h₁⟩ := hF
  obtain ⟨C₂, K₂, L₂, hK₂, hL₂, h₂⟩ := hG
  refine ⟨C₁ * C₂, K₁ + K₂, max L₁ L₂, add_nonneg hK₁ hK₂, le_trans hL₁ (le_max_left _ _),
    fun s hs => ?_⟩
  have hs1 : L₁ ≤ s := le_trans (le_max_left _ _) hs
  have hs2 : L₂ ≤ s := le_trans (le_max_right _ _) hs
  have hpos : 0 < s := lt_of_lt_of_le (lt_of_lt_of_le one_pos hL₁) hs1
  rw [abs_mul, Real.rpow_add hpos]
  calc |F s| * |G s| ≤ (C₁ * s ^ K₁) * (C₂ * s ^ K₂) :=
        mul_le_mul (h₁ s hs1) (h₂ s hs2) (abs_nonneg _) (le_trans (abs_nonneg _) (h₁ s hs1))
    _ = C₁ * C₂ * (s ^ K₁ * s ^ K₂) := by ring

theorem PolyBdd.id : PolyBdd fun s => s :=
  ⟨1, 1, 1, zero_le_one, le_rfl, fun s hs => by
    rw [Real.rpow_one, one_mul]
    exact le_of_eq (abs_of_nonneg (le_trans zero_le_one hs))⟩

theorem polyBdd_of_le {F : ℝ → ℝ} {C K L : ℝ} (h0 : ∀ s, L ≤ s → 0 ≤ F s)
    (h : ∀ s, L ≤ s → F s ≤ C * s ^ K) : PolyBdd F := by
  refine ⟨|C|, max K 0, max L 1, le_max_right _ _, le_max_right _ _, fun s hs => ?_⟩
  have hsL : L ≤ s := le_trans (le_max_left _ _) hs
  have hs1 : 1 ≤ s := le_trans (le_max_right _ _) hs
  rw [abs_of_nonneg (h0 s hsL)]
  calc F s ≤ C * s ^ K := h s hsL
    _ ≤ |C| * s ^ K := by
        gcongr
        exact le_abs_self C
    _ ≤ |C| * s ^ (max K 0) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _)) (abs_nonneg C)

/-- A polynomially bounded function tends to `0` against the Gaussian weight. -/
theorem PolyBdd.tendsto_mul_gaussW {F : ℝ → ℝ} (hF : PolyBdd F) :
    Tendsto (fun s => F s * gaussW s) atTop (𝓝 0) := by
  obtain ⟨C, K, L, -, hL, h⟩ := hF
  have hlim : Tendsto (fun s : ℝ => C * (s ^ K * Real.exp (-1 * s))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero K 1 one_pos).const_mul C
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (max L 2)] with s hs
  have hsL : L ≤ s := le_trans (le_max_left _ _) hs
  have hs2 : 2 ≤ s := le_trans (le_max_right _ _) hs
  have hw : gaussW s ≤ Real.exp (-1 * s) := by
    unfold gaussW
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gaussW_pos s)]
  calc |F s| * gaussW s ≤ (C * s ^ K) * Real.exp (-1 * s) :=
        mul_le_mul (h s hsL) hw (gaussW_pos s).le (le_trans (abs_nonneg _) (h s hsL))
    _ = C * (s ^ K * Real.exp (-1 * s)) := by ring

/-- A continuous polynomially bounded function is integrable against `gaussW` on any half line. -/
theorem PolyBdd.integrableOn_mul_gaussW {F : ℝ → ℝ} (hF : PolyBdd F) (hc : Continuous F) (a : ℝ) :
    IntegrableOn (fun s => F s * gaussW s) (Ioi a) := by
  obtain ⟨C, K, L, hK, hL, h⟩ := hF
  have h1 : IntegrableOn (fun s => F s * gaussW s) (Ioc a L) :=
    ((hc.mul continuous_gaussW).continuousOn.integrableOn_Icc (a := a) (b := L)).mono_set
      Ioc_subset_Icc_self
  have hg : IntegrableOn (fun s : ℝ => C * (s ^ K * Real.exp (-(1 / 4) * s ^ 2))) (Ioi L) :=
    ((integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 4) (by norm_num) (s := K)
      (by linarith)).const_mul C).integrableOn
  have h2 : IntegrableOn (fun s => F s * gaussW s) (Ioi L) := by
    refine Integrable.mono' hg ((hc.mul continuous_gaussW).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hsL : L ≤ s := le_of_lt hs
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gaussW_pos s)]
    calc |F s| * gaussW s ≤ (C * s ^ K) * Real.exp (-(1 / 4) * s ^ 2) :=
          mul_le_mul (h s hsL) (gaussW_le_exp_quarter s) (gaussW_pos s).le
            (le_trans (abs_nonneg _) (h s hsL))
      _ = C * (s ^ K * Real.exp (-(1 / 4) * s ^ 2)) := by ring
  exact (h1.union h2).mono_set fun s hs => by
    by_cases hsL : s ≤ L
    · exact Or.inl ⟨hs, hsL⟩
    · exact Or.inr (not_le.mp hsL)

theorem continuous_ouSol (c τ : ℝ) : Continuous (ouSol c τ) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_ouSol c τ s).continuousAt

theorem continuous_ouSolDeriv (c τ : ℝ) : Continuous (ouSolDeriv c τ) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_ouSolDeriv c τ s).continuousAt

/-- The ground state `ψ_τ`. -/
abbrev gpsi (τ : ℝ) : ℝ → ℝ := ouSol (gaussBeta τ) τ

/-- The derivative of the ground state. -/
abbrev gdpsi (τ : ℝ) : ℝ → ℝ := ouSolDeriv (gaussBeta τ) τ

theorem gpsi_pos {τ s : ℝ} (h : τ < s) : 0 < gpsi τ s := ouAdmissible_gaussBeta τ |>.2 s h

theorem polyBdd_gpsi (τ : ℝ) : PolyBdd (gpsi τ) := by
  obtain ⟨C, K, L, -, h⟩ := ouSol_gaussBeta_growth τ
  refine polyBdd_of_le (C := C) (K := K) (L := max L (τ + 1))
    (fun s hs => (gpsi_pos (by linarith [le_max_right L (τ + 1)])).le)
    (fun s hs => (h s (le_trans (le_max_left _ _) hs)).1)

theorem polyBdd_gdpsi (τ : ℝ) : PolyBdd (gdpsi τ) := by
  obtain ⟨C, K, L, -, h⟩ := ouSol_gaussBeta_growth τ
  exact polyBdd_of_le (C := C) (K := K) (L := L) (fun s hs => (h s hs).2.1)
    (fun s hs => (h s hs).2.2)

end

end BKP

end PDE.FHLane
