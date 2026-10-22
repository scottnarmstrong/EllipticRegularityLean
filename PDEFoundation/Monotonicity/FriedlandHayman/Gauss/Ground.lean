module

public import PDEFoundation.Monotonicity.FriedlandHayman.Gauss.GroundGrowth

/-!
# Friedland--Hayman: the Gaussian ground state

Summary of the one-dimensional Gaussian API (`β(τ)` and its ground state `ψ_τ = ouSol β τ`):
`ouAdmissible_gaussBeta` (positivity) and `ouSol_gaussBeta_growth` (polynomial growth of the ground
state and of its derivative, with a real exponent, i.e. `Real.rpow`).
-/

@[expose] public section

open Set MeasureTheory Filter Topology

namespace PDE.FHLane

noncomputable section

/-- Polynomial growth of the ground state (recessive solution). -/
theorem ouSol_gaussBeta_growth (τ : ℝ) : ∃ C K L : ℝ, 0 < L ∧ ∀ s, L ≤ s →
    ouSol (gaussBeta τ) τ s ≤ C * s ^ K ∧ 0 ≤ ouSolDeriv (gaussBeta τ) τ s ∧
    ouSolDeriv (gaussBeta τ) τ s ≤ C * s ^ K := by
  set β := gaussBeta τ with hβ
  have hadm : OUAdmissible τ β := ouAdmissible_gaussBeta τ
  have hβ0 : 0 ≤ β := hadm.1
  set L : ℝ := |τ| + 4 * β + 4 with hLdef
  have hL1 : 4 * β + 4 ≤ L := by rw [hLdef]; linarith [abs_nonneg τ]
  have hLmax : max τ 0 < L := max_lt (by linarith [le_abs_self τ]) (by linarith)
  have hL0 : 0 < L := by linarith
  have hLsq : 4 * β + 2 ≤ L ^ 2 := by nlinarith
  have hτL : τ < L := lt_of_le_of_lt (le_max_left _ _) hLmax
  have hψ : ∀ s, L ≤ s → 0 < ouSol β τ s := fun s hs => hadm.2 s (lt_of_lt_of_le hτL hs)
  have hDle : ∀ s, L ≤ s → s * ouSolDeriv β τ s ≤ 2 * β * ouSol β τ s := by
    intro s hs
    have h := groundD_nonpos hLmax hLsq s hs
    unfold groundD groundQ at h
    have h2 : s * ouSolDeriv β τ s / ouSol β τ s ≤ 2 * β := by
      rw [mul_div_assoc]; linarith
    rwa [div_le_iff₀ (hψ s hs)] at h2
  set K : ℝ := 2 * β with hK
  have hderiv : ∀ s, L ≤ s → HasDerivAt (fun x => ouSol β τ x * x ^ (-K))
      (ouSolDeriv β τ s * s ^ (-K) + ouSol β τ s * (-K * s ^ (-K - 1))) s := by
    intro s hs
    have hs0 : s ≠ 0 := (lt_of_lt_of_le hL0 hs).ne'
    exact (hasDerivAt_ouSol β τ s).mul (Real.hasDerivAt_rpow_const (Or.inl hs0))
  have hanti : AntitoneOn (fun x => ouSol β τ x * x ^ (-K)) (Ici L) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici L)
      (fun x hx => (hderiv x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Ici] at hx
    have hx' : L ≤ x := hx.out.le
    rw [(hderiv x hx').deriv]
    have hxpos : 0 < x := lt_of_lt_of_le hL0 hx'
    rw [Real.rpow_sub_one hxpos.ne']
    have h1 := hDle x hx'
    have hp : 0 < x ^ (-K) := Real.rpow_pos_of_pos hxpos _
    have e : ouSolDeriv β τ x * x ^ (-K) + ouSol β τ x * (-K * (x ^ (-K) / x))
        = (x ^ (-K) / x) * (x * ouSolDeriv β τ x - K * ouSol β τ x) := by
      field_simp
      ring
    rw [e]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by rw [hK]; linarith)
  set M : ℝ := ouSol β τ L * L ^ (-K) with hM
  have hM0 : 0 ≤ M := mul_nonneg (hψ L le_rfl).le (Real.rpow_pos_of_pos hL0 _).le
  have hbound : ∀ s, L ≤ s → ouSol β τ s ≤ M * s ^ K := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le hL0 hs
    have h := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs) hs
    simp only at h
    rw [Real.rpow_neg hspos.le] at h
    have hp : 0 < s ^ K := Real.rpow_pos_of_pos hspos _
    exact (mul_inv_le_iff₀ hp).mp h
  have hK0 : 0 ≤ K := by rw [hK]; linarith
  refine ⟨M * (K + 1), K, L, hL0, fun s hs => ?_⟩
  have hspos : 0 < s := lt_of_lt_of_le hL0 hs
  have hs1 : 1 ≤ s := by linarith
  have hp : 0 ≤ s ^ K := (Real.rpow_pos_of_pos hspos _).le
  have hD0 : 0 ≤ ouSolDeriv β τ s :=
    ouSolDeriv_nonneg hβ0 hadm.2 s (lt_of_lt_of_le hLmax hs)
  have hb := hbound s hs
  refine ⟨?_, hD0, ?_⟩
  · calc ouSol β τ s ≤ M * s ^ K := hb
      _ ≤ M * (K + 1) * s ^ K := by
          have : 0 ≤ M * s ^ K := mul_nonneg hM0 hp
          nlinarith
  · have h1 := hDle s hs
    have h2 : ouSolDeriv β τ s ≤ s * ouSolDeriv β τ s := by nlinarith
    have h3 : K * ouSol β τ s ≤ K * (M * s ^ K) := mul_le_mul_of_nonneg_left hb hK0
    have h4 : 0 ≤ M * s ^ K := mul_nonneg hM0 hp
    calc ouSolDeriv β τ s ≤ s * ouSolDeriv β τ s := h2
      _ ≤ K * ouSol β τ s := by rw [hK]; linarith
      _ ≤ K * (M * s ^ K) := h3
      _ ≤ M * (K + 1) * s ^ K := by nlinarith

end

end PDE.FHLane
