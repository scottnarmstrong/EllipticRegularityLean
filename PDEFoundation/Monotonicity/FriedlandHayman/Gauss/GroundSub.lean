module

public import PDEFoundation.Monotonicity.FriedlandHayman.Gauss.GroundInv

/-!
# Friedland--Hayman: the ground state stays below the barrier `y' = (s/2) y`

For `β = gaussBeta τ` and `ψ = ouSol β τ` we show `ψ' < (s/2) ψ` for every `s > τ` with `s ≥ 0` and
`s² ≥ 4β + 2`.  Otherwise forward invariance (`GroundInv`) together with joint continuity of the
solution in the parameter would make every `c` slightly above `β` admissible.
-/

@[expose] public section

open Set MeasureTheory Filter Topology

namespace PDE.FHLane

noncomputable section

/-- Uniform positivity of `ouSol c τ` just to the right of `τ`, for `c` near `c₀`. -/
theorem ouSol_near_uniform (c₀ τ : ℝ) : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
    ∀ᶠ c in 𝓝 c₀, ∀ a, τ < a → a ≤ τ + δ → 0 < ouSol c τ a := by
  have hev : ∀ᶠ p in 𝓝 (c₀, τ), (1 / 2 : ℝ) < ouSolDeriv p.1 τ p.2 :=
    (continuous_ouSolDeriv_uncurry τ).continuousAt.eventually
      (Ioi_mem_nhds (by show (1 / 2 : ℝ) < ouSolDeriv c₀ τ τ; rw [ouSolDeriv_self]; norm_num))
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hev
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨min (ε / 2) 1, by positivity, min_le_right _ _, ?_⟩
  filter_upwards [hU] with c hc a h1 h2
  have hδ : min (ε / 2) 1 ≤ ε / 2 := min_le_left _ _
  have hδpos : 0 < min (ε / 2) 1 := by positivity
  have hin : ∀ x, τ ≤ x → x ≤ τ + min (ε / 2) 1 → (1 / 2 : ℝ) < ouSolDeriv c τ x := by
    intro x hx1 hx2
    have hxV : x ∈ V := hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
    exact hUV (Set.mk_mem_prod hc hxV)
  have hdd : ∀ x, HasDerivAt (fun x => ouSol c τ x - x / 2) (ouSolDeriv c τ x - 1 / 2) x := by
    intro x
    exact (hasDerivAt_ouSol c τ x).sub ((hasDerivAt_id x).div_const 2)
  have hmono : MonotoneOn (fun x => ouSol c τ x - x / 2) (Icc τ (τ + min (ε / 2) 1)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · exact fun x _ => (hdd x).continuousAt.continuousWithinAt
    · exact fun x _ => (hdd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hdd x).deriv]
      have := hin x hx.1.le hx.2.le
      linarith
  have := hmono (a := τ) (b := a) ⟨le_rfl, by linarith⟩ ⟨h1.le, h2⟩ h1.le
  simp only [ouSol_self] at this
  linarith

/-- The ground state lies strictly below the barrier. -/
theorem ouU_gaussBeta_neg {τ L : ℝ} (hLτ : τ < L) (hL0 : 0 ≤ L)
    (hL : 4 * gaussBeta τ + 2 ≤ L ^ 2) : ouU (gaussBeta τ) τ L < 0 := by
  by_contra hcon
  push Not at hcon
  set β := gaussBeta τ with hβ
  have hadm := ouAdmissible_gaussBeta τ
  rw [← hβ] at hadm
  have hψpos : ∀ t, L ≤ t → t ≤ L + 1 → 0 < ouSol β τ t := fun t ht _ =>
    hadm.2 t (lt_of_lt_of_le hLτ ht)
  have hu1 : 0 < ouU β τ (L + 1) := ouU_succ_pos hL0 hL hψpos hcon
  obtain ⟨δ, hδ, hδ1, hnear⟩ := ouSol_near_uniform β τ
  have hP1 : ∀ᶠ c in 𝓝 β, ∀ s ∈ Icc (τ + δ) (L + 1), 0 < ouSol c τ s := by
    refine (isCompact_Icc (a := τ + δ) (b := L + 1)).eventually_forall_of_forall_eventually ?_
    intro y hy
    have hy' : 0 < ouSol β τ y := hadm.2 y (by linarith [hy.1])
    exact (continuous_ouSol_uncurry τ).continuousAt.eventually (Ioi_mem_nhds hy')
  have hP2 : ∀ᶠ c in 𝓝 β, 4 * c + 2 < (L + 1) ^ 2 := by
    refine (Continuous.continuousAt (by fun_prop : Continuous fun c : ℝ => 4 * c + 2)).eventually
      (Iio_mem_nhds ?_)
    nlinarith
  have hP3 : ∀ᶠ c in 𝓝 β, 0 < ouU c τ (L + 1) := by
    have hcont : Continuous fun c => ouU c τ (L + 1) := by
      unfold ouU
      exact (continuous_ouSolDeriv_param τ _).sub (continuous_const.mul (continuous_ouSol_param τ _))
    exact hcont.continuousAt.eventually (Ioi_mem_nhds hu1)
  obtain ⟨c, ⟨⟨⟨hc1, hc2⟩, hc3⟩, hc4⟩, hcβ⟩ := ((((hP1.and hP2).and hP3).and hnear).filter_mono
    nhdsWithin_le_nhds |>.and (self_mem_nhdsWithin (s := Ioi β))).exists
  have hcβ' : β < c := hcβ
  have hβ0 : 0 ≤ β := gaussBeta_nonneg τ
  have hadmc : OUAdmissible τ c := by
    refine ⟨by linarith, fun s hs => ?_⟩
    rcases le_or_gt s (τ + δ) with h | h
    · exact hc4 s hs h
    rcases le_or_gt s (L + 1) with h' | h'
    · exact hc1 s ⟨h.le, h'⟩
    · refine ouSol_pos_forward (c := c) (L := L + 1) (by linarith) hc2.le
        (hc1 (L + 1) ⟨by linarith, le_rfl⟩) hc3.le s h'.le
  have := le_gaussBeta hadmc
  linarith

end

end PDE.FHLane
