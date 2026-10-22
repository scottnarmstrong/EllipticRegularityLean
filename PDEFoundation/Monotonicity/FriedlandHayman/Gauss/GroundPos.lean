module

public import PDEFoundation.Monotonicity.FriedlandHayman.Gauss.Beta

/-!
# Friedland--Hayman: the threshold is admissible

The ground state `ouSol (gaussBeta τ) τ` is positive on `(τ, ∞)`: it is a limit of positive
solutions, hence nonnegative, and an interior zero would be a double zero, forcing the solution to
vanish identically by uniqueness.
-/

@[expose] public section

open Set MeasureTheory Filter Topology

namespace PDE.FHLane

noncomputable section

theorem continuous_ouSol_param (τ s : ℝ) : Continuous fun c => ouSol c τ s :=
  (continuous_ouSol_uncurry τ).comp (continuous_id.prodMk continuous_const)

theorem continuous_ouSolDeriv_param (τ s : ℝ) : Continuous fun c => ouSolDeriv c τ s :=
  (continuous_ouSolDeriv_uncurry τ).comp (continuous_id.prodMk continuous_const)

theorem ouSol_gaussBeta_nonneg (τ : ℝ) : ∀ s, τ < s → 0 ≤ ouSol (gaussBeta τ) τ s := by
  intro s hs
  have hmem : gaussBeta τ ∈ closure {c | OUAdmissible τ c} :=
    csSup_mem_closure (ouAdmissible_nonempty τ) (bddAbove_ouAdmissible τ)
  have hclosed : IsClosed {c : ℝ | 0 ≤ ouSol c τ s} :=
    isClosed_le continuous_const (continuous_ouSol_param τ s)
  have hsub : {c | OUAdmissible τ c} ⊆ {c : ℝ | 0 ≤ ouSol c τ s} :=
    fun c hc => (hc.2 s hs).le
  exact closure_minimal hsub hclosed hmem

/-- The threshold is admissible: the ground state is positive. -/
theorem ouAdmissible_gaussBeta (τ : ℝ) : OUAdmissible τ (gaussBeta τ) := by
  refine ⟨gaussBeta_nonneg τ, fun s hs => ?_⟩
  refine lt_of_le_of_ne (ouSol_gaussBeta_nonneg τ s hs) fun h0 => ?_
  have hmin : IsLocalMin (ouSol (gaussBeta τ) τ) s := by
    filter_upwards [Ioi_mem_nhds hs] with x hx
    rw [← h0]
    exact ouSol_gaussBeta_nonneg τ x hx
  have hder0 : ouSolDeriv (gaussBeta τ) τ s = 0 := hmin.hasDerivAt_eq_zero (hasDerivAt_ouSol _ _ _)
  have hzero := ou_unique (c := gaussBeta τ) (a := s) (hasDerivAt_ouSol _ τ)
    (hasDerivAt_ouSolDeriv _ τ) h0.symm hder0
  have hfun : ouSol (gaussBeta τ) τ = fun _ => 0 := funext hzero
  have h1 := hasDerivAt_ouSol (gaussBeta τ) τ τ
  rw [hfun] at h1
  have h2 := h1.unique (hasDerivAt_const τ (0 : ℝ))
  rw [ouSolDeriv_self] at h2
  exact one_ne_zero h2

end

end PDE.FHLane
