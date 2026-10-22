module

public import PDEFoundation.PDE.HarmonicWeylConvergence

/-! # A smooth harmonic representative of a weakly harmonic H¹ function -/

@[expose] public section

namespace PDE

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {d : ℕ}

private theorem euclideanCoordLaplacian_eq_of_eqOn_open
    {f g : Vec d → ℝ} {U : Set (Vec d)} (hU : IsOpen U)
    (hfg : Set.EqOn f g U) {x : Vec d} (hx : x ∈ U) :
    euclideanCoordLaplacian f x = euclideanCoordLaplacian g x := by
  unfold euclideanCoordLaplacian
  apply Finset.sum_congr rfl
  intro i _
  unfold euclideanCoordSecondDeriv
  have hderiv : Set.EqOn (euclideanCoordDeriv i f) (euclideanCoordDeriv i g) U := by
    intro y hy
    unfold euclideanCoordDeriv
    have hev : f =ᶠ[𝓝 y] g := by
      filter_upwards [hU.mem_nhds hy] with z hz
      exact hfg hz
    rw [hev.fderiv_eq]
  have hev : euclideanCoordDeriv i f =ᶠ[𝓝 x] euclideanCoordDeriv i g := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hderiv hy
  exact congrArg (fun L : Vec d →L[ℝ] ℝ => L (basisVec i)) hev.fderiv_eq

/-- Weyl's lemma on a round ball: a weakly harmonic H¹ function has a smooth
classically harmonic representative that agrees with all sufficiently small
interior mollifications and with the original function almost everywhere. -/
theorem exists_harmonicWeylRepresentative
    (hd : 0 < d) {x₀ : Vec d} {r : ℝ} (hr : 0 < r)
    (u : H1Function (euclideanBall x₀ r))
    (hsol : IsWeakDivergenceFormSolutionOn
      (fun _ : Vec d => (1 : Mat d)) (euclideanBall x₀ r) u 0 0) :
    ∃ v : Vec d → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) v (euclideanBall x₀ r) ∧
      (∀ y ∈ euclideanBall x₀ r, euclideanCoordLaplacian v y = 0) ∧
      (∀ᵐ y ∂volumeOn (euclideanBall x₀ r), v y = u.toFun y) ∧
      (∀ y ∈ euclideanBall x₀ r, ∀ δ : ℝ, 0 < δ →
        2 * δ < r - vecEuclideanNorm (y - x₀) → v y = harmonicMollify u δ y) := by
  classical
  let U := euclideanBall x₀ r
  let m : Vec d → ℝ := fun y => r - vecEuclideanNorm (y - x₀)
  let η : Vec d → ℝ := fun y => m y / 4
  let v : Vec d → ℝ := fun y => if y ∈ U then harmonicMollify u (η y) y else 0
  have hU : IsOpen U := isOpen_euclideanBall x₀ r
  have hmargin {y : Vec d} (hy : y ∈ U) : 0 < m y := by
    have hynorm := (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp hy
    dsimp [m]
    linarith
  have hη {y : Vec d} (hy : y ∈ U) : 0 < η y := by
    dsimp [η]
    linarith [hmargin hy]
  have hvalue : ∀ y ∈ U, ∀ δ : ℝ, 0 < δ → 2 * δ < m y →
      v y = harmonicMollify u δ y := by
    intro y hy δ hδ hδm
    have hηm : η y + δ < m y := by
      dsimp [η]
      have hm := hmargin hy
      linarith
    simpa [v, hy] using
      (harmonicMollify_eq_of_scales hd hr (hη hy) hδ u hsol hηm)
  have hlocal (y : Vec d) (hy : y ∈ U) :
      ∃ ρ : ℝ, 0 < ρ ∧
        Set.EqOn v (harmonicMollify u (η y)) (euclideanBall y ρ) := by
    let ρ : ℝ := m y / 8
    have hρ : 0 < ρ := by dsimp [ρ]; linarith [hmargin hy]
    refine ⟨ρ, hρ, ?_⟩
    intro z hz
    have hzy := (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).mp hz
    have hdecomp : z - x₀ = (z - y) + (y - x₀) := by abel
    have hnorm : vecEuclideanNorm (z - x₀) ≤
        vecEuclideanNorm (z - y) + vecEuclideanNorm (y - x₀) := by
      rw [hdecomp]
      exact vecEuclideanNorm_add_le _ _
    have hmz : m y - ρ < m z := by dsimp [m]; linarith
    have hzU : z ∈ U := by
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mpr
      dsimp [m, ρ] at hmz ⊢
      linarith [hmargin hy]
    apply hvalue z hzU (η y) (hη hy)
    dsimp [η, ρ] at hmz ⊢
    linarith [hmargin hy]
  have hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) v U := by
    apply hU.contDiffOn_iff.mpr
    intro y hy
    obtain ⟨ρ, hρ, heq⟩ := hlocal y hy
    have hev : v =ᶠ[𝓝 y] harmonicMollify u (η y) := by
      filter_upwards [(isOpen_euclideanBall y ρ).mem_nhds
        (center_mem_euclideanBall y hρ)] with z hz
      exact heq hz
    exact ((contDiff_harmonicMollify hU u (hη hy)).contDiffAt).congr_of_eventuallyEq hev
  have hharm : ∀ y ∈ U, euclideanCoordLaplacian v y = 0 := by
    intro y hy
    obtain ⟨ρ, hρ, heq⟩ := hlocal y hy
    rw [euclideanCoordLaplacian_eq_of_eqOn_open
      (isOpen_euclideanBall y ρ) heq (center_mem_euclideanBall y hρ)]
    apply euclideanCoordLaplacian_harmonicMollify_eq_zero hU u hsol (hη hy)
    have hηbound : η y + η y ≤ m y := by
      dsimp [η]
      linarith [hmargin hy]
    apply euclideanBall_subset_of_center_norm_add_le (hη hy) hr
    dsimp [m] at hηbound ⊢
    linarith [hη hy]
  have hg : LocallyIntegrable (Set.indicator U u.toFun) volume := by
    have hmem : MemLp (Set.indicator U u.toFun) 2 volume := by
      rw [memLp_indicator_iff_restrict hU.measurableSet]
      exact u.memL2
    exact hmem.locallyIntegrable (by norm_num)
  have hae := ae_tendsto_harmonicKernelScaled_convolution_of_locallyIntegrable hg
  have haeeq : ∀ᵐ y ∂volumeOn U, v y = u.toFun y := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hU.measurableSet]
      with y hlim hy
    have hevent : (fun δ : ℝ => harmonicMollify u δ y) =ᶠ[𝓝[>] 0]
        (fun _ => v y) := by
      have hthreshold : 0 < m y / 2 := by linarith [hmargin hy]
      have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < m y / 2 :=
        (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
          (Iio_mem_nhds hthreshold)
      filter_upwards [self_mem_nhdsWithin, hsmall] with δ hδ hδsmall
      exact (hvalue y hy δ hδ (by linarith)).symm
    have hlimv : Tendsto (fun δ : ℝ => harmonicMollify u δ y)
        (𝓝[>] 0) (𝓝 (v y)) :=
      Tendsto.congr' hevent.symm tendsto_const_nhds
    have hlimu : Tendsto (fun δ : ℝ => harmonicMollify u δ y)
        (𝓝[>] 0) (𝓝 (Set.indicator U u.toFun y)) := by
      simpa only [harmonicMollify] using hlim
    have hvu : v y = Set.indicator U u.toFun y :=
      tendsto_nhds_unique hlimv hlimu
    simpa [Set.indicator_of_mem hy] using hvu
  exact ⟨v, hsmooth, hharm, haeeq, hvalue⟩

end

end PDE
