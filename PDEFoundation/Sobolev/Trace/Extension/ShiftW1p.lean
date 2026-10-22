module

public import PDEFoundation.Sobolev.Trace.Extension.ShiftIntegral
public import PDEFoundation.Sobolev.Trace.Extension.ShiftBoundary

/-!
# Shifted extensions converge to the extension in `W^{1,p}(Ω)`

By the pointwise and integral bounds, the `p`-th powers of the `L^p(Ω)` norms of
`shift τ - ext` and of the length of its gradient are bounded by `∑ⱼ cⱼ ∫_{t>0} Q_{j,τ}`, which tends
to zero along `τ = 1/(k+1)` by `modelExt_tendsto_shift`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

theorem shift_aestronglyMeasurable_gradient (hΩo : IsOpen Ω) {f : Vec (n + 1) → ℝ}
    (hf : ContDiffOn ℝ 1 f Ω) : AEStronglyMeasurable (classicalGradient f) (volumeOn Ω) := by
  have hcont : ContinuousOn (fderiv ℝ f) Ω := hf.continuousOn_fderiv_of_isOpen hΩo le_rfl
  have hg : ContinuousOn (classicalGradient f) Ω :=
    continuousOn_pi.2 fun i => hcont.clm_apply continuousOn_const
  exact hg.aestronglyMeasurable hΩo.measurableSet

theorem ExtData.shift_ext_contDiffOn (D : ExtData Ω) {p : ℝ} (hp : 1 < p)
    {g : Vec (n + 1) → ℝ} (hg : IsBesov Ω (1 - 1 / p) p g) : ContDiffOn ℝ 1 (D.ext g) Ω := by
  rw [← D.shift_zero g]
  exact fun x hx => (D.shift_contDiffAt hp hg fun j hj => D.pos_of_mem hx j hj).contDiffWithinAt

/-- Upward shifts of the extension converge to the extension in `W^{1,p}(Ω)`. -/
theorem ExtData.tendsto_shift_w1p (D : ExtData Ω) (hΩo : IsOpen Ω)
    (_hΩb : Bornology.IsBounded Ω) {p : ℝ} (hp : 1 < p) {g : Vec (n + 1) → ℝ}
    (hg : IsBesov Ω (1 - 1 / p) p g) :
    Tendsto (fun k : ℕ => w1pPairNorm Ω p (D.shift (1 / ((k : ℝ) + 1)) g - D.ext g)
      (classicalGradient (D.shift (1 / ((k : ℝ) + 1)) g) - classicalGradient (D.ext g)))
      atTop (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨K, hK0, hpt⟩ := D.exists_shift_pointwise hp hg
  obtain ⟨c, hc, hint⟩ := D.exists_integral_bound hΩo hp hg K hK0
  have hQ : ∀ j : Fin D.A.N, Tendsto (fun k : ℕ => ∫⁻ z in upperHalf n,
      shiftQ (modelExt n (D.flat j g)) p (1 / ((k : ℝ) + 1)) z) atTop (𝓝 0) := fun j =>
    (modelExt_tendsto_shift hp (D.flat_memLp j hp hg) (D.flat_gag_ne_top j hp hg)).comp
      tendsto_shift_inv_nhdsGT
  have hsum : Tendsto (fun k : ℕ => ∑ j, c j * ∫⁻ z in upperHalf n,
      shiftQ (modelExt n (D.flat j g)) p (1 / ((k : ℝ) + 1)) z) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin D.A.N)) fun j _ =>
      ENNReal.Tendsto.const_mul (hQ j) (Or.inr (hc j))
    simpa using this
  have hpow : Tendsto (fun k : ℕ => (∑ j, c j * ∫⁻ z in upperHalf n,
      shiftQ (modelExt n (D.flat j g)) p (1 / ((k : ℝ) + 1)) z) ^ (1 / p)) atTop (𝓝 0) := by
    have := (ENNReal.continuous_rpow_const (y := 1 / p)).tendsto 0 |>.comp hsum
    rwa [ENNReal.zero_rpow_of_pos (by positivity)] at this
  have hfin := hpow.add hpow
  rw [add_zero] at hfin
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hfin
    (fun _ => zero_le) fun k => ?_
  set τ : ℝ := 1 / ((k : ℝ) + 1) with hτdef
  have hτ : 0 < τ := by positivity
  set S := ∑ j, c j * ∫⁻ z in upperHalf n, shiftQ (modelExt n (D.flat j g)) p τ z with hS
  have hcont1 : ContDiffOn ℝ 1 (D.shift τ g) Ω := (D.shift_contDiffOn hp hg hτ).mono subset_closure
  have hcont0 := D.shift_ext_contDiffOn hp hg
  have hm1 : AEStronglyMeasurable (D.shift τ g - D.ext g) (volumeOn Ω) :=
    ((hcont1.continuousOn.sub hcont0.continuousOn).aestronglyMeasurable hΩo.measurableSet)
  have hm2 : AEStronglyMeasurable
      (fun x => vecEuclideanNorm ((classicalGradient (D.shift τ g) - classicalGradient (D.ext g)) x))
      (volumeOn Ω) :=
    (continuous_vecEuclideanNorm (n + 1)).comp_aestronglyMeasurable
      ((shift_aestronglyMeasurable_gradient hΩo hcont1).sub
        (shift_aestronglyMeasurable_gradient hΩo hcont0))
  have e1 : eLpNorm (D.shift τ g - D.ext g) (ENNReal.ofReal p) (volumeOn Ω) ≤ S ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_ofReal_rpow hp0 hm1]
    refine ENNReal.rpow_le_rpow ?_ (by positivity)
    exact hint τ (fun x => (D.shift τ g - D.ext g) x) fun x hx => (hpt τ hτ x hx).1
  have e2 : eLpNorm (fun x => vecEuclideanNorm
      ((classicalGradient (D.shift τ g) - classicalGradient (D.ext g)) x)) (ENNReal.ofReal p)
      (volumeOn Ω) ≤ S ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_ofReal_rpow hp0 hm2]
    refine ENNReal.rpow_le_rpow ?_ (by positivity)
    refine hint τ (fun x => vecEuclideanNorm
      ((classicalGradient (D.shift τ g) - classicalGradient (D.ext g)) x)) fun x hx => ?_
    exact (abs_of_nonneg (vecEuclideanNorm_nonneg _)).le.trans (hpt τ hτ x hx).2
  exact add_le_add e1 e2

end PDE.TraceLane
