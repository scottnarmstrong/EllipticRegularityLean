module

public import PDEFoundation.Analysis.Newtonian.Representation.Green

/-!
# Green representation and the divergence-free identity for the Newton kernel

* `green_representation`: `g x = ∫ y, E(x - y) · ∇g(y)` for smooth compactly supported `g`;
* `integral_newtonKernel_dot_eq_zero_of_divergence_eq_zero`: `∫ E(x - y) · Ψ(y) dy = 0` for smooth
  compactly supported `Ψ` with `div Ψ = 0`.

Both follow from the regularized identities by letting `ε → 0⁺`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace PDE

namespace NewtonRepresentation

noncomputable section

variable {d : ℕ}

theorem integrable_newtonKernel_dot (hd : 0 < d) {G : Vec d → Vec d}
    (hG : ∀ i, Continuous fun y => G y i) (hGc : ∀ i, HasCompactSupport fun y => G y i)
    (x : Vec d) : Integrable (fun y => vecDot (newtonKernel (x - y)) (G y)) := by
  unfold vecDot
  exact integrable_finsetSum _ fun i _ => integrable_newtonKernel_apply_mul hd (hG i) (hGc i) i x

theorem tendsto_integral_regKernel_dot (hd : 0 < d) {G : Vec d → Vec d}
    (hG : ∀ i, Continuous fun y => G y i) (hGc : ∀ i, HasCompactSupport fun y => G y i)
    (x : Vec d) :
    Tendsto (fun ε : ℝ => ∫ y, vecDot (regKernel ε (x - y)) (G y)) (𝓝[>] 0)
      (𝓝 (∫ y, vecDot (newtonKernel (x - y)) (G y))) := by
  have h1 : Tendsto (fun ε : ℝ => ∑ i : Fin d, ∫ y, regKernel ε (x - y) i * G y i) (𝓝[>] 0)
      (𝓝 (∑ i : Fin d, ∫ y, newtonKernel (x - y) i * G y i)) :=
    tendsto_finsetSum _ fun i _ => tendsto_integral_regKernel_apply_mul hd (hG i) (hGc i) i x
  have h2 : (∑ i : Fin d, ∫ y, newtonKernel (x - y) i * G y i) =
      ∫ y, vecDot (newtonKernel (x - y)) (G y) := by
    unfold vecDot
    rw [integral_finsetSum _ fun i _ => integrable_newtonKernel_apply_mul hd (hG i) (hGc i) i x]
  rw [h2] at h1
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : ε ≠ 0 := ne_of_gt hε
  unfold vecDot
  rw [integral_finsetSum]
  intro i _
  exact Continuous.integrable_of_hasCompactSupport
    (((contDiff_regKernel_comp hε' i x).continuous).mul (hG i)) (hGc i).mul_left

/-- **Green representation formula.** -/
theorem green_representation (hd : 0 < d) {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) (x : Vec d) :
    g x = ∫ y, vecDot (newtonKernel (x - y)) (classicalGradient g y) := by
  obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hgc
  have hlim := tendsto_integral_regDiv_conv hd hg.continuous
    (fun y => by simpa [Real.norm_eq_abs] using hC y) x
  have hG : ∀ i, Continuous fun y => classicalGradient g y i := fun i =>
    (contDiff_euclideanCoordDeriv hg i).continuous
  have hGc : ∀ i, HasCompactSupport fun y => classicalGradient g y i := fun i =>
    hasCompactSupport_euclideanCoordDeriv hgc i
  have hlim2 := tendsto_integral_regKernel_dot hd hG hGc x
  have hlim3 : Tendsto (fun ε : ℝ => ∫ y, vecDot (regKernel ε (x - y)) (classicalGradient g y))
      (𝓝[>] 0) (𝓝 (g x)) := by
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (integral_regKernel_dot_gradient (ne_of_gt hε) hg hgc x).symm
  exact tendsto_nhds_unique hlim3 hlim2

/-- **Divergence-free fields are orthogonal to the Newton kernel.** -/
theorem integral_newtonKernel_dot_eq_zero_of_divergence_eq_zero (hd : 0 < d) {Ψ : Vec d → Vec d}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨc : HasCompactSupport Ψ)
    (hdiv : ∀ y, classicalDivergence Ψ y = 0) (x : Vec d) :
    ∫ y, vecDot (newtonKernel (x - y)) (Ψ y) = 0 := by
  have hG : ∀ i, Continuous fun y => Ψ y i := fun i => (contDiff_pi.1 hΨ i).continuous
  have hGc : ∀ i, HasCompactSupport fun y => Ψ y i := fun i =>
    hΨc.comp_left (g := fun v : Vec d => v i) rfl
  have hlim := tendsto_integral_regKernel_dot hd hG hGc x
  have hzero : Tendsto (fun ε : ℝ => ∫ y, vecDot (regKernel ε (x - y)) (Ψ y)) (𝓝[>] 0)
      (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (integral_regKernel_dot_divFree (ne_of_gt hε) hΨ hΨc hdiv x).symm
  exact tendsto_nhds_unique hlim hzero

end

end NewtonRepresentation

end PDE
