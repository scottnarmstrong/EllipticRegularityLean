module

public import PDEFoundation.Sobolev.Trace.Model.ExtDefs

/-!
# Differentiability of the dilated kernel in `(z, t)`

For `t ≠ 0` the map `(z, t) ↦ t⁻ⁿ ρ(z / t)` is differentiable with the explicit derivative
`dilFDeriv`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology

/-- The derivative of `(z, t) ↦ t⁻ⁿ ρ(z / t)`. -/
noncomputable def dilFDeriv (n : ℕ) (p : Vec n × ℝ) : Vec n × ℝ →L[ℝ] ℝ :=
  (p.2⁻¹) ^ (n + 1) • ((fderiv ℝ (extKernel n) (p.2⁻¹ • p.1)).comp
      (ContinuousLinearMap.fst ℝ (Vec n) ℝ) +
    extRad n (p.2⁻¹ • p.1) • ContinuousLinearMap.snd ℝ (Vec n) ℝ)

theorem hasFDerivAt_dil_kernel (n : ℕ) {p : Vec n × ℝ} (hp : p.2 ≠ 0) :
    HasFDerivAt (fun q : Vec n × ℝ => dil n (extKernel n) q.1 q.2) (dilFDeriv n p) p := by
  have hc : HasFDerivAt (fun q : Vec n × ℝ => q.2⁻¹)
      ((-(p.2 ^ 2)⁻¹) • ContinuousLinearMap.snd ℝ (Vec n) ℝ) p :=
    (hasDerivAt_inv hp).comp_hasFDerivAt p (hasFDerivAt_snd)
  have h1 := hc.pow n
  have h2 := hc.smul (hasFDerivAt_fst (𝕜 := ℝ) (E := Vec n) (F := ℝ) (p := p))
  have h3 := (((extKernel_contDiff n).differentiable one_ne_zero) (p.2⁻¹ • p.1)).hasFDerivAt.comp
    p h2
  have h4 := h1.mul h3
  refine (h4 : HasFDerivAt (fun q : Vec n × ℝ => dil n (extKernel n) q.1 q.2) _ p).congr_fderiv ?_
  ext u
  · simp only [dilFDeriv, extRad]
    simp
    field_simp
    ring
  · simp only [dilFDeriv, extRad]
    simp
    rcases n with _ | m
    · simp
      field_simp
    · simp only [Nat.add_sub_cancel]
      field_simp
      ring

end PDE.TraceLane
