module

public import PDEFoundation.Sobolev.Trace.Extension.FlatGagliardo

/-!
# The flat Gagliardo bound for the pull-back of an a.e.-measurable boundary function

`flatPullback_gagliardo_le`: for `g` only `σ`-a.e. measurable, replace `g` by a measurable
representative; neither side changes.  Also the identification of the `p`-th power of the
Gagliardo seminorm with the double integral of `flatKerF`, and `n = 0`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped ENNReal NNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

/-- The `p`-th power of the Gagliardo seminorm with `s = 1 - 1/p` as a double integral. -/
theorem gagliardoSeminorm_rpow (Ω : Set (Vec (n + 1))) {p : ℝ} (hp : 0 < p)
    (g : Vec (n + 1) → ℝ) :
    gagliardoSeminorm Ω (1 - 1 / p) p g ^ p =
      ∫⁻ x, ∫⁻ y, flatKerF p ((n : ℝ) + p - 1) g x y ∂boundarySurfaceMeasure Ω
        ∂boundarySurfaceMeasure Ω := by
  unfold gagliardoSeminorm
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]
  have hq : ((n + 1 : ℕ) : ℝ) - 1 + (1 - 1 / p) * p = (n : ℝ) + p - 1 := by
    push_cast
    field_simp
    ring
  simp only [flatKerF, hq]

theorem flat_flatGagliardo_congr_ae (n : ℕ) (q p : ℝ) {w₁ w₂ : Vec n → ℝ}
    (h : w₁ =ᵐ[volume] w₂) : flatGagliardo n q p w₁ = flatGagliardo n q p w₂ := by
  unfold flatGagliardo
  refine lintegral_congr_ae (h.mono fun x' hx' => lintegral_congr_ae (h.mono fun y' hy' => ?_))
  simp only [hx', hy']

theorem flatPullback_ae_eq (φ : GraphChart Ω) {ζ : Vec (n + 1) → ℝ}
    (hζU : tsupport ζ ⊆ φ.dom) {g g' : Vec (n + 1) → ℝ}
    (h : g =ᵐ[boundarySurfaceMeasure Ω] g') :
    flatPullback φ ζ g =ᵐ[volume] flatPullback φ ζ g' := by
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 h)
  have h0 : (volume.restrict (euclideanBall φ.c φ.r))
      ((fun x' => φ.map (x', 0)) ⁻¹' N) = 0 := by
    have := φ.mapBoundary_le_surface N
    rw [Measure.map_apply φ.measurable_boundaryMap hNm] at this
    exact le_antisymm (this.trans hN0.le) bot_le
  have h1 : ∀ᵐ x' ∂(volume.restrict (euclideanBall φ.c φ.r)),
      x' ∉ (fun x' => φ.map (x', 0)) ⁻¹' N := by
    have hset : {a | ¬ a ∉ (fun x' => φ.map (x', 0)) ⁻¹' N} =
        (fun x' => φ.map (x', 0)) ⁻¹' N := by
      ext; simp
    rw [ae_iff, hset]
    exact h0
  rw [ae_restrict_iff' φ.measurableSet_ball] at h1
  filter_upwards [h1] with x' hx'
  by_cases hx : x' ∈ euclideanBall φ.c φ.r
  · have hg : g (φ.map (x', 0)) = g' (φ.map (x', 0)) := by
      by_contra hne
      exact hx' hx (hsub hne)
    simp only [flatPullback, hg]
  · rw [φ.flatPullback_eq_zero_of_notMem hζU g hx, φ.flatPullback_eq_zero_of_notMem hζU g' hx]

/-- **Flat Gagliardo bound for the pull-back.** -/
theorem flatPullback_gagliardo_le (φ : GraphChart Ω) {ζ : Vec (n + 1) → ℝ}
    (hζ : ContDiff ℝ 1 ζ) (hζK : HasCompactSupport ζ) (hζU : tsupport ζ ⊆ φ.dom) {p : ℝ}
    (hp : 1 < p) :
    ∃ C : ℝ≥0, ∀ g : Vec (n + 1) → ℝ, AEMeasurable g (boundarySurfaceMeasure Ω) →
      flatGagliardo n ((n : ℝ) + p - 1) p (flatPullback φ ζ g) ≤
        C * (∫⁻ x, ENNReal.ofReal (|g x| ^ p) ∂boundarySurfaceMeasure Ω +
          gagliardoSeminorm Ω (1 - 1 / p) p g ^ p) := by
  have hp0 : 0 < p := by linarith
  by_cases hn : n = 0
  · subst hn
    exact ⟨0, fun g _ => by rw [flat_flatGagliardo_zero _ hp0]; exact zero_le⟩
  · have : NeZero n := ⟨hn⟩
    obtain ⟨C, hC⟩ := flatGagliardo_le_measurable φ hζ hζK hζU hp
    refine ⟨C, fun g hg => ?_⟩
    have hae : g =ᵐ[boundarySurfaceMeasure Ω] hg.mk g := hg.ae_eq_mk
    have h := hC (hg.mk g) hg.measurable_mk
    rw [gagliardoSeminorm_rpow Ω hp0, flat_flatGagliardo_congr_ae n _ p
      (flatPullback_ae_eq φ hζU hae)]
    have hG : ∫⁻ x, ENNReal.ofReal (|g x| ^ p) ∂boundarySurfaceMeasure Ω =
        ∫⁻ x, ENNReal.ofReal (|hg.mk g x| ^ p) ∂boundarySurfaceMeasure Ω :=
      lintegral_congr_ae (hae.mono fun x hx => by simp only [hx])
    have hS : ∫⁻ x, ∫⁻ y, flatKerF p ((n : ℝ) + p - 1) g x y ∂boundarySurfaceMeasure Ω
        ∂boundarySurfaceMeasure Ω =
        ∫⁻ x, ∫⁻ y, flatKerF p ((n : ℝ) + p - 1) (hg.mk g) x y ∂boundarySurfaceMeasure Ω
        ∂boundarySurfaceMeasure Ω :=
      lintegral_congr_ae (hae.mono fun x hx => lintegral_congr_ae
        (hae.mono fun y hy => by simp only [flatKerF, hx, hy]))
    rw [hG, hS]
    exact h

end PDE.TraceLane
