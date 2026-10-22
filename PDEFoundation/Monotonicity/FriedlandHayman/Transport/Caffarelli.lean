module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Friedland--Hayman: the one-dimensional Caffarelli contraction lemma

Abstract barrier argument.  Suppose `Θ : ℝ → (0, π)` and `w > 0` satisfy
`Θ' = -w / r` and `w' = w * G` with `G = r * cot Θ * w - s`.  Then `w ≤ 1` everywhere.  The
proof is a barrier argument: at a zero of `G` with `w > 1` one has `G' > 0`; hence `G ≥ 0` and `w`
is nondecreasing on a right half-line, forcing `Θ` to leave `(0, π)`.  The left half-line is
handled by the reflection `s ↦ -s`, `Θ ↦ π - Θ`.
-/

@[expose] public section

open Set Filter Topology

namespace PDE.FHLane

namespace Transp

noncomputable section

/-- The logarithmic derivative `G = r * cot Θ * w - s` of `w`. -/
def barG (r : ℝ) (Θ w : ℝ → ℝ) (s : ℝ) : ℝ :=
  r * (Real.cos (Θ s) / Real.sin (Θ s)) * w s - s

/-- The differential system of the Caffarelli lemma. -/
structure CaffData (r : ℝ) (Θ w : ℝ → ℝ) : Prop where
  r_pos : 0 < r
  Θ_pos : ∀ s, 0 < Θ s
  Θ_lt : ∀ s, Θ s < Real.pi
  w_pos : ∀ s, 0 < w s
  dΘ : ∀ s, HasDerivAt Θ (-(w s) / r) s
  dw : ∀ s, HasDerivAt w (w s * barG r Θ w s) s

theorem sin_pos_of_data {r : ℝ} {Θ w : ℝ → ℝ} (h : CaffData r Θ w) (s : ℝ) :
    0 < Real.sin (Θ s) :=
  Real.sin_pos_of_pos_of_lt_pi (h.Θ_pos s) (h.Θ_lt s)

theorem algebra_barG {r a b c w : ℝ} (hr : r ≠ 0) (hs : b ≠ 0) (hab : b ^ 2 + a ^ 2 = 1) :
    r * (((-b) * (-w / r) * b - a * (a * (-w / r))) / b ^ 2) * w +
        r * (a / b) * (w * c) - 1 = w ^ 2 / b ^ 2 + r * (a / b) * (w * c) - 1 := by
  field_simp
  linear_combination w ^ 2 * hab

theorem hasDerivAt_barG {r : ℝ} {Θ w : ℝ → ℝ} (h : CaffData r Θ w) (s : ℝ) :
    HasDerivAt (barG r Θ w)
      (w s ^ 2 / Real.sin (Θ s) ^ 2 +
        r * (Real.cos (Θ s) / Real.sin (Θ s)) * (w s * barG r Θ w s) - 1) s := by
  have hsin := (sin_pos_of_data h s).ne'
  have h1 : HasDerivAt (fun x => Real.cos (Θ x) / Real.sin (Θ x))
      (((-Real.sin (Θ s)) * (-(w s) / r) * Real.sin (Θ s) -
          Real.cos (Θ s) * (Real.cos (Θ s) * (-(w s) / r))) / Real.sin (Θ s) ^ 2) s :=
    (h.dΘ s).cos.div (h.dΘ s).sin hsin
  have h2 := (((h1.const_mul r).mul (h.dw s)).sub (hasDerivAt_id s))
  have e := algebra_barG (r := r) (a := Real.cos (Θ s)) (b := Real.sin (Θ s)) (w := w s)
    (c := barG r Θ w s) h.r_pos.ne' hsin (by rw [Real.sin_sq_add_cos_sq])
  have h3 : HasDerivAt (barG r Θ w) _ s := h2
  refine h3.congr_deriv ?_
  simp only [barG] at e ⊢
  exact e

theorem eventually_gt_right {f : ℝ → ℝ} {f' x : ℝ} (h : HasDerivAt f f' x) (hf' : 0 < f') :
    ∀ᶠ y in 𝓝[>] x, f x < f y := by
  have h1 : Tendsto (slope f x) (𝓝[>] x) (𝓝 f') :=
    (hasDerivAt_iff_tendsto_slope.1 h).mono_left (nhdsWithin_mono _ fun y hy => ne_of_gt hy)
  filter_upwards [h1.eventually (lt_mem_nhds hf'), self_mem_nhdsWithin] with y hy hyx
  rw [slope_def_field] at hy
  have hxy : 0 < y - x := sub_pos.2 hyx
  have := (div_pos_iff_of_pos_right hxy).1 hy
  linarith

theorem barG_nonneg_forward {r : ℝ} {Θ w : ℝ → ℝ} (h : CaffData r Θ w) {s₀ : ℝ}
    (hw : 1 < w s₀) (hG : 0 ≤ barG r Θ w s₀) :
    ∀ x, s₀ ≤ x → 0 ≤ barG r Θ w x ∧ w s₀ ≤ w x := by
  have hGc : Continuous (barG r Θ w) :=
    continuous_iff_continuousAt.2 fun s => (hasDerivAt_barG h s).continuousAt
  have hwc : Continuous w := continuous_iff_continuousAt.2 fun s => (h.dw s).continuousAt
  intro b hb
  have key : Icc s₀ b ⊆ {x | 0 ≤ barG r Θ w x ∧ w s₀ ≤ w x} := by
    refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin ?_ ⟨hG, le_rfl⟩ ?_
    · exact ((isClosed_le continuous_const hGc).inter (isClosed_le continuous_const hwc)).inter
        isClosed_Icc
    · rintro x ⟨⟨hGx, hwx⟩, hx1, -⟩
      have hwx1 : 1 < w x := lt_of_lt_of_le hw hwx
      have hpos : ∀ᶠ y in 𝓝[>] x, 0 < barG r Θ w y := by
        rcases hGx.lt_or_eq with hlt | heq
        · exact (hGc.continuousAt.eventually (lt_mem_nhds hlt)).filter_mono nhdsWithin_le_nhds
        · have hsin := sin_pos_of_data h x
          have hsin1 : Real.sin (Θ x) ^ 2 ≤ 1 := by
            nlinarith [Real.sin_sq_add_cos_sq (Θ x), sq_nonneg (Real.cos (Θ x))]
          have hd := hasDerivAt_barG h x
          have hpd : 0 < w x ^ 2 / Real.sin (Θ x) ^ 2 +
              r * (Real.cos (Θ x) / Real.sin (Θ x)) * (w x * barG r Θ w x) - 1 := by
            rw [← heq, mul_zero, mul_zero, add_zero]
            have : 1 < w x ^ 2 / Real.sin (Θ x) ^ 2 := by
              rw [lt_div_iff₀ (by positivity)]
              nlinarith
            linarith
          filter_upwards [eventually_gt_right hd hpd] with y hy
          rw [← heq] at hy
          exact hy
      obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hpos
      refine mem_nhdsGT_iff_exists_Ioo_subset.2 ⟨u, hu, fun y hy => ?_⟩
      have hmono : MonotoneOn w (Icc x y) := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc x y) hwc.continuousOn
          (fun z _ => (h.dw z).differentiableAt.differentiableWithinAt) ?_
        intro z hz
        rw [interior_Icc] at hz
        rw [(h.dw z).deriv]
        exact mul_nonneg (h.w_pos z).le (hsub ⟨hz.1, hz.2.trans hy.2⟩).le
      exact ⟨(hsub hy).le, hwx.trans (hmono ⟨le_rfl, hy.1.le⟩ ⟨hy.1.le, le_rfl⟩ hy.1.le)⟩
  exact key ⟨hb, le_rfl⟩

theorem no_forward {r : ℝ} {Θ w : ℝ → ℝ} (h : CaffData r Θ w) {s₀ : ℝ}
    (hw : 1 < w s₀) (hG : 0 ≤ barG r Θ w s₀) : False := by
  obtain hmain := barG_nonneg_forward h hw hG
  set w₀ := w s₀ with hw₀
  have hw0 : 0 < w₀ := by linarith
  have hr := h.r_pos
  set F : ℝ → ℝ := fun x => Θ x + (w₀ / r) * x with hF
  have hFd : ∀ x, HasDerivAt F (-(w x) / r + w₀ / r) x := fun x =>
    (h.dΘ x).add (((hasDerivAt_id x).const_mul (w₀ / r)).congr_deriv (by simp))
  have hFc : Continuous F :=
    continuous_iff_continuousAt.2 fun x => (hFd x).continuousAt
  have hanti : AntitoneOn F (Ici s₀) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici s₀) hFc.continuousOn
      (fun z _ => (hFd z).differentiableAt.differentiableWithinAt) ?_
    intro z hz
    rw [interior_Ici] at hz
    rw [(hFd z).deriv]
    have := (hmain z (le_of_lt hz)).2
    have h2 : -(w z) / r + w₀ / r = (w₀ - w z) / r := by ring
    rw [h2]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hr.le
  set x := s₀ + r * Real.pi / w₀ with hx
  have hxs : s₀ ≤ x := by
    have : 0 ≤ r * Real.pi / w₀ := by positivity
    linarith
  have h1 := hanti (le_refl s₀ : s₀ ∈ Ici s₀) (hxs : x ∈ Ici s₀) hxs
  simp only [hF] at h1
  have h2 : w₀ / r * x = w₀ / r * s₀ + Real.pi := by
    rw [hx]
    field_simp
  have := h.Θ_lt s₀
  have := h.Θ_pos x
  linarith

theorem CaffData.reflect {r : ℝ} {Θ w : ℝ → ℝ} (h : CaffData r Θ w) :
    CaffData r (fun s => Real.pi - Θ (-s)) (fun s => w (-s)) where
  r_pos := h.r_pos
  Θ_pos s := by have := h.Θ_lt (-s); show 0 < Real.pi - Θ (-s); linarith
  Θ_lt s := by have := h.Θ_pos (-s); show Real.pi - Θ (-s) < Real.pi; linarith
  w_pos s := h.w_pos (-s)
  dΘ s := by
    have h2 := ((h.dΘ (-s)).comp s (hasDerivAt_neg s)).const_sub Real.pi
    have h3 : HasDerivAt (fun s => Real.pi - Θ (-s)) _ s := h2
    refine h3.congr_deriv ?_
    ring
  dw s := by
    have h1 := ((h.dw (-s)).comp s (hasDerivAt_neg s))
    have h3 : HasDerivAt (fun s => w (-s)) _ s := h1
    refine h3.congr_deriv ?_
    simp only [barG, Real.cos_pi_sub, Real.sin_pi_sub]
    ring

/-- The Caffarelli contraction bound `w ≤ 1`. -/
theorem CaffData.w_le_one {r : ℝ} {Θ w : ℝ → ℝ} (h : CaffData r Θ w) (s₀ : ℝ) : w s₀ ≤ 1 := by
  by_contra hlt
  push Not at hlt
  rcases le_total 0 (barG r Θ w s₀) with hG | hG
  · exact no_forward h hlt hG
  · refine no_forward h.reflect (s₀ := -s₀) (by simpa using hlt) ?_
    have : barG r (fun s => Real.pi - Θ (-s)) (fun s => w (-s)) (-s₀) = -barG r Θ w s₀ := by
      simp only [barG, Real.cos_pi_sub, Real.sin_pi_sub, neg_neg]
      ring
    rw [this]
    linarith

end

end Transp

end PDE.FHLane
