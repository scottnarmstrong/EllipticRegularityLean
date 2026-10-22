module

public import PDEFoundation.Sobolev.Ch4.Lipschitz
public import PDEFoundation.Geometry.EuclideanBall.Topology

/-!
# Lipschitz radial cutoffs

`radialCutoff x₀ r₁ r₂` is the piecewise-linear radial cutoff equal to `1` on the closed
Euclidean ball `|x - x₀| ≤ r₁`, to `0` outside the open Euclidean ball `|x - x₀| < r₂`,
`1/(r₂ - r₁)`-Lipschitz for the Euclidean distance, with values in `[0, 1]` and compact support
inside the closed Euclidean ball of radius `r₂`.
-/

@[expose] public section

open Set

namespace PDE.Ch4Infra

variable {d : ℕ}

/-- The piecewise-linear radial cutoff `max (min ((r₂ - |x - x₀|) / (r₂ - r₁)) 1) 0`. -/
noncomputable def radialCutoff (x₀ : Vec d) (r₁ r₂ : ℝ) : Vec d → ℝ := fun x =>
  max (min ((r₂ - vecEuclideanNorm (x - x₀)) / (r₂ - r₁)) 1) 0

theorem radialCutoff_eucLip (x₀ : Vec d) {r₁ r₂ : ℝ} (h : r₁ < r₂) :
    EucLip (r₂ - r₁)⁻¹ (radialCutoff x₀ r₁ r₂) := by
  have hc : 0 < (r₂ - r₁)⁻¹ := inv_pos.mpr (sub_pos.mpr h)
  have hlin : EucLip (|(-(r₂ - r₁)⁻¹)| * 1)
      (fun x => (-(r₂ - r₁)⁻¹) * vecEuclideanNorm (x - x₀)) :=
    (EucLip.dist_center x₀).smul _
  have hlin' := hlin.add (EucLip.const (r₂ * (r₂ - r₁)⁻¹))
  have hfun : (fun x => (-(r₂ - r₁)⁻¹) * vecEuclideanNorm (x - x₀) + r₂ * (r₂ - r₁)⁻¹) =
      fun x => (r₂ - vecEuclideanNorm (x - x₀)) / (r₂ - r₁) := by
    funext x; field_simp; ring
  rw [hfun] at hlin'
  have h1 := hlin'.min (EucLip.const (1 : ℝ))
  have h2 := h1.max (EucLip.const (0 : ℝ))
  refine h2.mono ?_
  simp [abs_neg, abs_of_pos hc, max_eq_left hc.le]

theorem radialCutoff_nonneg (x₀ : Vec d) (r₁ r₂ : ℝ) (x : Vec d) : 0 ≤ radialCutoff x₀ r₁ r₂ x :=
  le_max_right _ _

theorem radialCutoff_le_one (x₀ : Vec d) (r₁ r₂ : ℝ) (x : Vec d) : radialCutoff x₀ r₁ r₂ x ≤ 1 :=
  max_le (min_le_right _ _) zero_le_one

theorem abs_radialCutoff_le_one (x₀ : Vec d) (r₁ r₂ : ℝ) (x : Vec d) :
    |radialCutoff x₀ r₁ r₂ x| ≤ 1 := by
  rw [abs_of_nonneg (radialCutoff_nonneg x₀ r₁ r₂ x)]; exact radialCutoff_le_one x₀ r₁ r₂ x

theorem radialCutoff_eq_one {x₀ x : Vec d} {r₁ r₂ : ℝ} (h : r₁ < r₂)
    (hx : vecEuclideanNorm (x - x₀) ≤ r₁) : radialCutoff x₀ r₁ r₂ x = 1 := by
  have hpos : 0 < r₂ - r₁ := sub_pos.mpr h
  have : 1 ≤ (r₂ - vecEuclideanNorm (x - x₀)) / (r₂ - r₁) := by
    rw [le_div_iff₀ hpos]; linarith
  simp [radialCutoff, min_eq_right this]

theorem radialCutoff_eq_zero {x₀ x : Vec d} {r₁ r₂ : ℝ} (h : r₁ < r₂)
    (hx : r₂ ≤ vecEuclideanNorm (x - x₀)) : radialCutoff x₀ r₁ r₂ x = 0 := by
  have hpos : 0 < r₂ - r₁ := sub_pos.mpr h
  have : (r₂ - vecEuclideanNorm (x - x₀)) / (r₂ - r₁) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le
  have h2 : min ((r₂ - vecEuclideanNorm (x - x₀)) / (r₂ - r₁)) 1 ≤ 0 :=
    (min_le_left _ _).trans this
  simp [radialCutoff, max_eq_right h2]

theorem tsupport_radialCutoff_subset (x₀ : Vec d) {r₁ r₂ : ℝ} (h : r₁ < r₂) (hr : 0 ≤ r₂) :
    tsupport (radialCutoff x₀ r₁ r₂) ⊆ euclideanClosedBall x₀ r₂ := by
  refine closure_minimal (fun x hx => ?_) (isClosed_euclideanClosedBall x₀ r₂)
  by_contra hxn
  apply hx
  rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr] at hxn
  exact radialCutoff_eq_zero h (not_le.mp hxn).le

theorem hasCompactSupport_radialCutoff (x₀ : Vec d) {r₁ r₂ : ℝ} (h : r₁ < r₂) (hr : 0 ≤ r₂) :
    HasCompactSupport (radialCutoff x₀ r₁ r₂) :=
  (isCompact_euclideanClosedBall x₀ hr).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_radialCutoff_subset x₀ h hr)

end PDE.Ch4Infra
