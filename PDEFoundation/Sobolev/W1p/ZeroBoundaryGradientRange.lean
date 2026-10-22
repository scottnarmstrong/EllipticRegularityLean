module

public import PDEFoundation.Sobolev.W1p.ZeroBoundaryPoincare
public import Mathlib.Analysis.Normed.Operator.Banach

/-! # Closed range of the zero-boundary weak-gradient map -/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory Set

noncomputable section

/-- The graph norm is bounded by a fixed multiple of the weak-gradient norm. -/
theorem W10pGraph.norm_le_max_two_pow_add_one_mul_diameter_one_mul_gradient
    {d : ℕ} (hd : 0 < d) {U : Set (Vec d)} {D q : ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hdiam : HasEuclideanDiameterLE U D) (hD : 0 ≤ D)
    (hq : 1 < q) :
    letI : Fact (1 ≤ ENNReal.ofReal q) :=
      ⟨ENNReal.one_le_ofReal.mpr hq.le⟩
    ∀ u : W10pGraph (p := ENNReal.ofReal q) hU.isOpen,
      ‖u‖ ≤ max (((2 : ℝ) ^ d + 1) * D) 1 *
        ‖w10pGradientCLM (ENNReal.ofReal q) hU.isOpen u‖ := by
  let : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr hq.le⟩
  intro u
  have hval := W10pGraph.norm_fst_le_two_pow_add_one_mul_diameter_norm_snd
    hd hU hdiam hD hq u
  change max ‖(u : W1pGraph U (ENNReal.ofReal q)).1.1‖
      ‖(u : W1pGraph U (ENNReal.ofReal q)).1.2‖ ≤
    max (((2 : ℝ) ^ d + 1) * D) 1 *
      ‖(u : W1pGraph U (ENNReal.ofReal q)).1.2‖
  apply max_le
  · exact hval.trans (mul_le_mul_of_nonneg_right
      (le_max_left (((2 : ℝ) ^ d + 1) * D) 1) (norm_nonneg _))
  · calc
      ‖(u : W1pGraph U (ENNReal.ofReal q)).1.2‖ =
          1 * ‖(u : W1pGraph U (ENNReal.ofReal q)).1.2‖ := by rw [one_mul]
      _ ≤ max (((2 : ℝ) ^ d + 1) * D) 1 *
          ‖(u : W1pGraph U (ENNReal.ofReal q)).1.2‖ :=
        mul_le_mul_of_nonneg_right
          (le_max_right (((2 : ℝ) ^ d + 1) * D) 1) (norm_nonneg _)

/-- The canonical zero-boundary weak-gradient map is anti-Lipschitz with
the constant supplied by the Poincaré inequality. -/
theorem w10pGradientCLM_antilipschitz
    {d : ℕ} (hd : 0 < d) {U : Set (Vec d)} {D q : ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hdiam : HasEuclideanDiameterLE U D) (hD : 0 ≤ D)
    (hq : 1 < q) :
    letI : Fact (1 ≤ ENNReal.ofReal q) :=
      ⟨ENNReal.one_le_ofReal.mpr hq.le⟩
    ∃ K : NNReal,
      AntilipschitzWith K
        (w10pGradientCLM (ENNReal.ofReal q) hU.isOpen) := by
  let : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr hq.le⟩
  let K : NNReal :=
    ⟨max (((2 : ℝ) ^ d + 1) * D) 1, by positivity⟩
  have hbound : ∀ u : W10pGraph (p := ENNReal.ofReal q) hU.isOpen,
      ‖u‖ ≤ (K : ℝ) * ‖w10pGradientCLM (ENNReal.ofReal q) hU.isOpen u‖ := by
    intro u
    change ‖u‖ ≤ max (((2 : ℝ) ^ d + 1) * D) 1 *
      ‖w10pGradientCLM (ENNReal.ofReal q) hU.isOpen u‖
    exact W10pGraph.norm_le_max_two_pow_add_one_mul_diameter_one_mul_gradient
      hd hU hdiam hD hq u
  let T : W10pGraph (p := ENNReal.ofReal q) hU.isOpen →L[ℝ]
      HilbertVectorLp U (ENNReal.ofReal q) :=
    w10pGradientCLM (ENNReal.ofReal q) hU.isOpen
  have hboundT : ∀ u, ‖u‖ ≤ (K : ℝ) * ‖T u‖ := by
    simpa only [T] using hbound
  refine ⟨K, ?_⟩
  exact AntilipschitzWith.of_le_mul_dist fun x y => by
    have hxy : dist x y = ‖x - y‖ := dist_eq_norm x y
    rw [hxy, dist_eq_norm, ← map_sub]
    exact hboundT (x - y)

/-- On a bounded open convex domain, the canonical zero-boundary weak-gradient
map has closed range. -/
theorem w10pGradientCLM_isClosed_range
    {d : ℕ} (hd : 0 < d) {U : Set (Vec d)} {D q : ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hdiam : HasEuclideanDiameterLE U D) (hD : 0 ≤ D)
    (hq : 1 < q) :
    letI : Fact (1 ≤ ENNReal.ofReal q) :=
      ⟨ENNReal.one_le_ofReal.mpr hq.le⟩
    IsClosed (Set.range (w10pGradientCLM (ENNReal.ofReal q) hU.isOpen)) := by
  let : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr hq.le⟩
  obtain ⟨K, hanti⟩ := w10pGradientCLM_antilipschitz hd hU hdiam hD hq
  let S := W10pGraph (p := ENNReal.ofReal q) hU.isOpen
  let : NormedAddCommGroup S := inferInstance
  let : CompleteSpace S := w10pGraphCompleteSpace hU.isOpen
  exact hanti.isClosed_range
    (w10pGradientCLM (ENNReal.ofReal q) hU.isOpen).uniformContinuous

end

end PDE
