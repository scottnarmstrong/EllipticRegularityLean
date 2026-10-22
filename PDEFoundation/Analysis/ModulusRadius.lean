module

public import Mathlib.Topology.Order.LeftRightNhds
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! # Uniform small radii from a prescribed modulus of continuity -/

@[expose] public section

namespace PDE

open Filter Set
open scoped Topology

/-- A modulus tending to zero supplies a positive radius uniform among all
fields controlled by that modulus. No monotonicity of the modulus is needed. -/
theorem exists_small_modulus_radius
    {ω : ℝ → ℝ} (hω0 : ω 0 = 0)
    (hωlim : Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ 2 * r → ω t ≤ δ := by
  have hev : {t : ℝ | ω t < δ} ∈ 𝓝[>] (0 : ℝ) :=
    hωlim (Iio_mem_nhds hδ)
  obtain ⟨s, hs, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hs0 : 0 < s := hs
  refine ⟨min (s / 4) (1 / 4), lt_min (by positivity) (by norm_num),
    min_le_right _ _, ?_⟩
  intro t ht0 htr
  rcases ht0.eq_or_lt with heq | htpos
  · rw [← heq, hω0]
    exact hδ.le
  · have hts : t < s := by
      have hmin := min_le_left (s / 4) (1 / 4 : ℝ)
      linarith only [htr, hmin, hs0]
    exact (hsmall ⟨htpos, hts⟩).le

end PDE
