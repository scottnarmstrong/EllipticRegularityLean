module

public import PDEFoundation.Monotonicity.FriedlandHayman.Transport.Weights
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Friedland--Hayman: the transport map

`capInv D` is the inverse of the cap fraction on `(0, 1)`.  The transport map
`Θ s = capInv D (gaussTail s)` is a strictly decreasing `C¹` bijection of `ℝ` onto `(0, π)`
with `Θ' s = -(zTot D / gTot) * gaussW s / sinW D (Θ s)`.
-/

@[expose] public section

open Set Filter Topology

namespace PDE.FHLane

namespace Transp

noncomputable section

/-- Inverse of the cap fraction (a junk value off `[0, 1]`). -/
def capInv (D : ℕ) (v : ℝ) : ℝ :=
  Classical.epsilon fun φ => φ ∈ Set.Icc (0 : ℝ) Real.pi ∧ capFrac D φ = v

theorem exists_capInv (D : ℕ) {v : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) Real.pi, capFrac D φ = v := by
  have h := intermediate_value_Icc Real.pi_pos.le (continuous_capFrac D).continuousOn
  rw [capFrac_zero, capFrac_pi] at h
  obtain ⟨φ, hφ, hφv⟩ := h ⟨hv.1.le, hv.2.le⟩
  refine ⟨φ, ⟨lt_of_le_of_ne hφ.1 ?_, lt_of_le_of_ne hφ.2 ?_⟩, hφv⟩
  · rintro rfl
    rw [capFrac_zero] at hφv
    exact hv.1.ne hφv
  · rintro rfl
    rw [capFrac_pi] at hφv
    exact hv.2.ne hφv.symm

theorem capInv_spec (D : ℕ) {v : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) 1) :
    capInv D v ∈ Set.Ioo (0 : ℝ) Real.pi ∧ capFrac D (capInv D v) = v := by
  obtain ⟨φ, hφ, hφv⟩ := exists_capInv D hv
  obtain ⟨hm, hv'⟩ : capInv D v ∈ Set.Icc (0 : ℝ) Real.pi ∧ capFrac D (capInv D v) = v :=
    Classical.epsilon_spec (p := fun φ => φ ∈ Set.Icc (0 : ℝ) Real.pi ∧ capFrac D φ = v)
      ⟨φ, Ioo_subset_Icc_self hφ, hφv⟩
  refine ⟨⟨lt_of_le_of_ne hm.1 ?_, lt_of_le_of_ne hm.2 ?_⟩, hv'⟩
  · intro h0
    rw [← h0, capFrac_zero] at hv'
    exact hv.1.ne hv'
  · intro h0
    rw [h0, capFrac_pi] at hv'
    exact hv.2.ne hv'.symm

theorem capInv_capFrac (D : ℕ) {φ : ℝ} (hφ : φ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    capInv D (capFrac D φ) = φ := by
  have hv : capFrac D φ ∈ Set.Ioo (0 : ℝ) 1 := by
    have := strictMonoOn_capFrac D
    constructor
    · simpa using this ⟨le_rfl, Real.pi_pos.le⟩ (Ioo_subset_Icc_self hφ) hφ.1
    · simpa [capFrac_pi] using this (Ioo_subset_Icc_self hφ) ⟨Real.pi_pos.le, le_rfl⟩ hφ.2
  obtain ⟨hm, hs⟩ := capInv_spec D hv
  exact (strictMonoOn_capFrac D).injOn (Ioo_subset_Icc_self hm) (Ioo_subset_Icc_self hφ) hs

theorem capFrac_mem_Ioo (D : ℕ) {φ : ℝ} (hφ : φ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    capFrac D φ ∈ Set.Ioo (0 : ℝ) 1 := by
  have := strictMonoOn_capFrac D
  constructor
  · simpa using this ⟨le_rfl, Real.pi_pos.le⟩ (Ioo_subset_Icc_self hφ) hφ.1
  · simpa [capFrac_pi] using this (Ioo_subset_Icc_self hφ) ⟨Real.pi_pos.le, le_rfl⟩ hφ.2

theorem capInv_strictMonoOn (D : ℕ) : StrictMonoOn (capInv D) (Set.Ioo 0 1) := by
  intro a ha b hb hab
  by_contra hle
  push Not at hle
  have h1 := capInv_spec D ha
  have h2 := capInv_spec D hb
  have := (strictMonoOn_capFrac D).monotoneOn (Ioo_subset_Icc_self h2.1)
    (Ioo_subset_Icc_self h1.1) hle
  rw [h1.2, h2.2] at this
  exact absurd hab (not_lt.2 this)

theorem continuousAt_capInv (D : ℕ) {v : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) 1) :
    ContinuousAt (capInv D) v := by
  refine continuousAt_of_monotoneOn_of_image_mem_nhds (s := Set.Ioo 0 1)
    (capInv_strictMonoOn D).monotoneOn (isOpen_Ioo.mem_nhds hv) ?_
  refine mem_of_superset (isOpen_Ioo.mem_nhds (capInv_spec D hv).1) ?_
  intro φ hφ
  exact ⟨capFrac D φ, capFrac_mem_Ioo D hφ, capInv_capFrac D hφ⟩

theorem hasDerivAt_capInv (D : ℕ) {v : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (capInv D) (sinW D (capInv D v) / zTot D)⁻¹ v := by
  obtain ⟨hm, hs⟩ := capInv_spec D hv
  refine HasDerivAt.of_local_left_inverse (f := capFrac D) (continuousAt_capInv D hv)
    (hasDerivAt_capFrac D _) ?_ ?_
  · exact (div_pos (sinW_pos hm) (zTot_pos D)).ne'
  · filter_upwards [isOpen_Ioo.mem_nhds hv] with y hy
    exact (capInv_spec D hy).2

/-- The transport map from the Gaussian line to the angle. -/
def tmap (D : ℕ) (s : ℝ) : ℝ := capInv D (gaussTail s)

theorem gaussTail_mem (s : ℝ) : gaussTail s ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨gaussTail_pos s, gaussTail_lt_one s⟩

theorem tmap_mem (D : ℕ) (s : ℝ) : tmap D s ∈ Set.Ioo (0 : ℝ) Real.pi :=
  (capInv_spec D (gaussTail_mem s)).1

theorem capFrac_tmap (D : ℕ) (s : ℝ) : capFrac D (tmap D s) = gaussTail s :=
  (capInv_spec D (gaussTail_mem s)).2

theorem hasDerivAt_tmap (D : ℕ) (s : ℝ) :
    HasDerivAt (tmap D) (-(zTot D / gTot) * gaussW s / sinW D (tmap D s)) s := by
  have h := (hasDerivAt_capInv D (gaussTail_mem s)).comp s (hasDerivAt_gaussTail s)
  have hz := (sinW_pos (D := D) (tmap_mem D s)).ne'
  have hzt := (zTot_pos D).ne'
  have hg := gTot_pos.ne'
  refine h.congr_deriv ?_
  unfold tmap
  field_simp

theorem tmap_strictAnti (D : ℕ) : StrictAnti (tmap D) := by
  intro a b hab
  exact capInv_strictMonoOn D (gaussTail_mem b) (gaussTail_mem a) (strictAnti_gaussTail hab)

theorem exists_tmap_eq (D : ℕ) {φ : ℝ} (hφ : φ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    ∃ s, tmap D s = φ := by
  have hv := capFrac_mem_Ioo D hφ
  obtain ⟨a, ha⟩ := (tendsto_gaussTail_atBot.eventually (lt_mem_nhds hv.2)).exists
  obtain ⟨b, hb⟩ := (tendsto_gaussTail_atTop.eventually (gt_mem_nhds hv.1)).exists
  have h := intermediate_value_uIcc (a := a) (b := b) continuous_gaussTail.continuousOn
  have hmem : capFrac D φ ∈ uIcc (gaussTail a) (gaussTail b) := by
    rw [uIcc_of_ge (le_of_lt (hb.trans ha))]
    exact ⟨hb.le, ha.le⟩
  obtain ⟨s, -, hs⟩ := h hmem
  refine ⟨s, ?_⟩
  unfold tmap
  rw [hs]
  exact capInv_capFrac D hφ

end

end Transp

end PDE.FHLane
