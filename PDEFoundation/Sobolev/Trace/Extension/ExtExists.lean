module

public import PDEFoundation.Sobolev.Trace.Extension.Defs
import PDEFoundation.Sobolev.Trace.Chart.FactsTopology
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Existence of extension data

Every trace atlas admits cutoffs `ηⱼ`: smooth, compactly supported inside the chart cylinder and
equal to one on the compact support of the partition function `ζⱼ`.
-/

@[expose] public section

namespace PDE.TraceLane

open Set Metric

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

/-- A smooth cutoff, compactly supported in an open set and equal to one on a compact set. -/
theorem ext_exists_cutoff {S U : Set (Vec (n + 1))} (hS : IsCompact S) (hU : IsOpen U)
    (hSU : S ⊆ U) :
    ∃ χ : Vec (n + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      ∀ x ∈ S, χ x = 1 := by
  obtain ⟨r, hr, hrU⟩ := hS.exists_cthickening_subset_open hU hSU
  obtain ⟨χ, hχ, -, hsupp, h1⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    (isOpen_thickening (δ := r) (E := S)) (isClosed_cthickening (δ := r / 2) (E := S))
    (cthickening_subset_thickening' hr (half_lt_self hr) S)
  have hts : tsupport χ ⊆ cthickening r S := by
    rw [tsupport, hsupp]; exact closure_thickening_subset_cthickening r S
  refine ⟨χ, hχ, ?_, hts.trans hrU, fun x hx => ?_⟩
  · exact (hS.cthickening (r := r)).of_isClosed_subset isClosed_closure
      (by simpa [tsupport, hsupp] using closure_thickening_subset_cthickening r S)
  · exact (h1 x).1 (self_subset_cthickening _ hx)

/-- Every trace atlas carries extension data. -/
theorem exists_extData (A : TraceAtlas Ω) : ∃ D : ExtData Ω, D.A = A := by
  choose η hη1 hη2 hη3 hη4 using fun j => ext_exists_cutoff (A.ζ_compact j).isCompact
    (A.chart j).isOpen_dom (A.ζ_tsupport j)
  exact ⟨⟨A, η, hη1, hη2, hη3, hη4⟩, rfl⟩

end PDE.TraceLane
