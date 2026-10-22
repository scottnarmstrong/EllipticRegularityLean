module

public import PDEFoundation.Sobolev.Trace.Density.LocalMollify
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Extension by zero across a closed set

Let `Ω` be open, `K` closed, and let `g` be the weak `i`-th derivative of `u` on `Ω`, with `u` and
`g` vanishing on `Ω \ K`.  Then the zero extensions `Ω.indicator u`, `Ω.indicator g` satisfy the
weak derivative identity on the larger open set `Ω ∪ Kᶜ`: a test function there is split by a
smooth cutoff, equal to `1` near the compact set `tsupport φ ∩ K ⊆ Ω`, into a part supported in
`Ω` and a part on which both sides vanish identically.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology Metric

variable {d : ℕ}

/-- A smooth cutoff, compactly supported in an open set, equal to `1` near a compact subset. -/
theorem exists_cutoff_near_compact {S Ω : Set (Vec d)} (hS : IsCompact S) (hΩ : IsOpen Ω)
    (hSΩ : S ⊆ Ω) :
    ∃ χ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ω ∧
      ∀ x ∈ S, ∀ᶠ y in 𝓝 x, χ y = 1 := by
  obtain ⟨r, hr, hrΩ⟩ := hS.exists_cthickening_subset_open hΩ hSΩ
  obtain ⟨χ, hχ, -, hsupp, h1⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    (isOpen_thickening (δ := r) (E := S)) (isClosed_cthickening (δ := r / 2) (E := S))
    (cthickening_subset_thickening' hr (by linarith) S)
  have hts : tsupport χ ⊆ cthickening r S := by
    rw [tsupport, hsupp]; exact closure_thickening_subset_cthickening r S
  refine ⟨χ, hχ, ?_, hts.trans hrΩ, fun x hx => ?_⟩
  · exact (hS.cthickening (r := r)).of_isClosed_subset isClosed_closure
      (by simpa [tsupport, hsupp] using closure_thickening_subset_cthickening r S)
  · have hopen : IsOpen (thickening (r / 2) S) := isOpen_thickening
    filter_upwards [hopen.mem_nhds (self_subset_thickening (by linarith) S hx)] with y hy
    exact (h1 y).1 (thickening_subset_cthickening _ _ hy)

/-- Extension by zero of a weak derivative across a closed set. -/
theorem hasWeakPartialDerivOn_indicator_union_compl {Ω K : Set (Vec d)} (hΩ : IsOpen Ω)
    (hK : IsClosed K) {i : Fin d} {u g : Vec d → ℝ} (h : HasWeakPartialDerivOn Ω i u g)
    (hu0 : ∀ x ∈ Ω, x ∉ K → u x = 0) (hg0 : ∀ x ∈ Ω, x ∉ K → g x = 0) :
    HasWeakPartialDerivOn (Ω ∪ Kᶜ) i (Ω.indicator u) (Ω.indicator g) := by
  intro φ hφ hφc hφO
  have hSc : IsCompact (tsupport φ ∩ K) := hφc.inter_right hK
  have hSΩ : tsupport φ ∩ K ⊆ Ω := by
    rintro x ⟨hx1, hx2⟩
    rcases hφO hx1 with hx | hx
    · exact hx
    · exact absurd hx2 hx
  obtain ⟨χ, hχ, hχc, hχΩ, hχ1⟩ := exists_cutoff_near_compact hSc hΩ hSΩ
  set ψ : Vec d → ℝ := fun x => χ x * φ x with hψdef
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hχ.mul hφ
  have hψc : HasCompactSupport ψ := hχc.mul_right
  have hψΩ : tsupport ψ ⊆ Ω := tsupport_mul_subset_left.trans hχΩ
  -- `φ` and `ψ` agree near every point of `K`
  have hnear : ∀ x ∈ K, φ =ᶠ[𝓝 x] ψ := by
    intro x hxK
    by_cases hx : x ∈ tsupport φ
    · filter_upwards [hχ1 x ⟨hx, hxK⟩] with y hy
      simp [ψ, hy]
    · have h0 : φ =ᶠ[𝓝 x] 0 :=
        (isClosed_tsupport φ).isOpen_compl.eventually_mem hx |>.mono
          (fun y hy => image_eq_zero_of_notMem_tsupport hy)
      filter_upwards [h0] with y hy
      simp [ψ, hy]
  have e1 : (fun x => Ω.indicator u x * fderiv ℝ φ x (basisVec i)) =
      Ω.indicator (fun x => u x * fderiv ℝ ψ x (basisVec i)) := by
    funext x
    by_cases hx : x ∈ Ω
    · by_cases hxK : x ∈ K
      · simp only [indicator_of_mem hx, (hnear x hxK).fderiv_eq]
      · simp [indicator_of_mem hx, hu0 x hx hxK]
    · simp [indicator_of_notMem hx]
  have e2 : (fun x => Ω.indicator g x * φ x) = Ω.indicator (fun x => g x * ψ x) := by
    funext x
    by_cases hx : x ∈ Ω
    · by_cases hxK : x ∈ K
      · simp only [indicator_of_mem hx, (hnear x hxK).eq_of_nhds]
      · simp [indicator_of_mem hx, hg0 x hx hxK]
    · simp [indicator_of_notMem hx]
  have hinter : (Ω ∪ Kᶜ) ∩ Ω = Ω := inter_eq_right.2 subset_union_left
  have hw := h ψ hψ hψc hψΩ
  rw [e1, e2, setIntegral_indicator hΩ.measurableSet, setIntegral_indicator hΩ.measurableSet,
    hinter]
  exact hw

/-- Gradient form of `hasWeakPartialDerivOn_indicator_union_compl`. -/
theorem hasWeakGradientOn_indicator_union_compl {Ω K : Set (Vec d)} (hΩ : IsOpen Ω)
    (hK : IsClosed K) {u : Vec d → ℝ} {g : Vec d → Vec d} (h : HasWeakGradientOn Ω u g)
    (hu0 : ∀ x ∈ Ω, x ∉ K → u x = 0) (hg0 : ∀ x ∈ Ω, x ∉ K → g x = 0) :
    HasWeakGradientOn (Ω ∪ Kᶜ) (Ω.indicator u) (Ω.indicator g) := by
  intro i
  have := hasWeakPartialDerivOn_indicator_union_compl hΩ hK (h i) hu0
    (fun x hx hxK => by simp [hg0 x hx hxK])
  convert this using 2
  rename_i x
  by_cases hx : x ∈ Ω <;> simp [hx]

end PDE.TraceLane
