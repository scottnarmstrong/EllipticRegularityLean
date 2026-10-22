module

public import PDEFoundation.Geometry.C1Boundary
public import PDEFoundation.Analysis.HilbertDictionary

/-!
# `C¹` boundaries on a general normed space

`HasC1Frontier E` is the notion `PDE.HasC1Boundary` transcribed verbatim to an arbitrary
real normed space; `hasC1Frontier_toHilbertVec` transports it from `Vec d` to the Euclidean
realisation `HilbertVec d`, where the isoperimetric argument is carried out.
-/

@[expose] public section

namespace PDE.IsoperimetricProof

open Set

/-- `E` has `C¹` boundary in the sense of `PDE.HasC1Boundary`, on a general real normed space. -/
def HasC1Frontier {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (E : Set V) : Prop :=
  ∀ x ∈ frontier E, ∃ W : Set V, IsOpen W ∧ x ∈ W ∧
    ∃ φ : V → ℝ, ContDiff ℝ 1 φ ∧ (∀ y ∈ W, fderiv ℝ φ y ≠ 0) ∧
      E ∩ W = {y | y ∈ W ∧ φ y < 0}

/-- A `C¹` boundary is preserved by a continuous linear equivalence. -/
theorem HasC1Frontier.image_equiv {V U : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup U] [NormedSpace ℝ U] (e : V ≃L[ℝ] U) {E : Set V}
    (hE : HasC1Frontier E) : HasC1Frontier (e '' E) := by
  intro x hx
  have himg : frontier (e '' E) = e '' frontier E := (e.toHomeomorph.image_frontier E).symm
  rw [himg] at hx
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨W, hW, hxW, φ, hφ, hdφ, hEW⟩ := hE x hx
  refine ⟨e '' W, e.toHomeomorph.isOpenMap W hW, mem_image_of_mem _ hxW, φ ∘ e.symm,
    hφ.comp e.symm.contDiff, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩ h0
    have hcomp : fderiv ℝ (φ ∘ e.symm) (e y) =
        (fderiv ℝ φ (e.symm (e y))).comp (e.symm : U →L[ℝ] V) :=
      e.symm.comp_right_fderiv (f := φ) (x := e y)
    rw [hcomp, e.symm_apply_apply] at h0
    apply hdφ y hy
    ext v
    have := congrArg (fun L : U →L[ℝ] ℝ => L (e v)) h0
    simpa using this
  · ext z
    constructor
    · rintro ⟨⟨y, hyE, rfl⟩, ⟨y', hy'W, hyy'⟩⟩
      have hy : y = y' := e.injective hyy'.symm
      subst hy
      have : y ∈ E ∩ W := ⟨hyE, hy'W⟩
      rw [hEW] at this
      exact ⟨⟨y, this.1, rfl⟩, by simpa using this.2⟩
    · rintro ⟨⟨y, hyW, rfl⟩, hneg⟩
      have : y ∈ {y | y ∈ W ∧ φ y < 0} := ⟨hyW, by simpa using hneg⟩
      rw [← hEW] at this
      exact ⟨⟨y, this.1, rfl⟩, ⟨y, hyW, rfl⟩⟩

/-- Transport of the `C¹`-boundary notion to the Euclidean realisation. -/
theorem hasC1Frontier_toHilbertVec {d : ℕ} {E : Set (Vec d)} (hE : HasC1Boundary E) :
    HasC1Frontier (Vec.toHilbertVec '' E) := by
  have h : HasC1Frontier E := hE
  have himg : (Internal.toHilbert : Vec d → HilbertVec d) '' E = Vec.toHilbertVec '' E := rfl
  rw [← himg]
  exact h.image_equiv (Internal.toHilbert (d := d))

end PDE.IsoperimetricProof
