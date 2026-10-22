module

public import EllipticRegularity.Parabolic.Caccioppoli.Result
public import EllipticRegularity.Parabolic.Caccioppoli.Cutoff

/-!
# Cutoff constructions for the time slice estimate

* a cutoff `ψ` equal to `1` where a given cutoff `φ` does not vanish (for `G < ∞`);
* the square `φ²` as a cutoff, with its time derivative and spatial gradient.
-/

@[expose] public section

namespace PDE.Parabolic.Slice

open MeasureTheory Set Filter Topology Metric PDE

variable {d : ℕ}

/-- A cutoff equal to `1` on the set where `φ ≠ 0`. -/
theorem exists_unit_cutoff (φ : ParCutoff (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)) :
    ∃ ψ : ParCutoff (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
      ∀ z ∈ euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, φ.toFun z ≠ 0 → ψ.toFun z = 1 := by
  obtain ⟨Z, hZc, hZs, hZ0⟩ := φ.compact_support
  set O : Set (Vec d × ℝ) := euclideanBall (0 : Vec d) 1 ×ˢ Ioo (-1 : ℝ) 1 with hO
  have hOo : IsOpen O := (isOpen_euclideanBall _ _).prod isOpen_Ioo
  have hZO : Z ⊆ O := fun z hz => by
    have := hZs hz
    exact ⟨this.1, this.2.1, by linarith [this.2.2]⟩
  obtain ⟨δ, hδ, hδO⟩ := hZc.exists_cthickening_subset_open hOo hZO
  have hd : Disjoint (thickening δ Z)ᶜ Z :=
    Set.disjoint_left.2 fun z hz hzZ => hz (self_subset_thickening hδ Z hzZ)
  obtain ⟨f, hf, -, hfs, hft⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed (n := 1)
    (isOpen_thickening.isClosed_compl) hZc.isClosed hd
  have hf0 : ∀ z, z ∉ thickening δ Z → f z = 0 := fun z hz => (hfs z).1 hz
  have hZ' : IsCompact (cthickening δ Z ∩ (univ ×ˢ Iic (0 : ℝ))) :=
    (hZc.cthickening).inter_right (isClosed_univ.prod isClosed_Iic)
  refine ⟨⟨f, hf, cthickening δ Z ∩ (univ ×ˢ Iic (0 : ℝ)), hZ', ?_, ?_⟩, ?_⟩
  · rintro ⟨x, τ⟩ ⟨hz, hτ⟩
    have := hδO hz
    exact ⟨this.1, this.2.1, hτ.2⟩
  · intro z hz hzn
    apply hf0
    intro hth
    exact hzn ⟨thickening_subset_cthickening δ Z hth, mem_univ _, hz.2.2⟩
  · intro z hz hφ
    have : z ∈ Z := by
      by_contra hn
      exact hφ (hZ0 z hz hn)
    exact (hft z).1 this

/-- The square of a cutoff is a cutoff. -/
def sqCutoff (φ : ParCutoff (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)) :
    ParCutoff (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) where
  toFun := fun z => φ.toFun z ^ 2
  contDiff := φ.contDiff.pow 2
  compact_support := by
    obtain ⟨Z, hZc, hZs, hZ0⟩ := φ.compact_support
    exact ⟨Z, hZc, hZs, fun z hz hzZ => by simp [hZ0 z hz hzZ]⟩

theorem fderiv_sq (φ : Vec d × ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (z : Vec d × ℝ) (e : Vec d × ℝ) :
    fderiv ℝ (fun w => φ w ^ 2) z e = 2 * φ z * fderiv ℝ φ z e := by
  have h1 : HasFDerivAt φ (fderiv ℝ φ z) z := ((hφ.differentiable (by simp)) z).hasFDerivAt
  have h2 : HasFDerivAt (fun w => φ w * φ w) (φ z • fderiv ℝ φ z + φ z • fderiv ℝ φ z) z :=
    h1.mul h1
  have e1 : (fun w => φ w ^ 2) = fun w => φ w * φ w := by funext w; ring
  rw [e1, h2.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem parTimeDeriv_sq (φ : Vec d × ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (z : Vec d × ℝ) :
    parTimeDeriv (fun w => φ w ^ 2) z = 2 * φ z * parTimeDeriv φ z := by
  unfold parTimeDeriv
  exact fderiv_sq φ hφ z _

theorem parSpaceGrad_sq (φ : Vec d × ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (z : Vec d × ℝ) (i : Fin d) :
    parSpaceGrad (fun w => φ w ^ 2) z i = 2 * φ z * parSpaceGrad φ z i := by
  unfold parSpaceGrad
  exact fderiv_sq φ hφ z _

end PDE.Parabolic.Slice
