module

public import PDEFoundation.Monotonicity.Defs
public import PDEFoundation.Sobolev.Cutoff.Ball
public import PDEFoundation.Geometry.EuclideanBall.Topology

/-!
# Chapter 2 bridge: localization of `C²` functions on a ball

A function that is `C²` on the open ball `euclideanBall 0 R` agrees, on a smaller ball
`euclideanBall 0 ρ'` with `ρ < ρ' < R`, with a globally `C²` function (the product with the
canonical ball cutoff, extended by zero).
-/

@[expose] public section

open Set

namespace PDE

noncomputable section

variable {d : ℕ}

theorem exists_contDiff_localization {u : Vec d → ℝ} {R ρ : ℝ} {n : ℕ}
    (hu : ContDiffOn ℝ n u (euclideanBall 0 R)) (hρ : 0 < ρ) (hρR : ρ < R) :
    ∃ (ρ' : ℝ) (v : Vec d → ℝ), ρ < ρ' ∧ ρ' < R ∧ ContDiff ℝ n v ∧
      EqOn v u (euclideanBall 0 ρ') := by
  set ρ' : ℝ := (ρ + R) / 2 with hρ'
  have h1 : ρ < ρ' := by rw [hρ']; linarith
  have h2 : ρ' < R := by rw [hρ']; linarith
  have hρ'0 : 0 ≤ ρ' := by linarith
  set χ := canonicalBallCutoff (0 : Vec d) ρ' R with hχ
  have hχs : ContDiff ℝ n χ :=
    (canonicalBallCutoff_smooth (0 : Vec d) hρ'0 h2).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hts : tsupport χ ⊆ euclideanBall 0 R :=
    canonicalBallCutoff_tsupport_subset_outer hρ'0 h2
  have hopen : IsOpen (euclideanBall (0 : Vec d) R) := isOpen_euclideanBall 0 R
  refine ⟨ρ', (euclideanBall 0 R).indicator (fun x => χ x * u x), h1, h2, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ euclideanBall (0 : Vec d) R
    · have hat : ContDiffAt ℝ n (fun x => χ x * u x) x :=
        hχs.contDiffAt.mul (hu.contDiffAt (hopen.mem_nhds hx))
      refine hat.congr_of_eventuallyEq ?_
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact indicator_of_mem hy _
    · have hxt : x ∉ tsupport χ := fun h => hx (hts h)
      have hn : (tsupport χ)ᶜ ∈ nhds x := (isClosed_tsupport χ).isOpen_compl.mem_nhds hxt
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hn] with y hy
      by_cases hyb : y ∈ euclideanBall (0 : Vec d) R
      · rw [indicator_of_mem hyb, image_eq_zero_of_notMem_tsupport hy, zero_mul]
      · rw [indicator_of_notMem hyb]
  · intro x hx
    have hxR : x ∈ euclideanBall (0 : Vec d) R := euclideanBall_mono hρ'0 h2.le hx
    simp only [indicator_of_mem hxR]
    have h1x : χ x = 1 := canonicalBallCutoff_eq_one_on_inner hρ'0 h2 hx
    rw [h1x, one_mul]

/-- The localization agrees with `u` on a neighbourhood of the closed ball of radius `ρ`. -/
theorem exists_contDiff_localization_closedBall {u : Vec d → ℝ} {R ρ : ℝ} {n : ℕ}
    (hu : ContDiffOn ℝ n u (euclideanBall 0 R)) (hρ : 0 < ρ) (hρR : ρ < R) :
    ∃ (ρ' : ℝ) (v : Vec d → ℝ), ρ < ρ' ∧ ρ' < R ∧ ContDiff ℝ n v ∧
      EqOn v u (euclideanBall 0 ρ') ∧
      euclideanClosedBall (0 : Vec d) ρ ⊆ euclideanBall 0 ρ' :=
  let ⟨ρ', v, h1, h2, h3, h4⟩ := exists_contDiff_localization hu hρ hρR
  ⟨ρ', v, h1, h2, h3, h4, euclideanClosedBall_subset_euclideanBall hρ.le h1⟩

end

end PDE

