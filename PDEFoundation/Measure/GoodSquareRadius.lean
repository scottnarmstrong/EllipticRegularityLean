module

public import Mathlib.MeasureTheory.Integral.Average
public import PDEFoundation.Geometry.SquarePoint
public import PDEFoundation.Geometry.SquareShell
public import PDEFoundation.Sobolev.H1.Pairing

/-!
# Good radii for square boundaries

This module fixes the native-`Vec 2` boundary-energy convention used in the
planar good-boundary argument.  The four integrals below are genuinely
tangential: on a vertical side they use coordinate `1` of the vector field,
and on a horizontal side they use coordinate `0`.

For the radius-selection step we deliberately use side segments of the fixed
outer half-side `2 * r`.  They contain the corresponding sides of every
intermediate square of radius `ρ ∈ (r, 2r)`, avoid a variable-limit coarea
formula, and are exactly the rectangular strips to which coordinate Fubini
applies.  The later Fubini lemma will supply its averaged bound from `L²`.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set

noncomputable section

/-- The four-side tangential energy on the square of radius `ρ`, enlarged to
fixed outer side segments of half-length `2 * r`.

The enlargement is intentional and auditable: if `r < ρ < 2r`, each actual
side of the radius-`ρ` square is contained in the parameter interval used
here. -/
def enlargedSquareSideTangentialEnergy
    (g : Vec 2 → Vec 2) (x₀ : Vec 2) (r ρ : ℝ) : ℝ :=
  (∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
      (g (squarePoint (x₀ 0 + ρ) t) 1) ^ 2) +
  (∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
      (g (squarePoint (x₀ 0 - ρ) t) 1) ^ 2) +
  (∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
      (g (squarePoint t (x₀ 1 + ρ)) 0) ^ 2) +
  ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
      (g (squarePoint t (x₀ 1 - ρ)) 0) ^ 2

/-- The actual tangential energy on the four closed sides of the square of
half-side `ρ`.  This is the energy used by the boundary oscillation theorem;
the enlarged energy above is only the fixed-width quantity used to select a
good radius by Fubini. -/
def squareSideTangentialEnergy
    (g : Vec 2 → Vec 2) (x₀ : Vec 2) (ρ : ℝ) : ℝ :=
  (∫ t in Icc (x₀ 1 - ρ) (x₀ 1 + ρ),
      (g (squarePoint (x₀ 0 + ρ) t) 1) ^ 2) +
  (∫ t in Icc (x₀ 1 - ρ) (x₀ 1 + ρ),
      (g (squarePoint (x₀ 0 - ρ) t) 1) ^ 2) +
  (∫ t in Icc (x₀ 0 - ρ) (x₀ 0 + ρ),
      (g (squarePoint t (x₀ 1 + ρ)) 0) ^ 2) +
  ∫ t in Icc (x₀ 0 - ρ) (x₀ 0 + ρ),
      (g (squarePoint t (x₀ 1 - ρ)) 0) ^ 2

/-- Actual four-side tangential energy is nonnegative. -/
theorem squareSideTangentialEnergy_nonneg
    (g : Vec 2 → Vec 2) (x₀ : Vec 2) (ρ : ℝ) :
    0 ≤ squareSideTangentialEnergy g x₀ ρ := by
  unfold squareSideTangentialEnergy
  positivity

/-- The square-shell energy which controls the enlarged boundary energy.
It is stated separately so the selection lemma below is independent of the
subsequent coordinate-Fubini calculation. -/
def squareShellVectorEnergy
    (g : Vec 2 → Vec 2) (x₀ : Vec 2) (r : ℝ) : ℝ :=
  ∫ x in dyadicSquareShell x₀ r, vecNormSq (g x)

/-- The shell energy is integrable under the project's native coordinatewise
`L²` hypothesis.  Thus the only analytic input still needed for a good-radius
theorem is the explicit Fubini/strip comparison, not a trace hypothesis. -/
theorem integrableOn_squareShellVectorEnergy_integrand
    {g : Vec 2 → Vec 2} {x₀ : Vec 2} {r : ℝ}
    (hg : MemVectorL2On (centeredAxisCube x₀ (2 * r)) g) :
    IntegrableOn (fun x => vecNormSq (g x)) (dyadicSquareShell x₀ r) := by
  apply (integrableOn_vecNormSq_of_memVectorL2On hg).mono_set
  intro x hx
  exact hx.1

/-- A purely measure-theoretic good-radius selection principle.  It avoids
an arbitrary null set `N`, which is essential when the four side restrictions
are available only for almost every radius.

The hypothesis `hstrip` is the exact output required from the coordinate
Fubini/strip calculation.  Keeping it explicit prevents this selection lemma
from concealing a trace or measurability assumption. -/
theorem exists_good_square_radius_of_strip_bound
    {B : ℝ → ℝ} {r E : ℝ} {N : Set ℝ}
    (hr : 0 < r)
    (hB : IntegrableOn B (Ioo r (2 * r)))
    (hstrip : ∫ ρ in Ioo r (2 * r), B ρ ≤ 4 * E)
    (hN : volume N = 0) :
    ∃ ρ ∈ Ioo r (2 * r), ρ ∉ N ∧ B ρ ≤ (4 / r) * E := by
  let I : Set ℝ := Ioo r (2 * r)
  have hIpos : volume I ≠ 0 := by
    rw [show I = Ioo r (2 * r) by rfl, Real.volume_Ioo]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  have hNrestrict : (volume.restrict I) N = 0 := by
    rw [Measure.restrict_apply' (measurableSet_Ioo : MeasurableSet I)]
    exact measure_mono_null inter_subset_left hN
  have hIrestrict : volume.restrict I ≠ 0 := by
    intro hzero
    apply hIpos
    calc
      volume I = (volume.restrict I) I :=
        (Measure.restrict_apply_self volume I).symm
      _ = 0 := by simp [hzero]
  have hIcomp : (volume.restrict I) Iᶜ = 0 := by
    rw [Measure.restrict_apply' (measurableSet_Ioo : MeasurableSet I)]
    rw [compl_inter_self]
    exact measure_empty
  have hbad : (volume.restrict I) (N ∪ Iᶜ) = 0 :=
    measure_union_null hNrestrict hIcomp
  obtain ⟨ρ, hρbad, hρ⟩ :=
    exists_notMem_null_le_average hIrestrict
      (by simpa only [I] using! hB) hbad
  have hρI : ρ ∈ I := by
    by_contra hρI
    exact hρbad (Or.inr hρI)
  have hρN : ρ ∉ N := by
    intro hρN
    exact hρbad (Or.inl hρN)
  refine ⟨ρ, hρI, hρN, ?_⟩
  have hmeasure : (volume I).toReal = r := by
    rw [show I = Ioo r (2 * r) by rfl, Real.volume_Ioo,
      ENNReal.toReal_ofReal]
    · ring
    · linarith
  have haverage :
      (⨍ s in I, B s) = (1 / r) * ∫ s in I, B s := by
    rw [MeasureTheory.average_eq]
    simp only [Measure.restrict_apply, MeasurableSet.univ, univ_inter,
      measureReal_def, hmeasure, smul_eq_mul]
    ring
  rw [haverage] at hρ
  have hstrip' : ∫ s in I, B s ≤ 4 * E := by
    simpa only [I] using hstrip
  calc
    B ρ ≤ (1 / r) * ∫ s in I, B s := hρ
    _ ≤ (1 / r) * (4 * E) := by
      exact mul_le_mul_of_nonneg_left hstrip' (by positivity)
    _ = (4 / r) * E := by ring

/-- Good radii for the concrete enlarged four-side tangential energy.

The two hypotheses are precisely the Fubini conclusions for the displayed
four side integrals.  They are intentionally not folded into an unnamed
regularity or trace assumption: the next module can prove them directly from
`MemVectorL2On` by coordinate peeling and then apply this theorem, retaining
the explicit factor `4 / r`. -/
theorem exists_good_enlargedSquare_radius_of_strip_bound
    {g : Vec 2 → Vec 2} {x₀ : Vec 2} {r : ℝ} {N : Set ℝ}
    (hr : 0 < r)
    (hboundary : IntegrableOn
      (enlargedSquareSideTangentialEnergy g x₀ r) (Ioo r (2 * r)))
    (hstrip :
      ∫ ρ in Ioo r (2 * r), enlargedSquareSideTangentialEnergy g x₀ r ρ ≤
        4 * squareShellVectorEnergy g x₀ r)
    (hN : volume N = 0) :
    ∃ ρ ∈ Ioo r (2 * r), ρ ∉ N ∧
      enlargedSquareSideTangentialEnergy g x₀ r ρ ≤
        (4 / r) * squareShellVectorEnergy g x₀ r :=
  exists_good_square_radius_of_strip_bound hr hboundary hstrip hN

end

end PDE
