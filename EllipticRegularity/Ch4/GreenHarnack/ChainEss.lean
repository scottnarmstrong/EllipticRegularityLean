module

public import PDEFoundation.Geometry.EuclideanBall.Topology
public import PDEFoundation.Measure.RestrictedVolume
public import Mathlib.MeasureTheory.Function.EssSup
public import EllipticRegularity.Ch4.GreenHarnack.ChainDef

/-!
# Propagating one-ball Harnack inequalities along a chain

Abstract chaining: if `M y ≤ H m y` for every `y` in `K` and `m y ≤ M y'` whenever
`|y' - y| < s`, then along an `n`-step chain `M x ≤ H^{n+1} m y`. The overlap hypothesis holds
for the essential extrema of any function over the balls `B_s(y)`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4GreenHarnack

open PDE MeasureTheory

variable {d : ℕ}

theorem chain_propagate {K : Set (Vec d)} {s : ℝ} {M m : Vec d → ℝ≥0∞} {H : ℝ≥0∞}
    (hA : ∀ y ∈ K, M y ≤ H * m y)
    (hB : ∀ y ∈ K, ∀ y' ∈ K, vecEuclideanNorm (y' - y) < s → m y ≤ M y')
    {n : ℕ} {x y : Vec d} (h : IsChain K s n x y) : M x ≤ H ^ (n + 1) * m y := by
  obtain ⟨z, hz0, hzn, hzK, hzs⟩ := h
  have key : ∀ i ≤ n, M x ≤ H ^ (i + 1) * m (z i) := by
    intro i
    induction i with
    | zero => intro _; simpa [hz0] using hA x (hz0 ▸ hzK 0 (Nat.zero_le _))
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 : m (z i) ≤ M (z (i + 1)) :=
        hB _ (hzK i (by omega)) _ (hzK (i + 1) hi) (hzs i (by omega))
      calc M x ≤ H ^ (i + 1) * m (z i) := h1
        _ ≤ H ^ (i + 1) * M (z (i + 1)) := by gcongr
        _ ≤ H ^ (i + 1) * (H * m (z (i + 1))) := by gcongr; exact hA _ (hzK _ hi)
        _ = H ^ (i + 1 + 1) * m (z (i + 1)) := by ring
  simpa [hzn] using key n le_rfl

theorem neZero_volumeOn_of_isOpen {U : Set (Vec d)} (hU : IsOpen U) (hne : U.Nonempty) :
    NeZero (volumeOn U) := by
  obtain ⟨x, hx⟩ := hne
  refine ⟨fun h => ?_⟩
  have h1 : 0 < volume U := hU.measure_pos volume ⟨x, hx⟩
  have := Measure.restrict_apply_self volume U
  rw [show volume.restrict U = 0 from h] at this
  simp at this
  exact h1.ne' this.symm

/-- The essential infimum over `B_s(y)` is at most the essential supremum over `B_s(y')` when
`|y' - y| < s`. -/
theorem essInf_le_essSup_of_close (f : Vec d → ℝ≥0∞) {s : ℝ} (hs : 0 < s) {y y' : Vec d}
    (h : vecEuclideanNorm (y' - y) < s) :
    essInf f (volumeOn (euclideanBall y s)) ≤ essSup f (volumeOn (euclideanBall y' s)) := by
  have hy' : y' ∈ euclideanBall y s ∩ euclideanBall y' s :=
    ⟨(mem_euclideanBall_iff_vecEuclideanNorm_lt hs).mpr h, center_mem_euclideanBall y' hs⟩
  have hopen : IsOpen (euclideanBall y s ∩ euclideanBall y' s) :=
    (isOpen_euclideanBall _ _).inter (isOpen_euclideanBall _ _)
  have := neZero_volumeOn_of_isOpen hopen ⟨y', hy'⟩
  have h1 : ∀ᵐ x ∂volumeOn (euclideanBall y s ∩ euclideanBall y' s),
      essInf f (volumeOn (euclideanBall y s)) ≤ f x :=
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left ae_essInf_le
  have h2 : ∀ᵐ x ∂volumeOn (euclideanBall y s ∩ euclideanBall y' s),
      f x ≤ essSup f (volumeOn (euclideanBall y' s)) :=
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right (ENNReal.ae_le_essSup f)
  obtain ⟨x, hx1, hx2⟩ := (h1.and h2).exists
  exact hx1.trans hx2

end PDE.Ch4GreenHarnack
