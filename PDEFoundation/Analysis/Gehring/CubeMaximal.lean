module

public import PDEFoundation.Measure.AxisBoxVolume
public import PDEFoundation.Geometry.AxisBox

/-!
# The uncentered maximal function over closed axis cubes

`cubeMaximal k x` is the supremum, over all closed axis-parallel cubes containing `x`, of the
average of `‖k‖`. It takes values in `ℝ≥0∞`, so no integrability is needed to define it.
-/

@[expose] public section

namespace PDE.Gehring

open MeasureTheory Set
open scoped ENNReal

/-- The average of `‖k‖ₑ` over the closed axis cube of center `c` and half-side `r`,
as an extended nonnegative real. -/
noncomputable def cubeAvg {d : ℕ} (k : Vec d → ℝ) (c : Vec d) (r : ℝ) : ℝ≥0∞ :=
  (∫⁻ y in closedCenteredAxisCube c r, ‖k y‖ₑ) / volume (closedCenteredAxisCube c r)

/-- The uncentered maximal function over closed axis-parallel cubes: the supremum of the
averages of `‖k‖ₑ` over closed cubes (of positive side) containing `x`. -/
noncomputable def cubeMaximal {d : ℕ} (k : Vec d → ℝ) (x : Vec d) : ℝ≥0∞ :=
  ⨆ (c : Vec d) (r : ℝ) (_ : 0 < r) (_ : x ∈ closedCenteredAxisCube c r), cubeAvg k c r

theorem cubeAvg_le_cubeMaximal {d : ℕ} (k : Vec d → ℝ) {c : Vec d} {r : ℝ} {x : Vec d}
    (hr : 0 < r) (hx : x ∈ closedCenteredAxisCube c r) :
    cubeAvg k c r ≤ cubeMaximal k x :=
  le_iSup₂_of_le c r <| le_iSup₂_of_le hr hx le_rfl

theorem cubeMaximal_le_iff {d : ℕ} (k : Vec d → ℝ) (x : Vec d) (s : ℝ≥0∞) :
    cubeMaximal k x ≤ s ↔
      ∀ (c : Vec d) (r : ℝ), 0 < r → x ∈ closedCenteredAxisCube c r → cubeAvg k c r ≤ s := by
  unfold cubeMaximal
  simp only [iSup_le_iff]

theorem lt_cubeMaximal_iff {d : ℕ} (k : Vec d → ℝ) (x : Vec d) (s : ℝ≥0∞) :
    s < cubeMaximal k x ↔
      ∃ (c : Vec d) (r : ℝ), 0 < r ∧ x ∈ closedCenteredAxisCube c r ∧ s < cubeAvg k c r := by
  rw [← not_le, cubeMaximal_le_iff]
  push Not
  rfl

theorem cubeMaximal_mono {d : ℕ} {k l : Vec d → ℝ} (h : ∀ y, ‖k y‖ₑ ≤ ‖l y‖ₑ) (x : Vec d) :
    cubeMaximal k x ≤ cubeMaximal l x := by
  rw [cubeMaximal_le_iff]
  intro c r hr hx
  refine le_trans ?_ (cubeAvg_le_cubeMaximal l hr hx)
  exact ENNReal.div_le_div_right (lintegral_mono fun y => h y) _

/-- The average over a closed cube of a function whose `‖·‖ₑ` is bounded by `s` is bounded
by `s`. -/
theorem cubeAvg_le_of_le {d : ℕ} (k : Vec d → ℝ) {c : Vec d} {r : ℝ} (hr : 0 < r) {s : ℝ≥0∞}
    (h : ∀ y, ‖k y‖ₑ ≤ s) : cubeAvg k c r ≤ s := by
  unfold cubeAvg
  have hpos := volume_closedCenteredAxisCube_pos c hr
  have hfin := volume_closedCenteredAxisCube_ne_top c r
  calc (∫⁻ y in closedCenteredAxisCube c r, ‖k y‖ₑ) / volume (closedCenteredAxisCube c r)
      ≤ (∫⁻ _ in closedCenteredAxisCube c r, s) / volume (closedCenteredAxisCube c r) :=
        ENNReal.div_le_div_right (lintegral_mono h) _
    _ = s := by
        rw [setLIntegral_const, ENNReal.mul_div_cancel_right hpos.ne' hfin]

/-- The level sets of the cube maximal function are open. -/
theorem isOpen_lt_cubeMaximal {d : ℕ} (k : Vec d → ℝ) (s : ℝ≥0∞) :
    IsOpen {x | s < cubeMaximal k x} := by
  rw [Metric.isOpen_iff]
  intro x hx
  obtain ⟨c, r, hr, hxc, hs⟩ := (lt_cubeMaximal_iff k x s).1 hx
  -- limit of the enlarged averages
  set I := ∫⁻ y in closedCenteredAxisCube c r, ‖k y‖ₑ with hI
  have hV : volume (closedCenteredAxisCube c r) = ENNReal.ofReal ((2 * r) ^ d) :=
    volume_closedCenteredAxisCube c hr.le
  have hVpos : ENNReal.ofReal ((2 * r) ^ d) ≠ 0 := by
    have := volume_closedCenteredAxisCube_pos c hr
    rw [hV] at this
    exact this.ne'
  have hcont : Filter.Tendsto (fun δ : ℝ => ENNReal.ofReal ((2 * (r + δ)) ^ d))
      (nhdsWithin 0 (Ioi 0)) (nhds (ENNReal.ofReal ((2 * r) ^ d))) := by
    have hc : Continuous fun δ : ℝ => (2 * (r + δ)) ^ d := by fun_prop
    have : Filter.Tendsto (fun δ : ℝ => ENNReal.ofReal ((2 * (r + δ)) ^ d)) (nhds 0)
        (nhds (ENNReal.ofReal ((2 * (r + 0)) ^ d))) :=
      ENNReal.tendsto_ofReal (hc.tendsto 0)
    simp only [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlim : Filter.Tendsto
      (fun δ : ℝ => I / ENNReal.ofReal ((2 * (r + δ)) ^ d))
      (nhdsWithin 0 (Ioi 0)) (nhds (I / ENNReal.ofReal ((2 * r) ^ d))) :=
    ENNReal.Tendsto.div tendsto_const_nhds (Or.inr hVpos) hcont
      (Or.inl ENNReal.ofReal_ne_top)
  have hs' : s < I / ENNReal.ofReal ((2 * r) ^ d) := by
    unfold cubeAvg at hs; rwa [hV] at hs
  obtain ⟨δ, hδ, hδpos⟩ := ((hlim.eventually (lt_mem_nhds hs')).and
    self_mem_nhdsWithin).exists
  have hδpos' : (0 : ℝ) < δ := hδpos
  refine ⟨δ, hδpos', fun x' hx' => ?_⟩
  show s < cubeMaximal k x'
  rw [lt_cubeMaximal_iff]
  refine ⟨c, r + δ, by linarith, ?_, ?_⟩
  · intro i _
    have h1 : |x' i - x i| < δ := by
      have := dist_le_pi_dist x' x i
      rw [Real.dist_eq] at this
      exact lt_of_le_of_lt this hx'
    have h2 := hxc i (mem_univ i)
    simp only [mem_Icc] at h2 ⊢
    have := abs_lt.1 h1
    constructor <;> linarith [h2.1, h2.2, this.1, this.2]
  · refine lt_of_lt_of_le hδ ?_
    unfold cubeAvg
    rw [volume_closedCenteredAxisCube c (by linarith)]
    refine ENNReal.div_le_div_right (lintegral_mono_set ?_) _
    intro y hy i _
    have := hy i (mem_univ i)
    simp only [mem_Icc] at this ⊢
    constructor <;> linarith [this.1, this.2]

end PDE.Gehring
