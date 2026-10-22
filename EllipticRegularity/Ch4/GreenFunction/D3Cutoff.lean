module

public import EllipticRegularity.Ch4.GreenFunction.Caccioppoli
public import EllipticRegularity.Ch4.GreenFunction.Flux

/-!
# Cutoffs for the lower bound of Proposition 4.42

* `fluxCutoff r = radialCutoff 0 (r/2) r`: `1` on `B̄_{r/2}`, `0` outside `B_r`, `(2/r)`-Lipschitz;
  its gradient vanishes unless `r/2 ≤ |x| ≤ r`.
* `shellCutoff r = min (radialCutoff 0 r (4r/3)) (1 - radialCutoff 0 (r/3) (r/2))`: `1` on
  `r/2 ≤ |x| ≤ r`, `0` unless `r/3 < |x| < 4r/3`, `(6/r)`-Lipschitz.
-/

@[expose] public section

open scoped Topology ENNReal

namespace PDE.Ch4Green

open MeasureTheory PDE Filter

variable {d : ℕ}

/-- The squared gradient of a Euclidean-Lipschitz function is bounded by `L²` everywhere. -/
theorem vecNormSq_classicalGradient_le_of_eucLip {L : ℝ} {η : Vec d → ℝ}
    (hη : Ch4Infra.EucLip L η) (hL : 0 ≤ L) (x : Vec d) :
    vecNormSq (classicalGradient η x) ≤ L ^ 2 := by
  rw [← vecEuclideanNorm_sq]
  exact pow_le_pow_left₀ (vecEuclideanNorm_nonneg _)
    (hη.vecEuclideanNorm_classicalGradient_le' hL x) 2

/-- The cutoff used in the flux identity. -/
noncomputable def fluxCutoff (r : ℝ) : Vec d → ℝ := Ch4Infra.radialCutoff 0 (r / 2) r

theorem fluxCutoff_eucLip {r : ℝ} (hr : 0 < r) : Ch4Infra.EucLip (2 / r) (fluxCutoff (d := d) r) :=
    by
  have h := Ch4Infra.radialCutoff_eucLip (0 : Vec d) (show r / 2 < r by linarith)
  refine h.mono (le_of_eq ?_)
  field_simp
  ring

theorem fluxCutoff_eq_one {r : ℝ} (hr : 0 < r) {x : Vec d} (hx : vecEuclideanNorm x ≤ r / 2) :
    fluxCutoff r x = 1 :=
  Ch4Infra.radialCutoff_eq_one (by linarith) (by rwa [sub_zero])

theorem fluxCutoff_eq_zero {r : ℝ} (hr : 0 < r) {x : Vec d} (hx : r ≤ vecEuclideanNorm x) :
    fluxCutoff r x = 0 :=
  Ch4Infra.radialCutoff_eq_zero (by linarith) (by rwa [sub_zero])

theorem classicalGradient_fluxCutoff_eq_zero {r : ℝ} (hr : 0 < r) {x : Vec d}
    (hx : vecEuclideanNorm x < r / 2 ∨ r < vecEuclideanNorm x) :
    classicalGradient (fluxCutoff r) x = 0 := by
  rcases hx with hx | hx
  · refine classicalGradient_eq_zero_of_const (V := euclideanBall (0 : Vec d) (r / 2))
      (isOpen_euclideanBall _ _) (c := 1) (fun y hy => fluxCutoff_eq_one hr ?_) ?_
    · rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith), sub_zero] at hy
      exact hy.le
    · rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith), sub_zero]; exact hx
  · refine classicalGradient_eq_zero_of_const (V := (euclideanClosedBall (0 : Vec d) r)ᶜ)
      (isClosed_euclideanClosedBall _ _).isOpen_compl (c := 0)
      (fun y hy => fluxCutoff_eq_zero hr ?_) ?_
    · rw [Set.mem_compl_iff, mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr.le,
        sub_zero, not_le] at hy
      exact hy.le
    · rw [Set.mem_compl_iff, mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr.le,
        sub_zero, not_le]
      exact hx

theorem tsupport_fluxCutoff_subset {r : ℝ} (hr : 0 < r) :
    tsupport (fluxCutoff (d := d) r) ⊆ euclideanClosedBall 0 r :=
  Ch4Infra.tsupport_radialCutoff_subset 0 (by linarith) hr.le

theorem hasCompactSupport_fluxCutoff {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (fluxCutoff (d := d) r) :=
  Ch4Infra.hasCompactSupport_radialCutoff 0 (by linarith) hr.le

/-- The cutoff used in the Caccioppoli inequality. -/
noncomputable def shellCutoff (r : ℝ) : Vec d → ℝ := fun x =>
  min (Ch4Infra.radialCutoff 0 r (4 * r / 3) x) (1 - Ch4Infra.radialCutoff 0 (r / 3) (r / 2) x)

theorem shellCutoff_eucLip {r : ℝ} (hr : 0 < r) :
    Ch4Infra.EucLip (6 / r) (shellCutoff (d := d) r) := by
  have h1 := Ch4Infra.radialCutoff_eucLip (0 : Vec d) (show r < 4 * r / 3 by linarith)
  have h2 := (Ch4Infra.EucLip.const (d := d) (1 : ℝ)).sub
    (Ch4Infra.radialCutoff_eucLip (0 : Vec d) (show r / 3 < r / 2 by linarith))
  refine (h1.min h2).mono (le_of_eq ?_)
  have e1 : (4 * r / 3 - r)⁻¹ = 3 / r := by field_simp; ring
  have e2 : (0 : ℝ) + (r / 2 - r / 3)⁻¹ = 6 / r := by field_simp; ring
  rw [e1, e2, max_eq_right]
  rw [div_le_div_iff_of_pos_right hr]
  norm_num

theorem abs_shellCutoff_le_one (r : ℝ) (x : Vec d) : |shellCutoff r x| ≤ 1 := by
  unfold shellCutoff
  have a0 := Ch4Infra.radialCutoff_nonneg (0 : Vec d) r (4 * r / 3) x
  have a1 := Ch4Infra.radialCutoff_le_one (0 : Vec d) r (4 * r / 3) x
  have b0 := Ch4Infra.radialCutoff_nonneg (0 : Vec d) (r / 3) (r / 2) x
  have b1 := Ch4Infra.radialCutoff_le_one (0 : Vec d) (r / 3) (r / 2) x
  rw [abs_le]
  constructor
  · exact le_min (by linarith) (by linarith)
  · exact (min_le_left _ _).trans a1

theorem shellCutoff_eq_one {r : ℝ} (hr : 0 < r) {x : Vec d} (h1 : r / 2 ≤ vecEuclideanNorm x)
    (h2 : vecEuclideanNorm x ≤ r) : shellCutoff r x = 1 := by
  unfold shellCutoff
  rw [Ch4Infra.radialCutoff_eq_one (by linarith) (by rwa [sub_zero]),
    Ch4Infra.radialCutoff_eq_zero (by linarith) (by rwa [sub_zero]), sub_zero, min_self]

theorem shellCutoff_eq_zero {r : ℝ} (hr : 0 < r) {x : Vec d}
    (hx : vecEuclideanNorm x ≤ r / 3 ∨ 4 * r / 3 ≤ vecEuclideanNorm x) : shellCutoff r x = 0 := by
  unfold shellCutoff
  rcases hx with hx | hx
  · rw [Ch4Infra.radialCutoff_eq_one (x := x) (show r / 3 < r / 2 by linarith)
      (by rwa [sub_zero]), sub_self]
    exact min_eq_right (Ch4Infra.radialCutoff_nonneg _ _ _ _)
  · rw [Ch4Infra.radialCutoff_eq_zero (x := x) (show r < 4 * r / 3 by linarith)
      (by rwa [sub_zero])]
    exact min_eq_left (by linarith [Ch4Infra.radialCutoff_le_one (0 : Vec d) (r / 3) (r / 2) x])

theorem classicalGradient_shellCutoff_eq_zero {r : ℝ} (hr : 0 < r) {x : Vec d}
    (hx : vecEuclideanNorm x < r / 3 ∨ 4 * r / 3 < vecEuclideanNorm x) :
    classicalGradient (shellCutoff r) x = 0 := by
  rcases hx with hx | hx
  · refine classicalGradient_eq_zero_of_const (V := euclideanBall (0 : Vec d) (r / 3))
      (isOpen_euclideanBall _ _) (c := 0) (fun y hy => shellCutoff_eq_zero hr (Or.inl ?_)) ?_
    · rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith), sub_zero] at hy
      exact hy.le
    · rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith), sub_zero]; exact hx
  · refine classicalGradient_eq_zero_of_const
      (V := (euclideanClosedBall (0 : Vec d) (4 * r / 3))ᶜ)
      (isClosed_euclideanClosedBall _ _).isOpen_compl (c := 0)
      (fun y hy => shellCutoff_eq_zero hr (Or.inr ?_)) ?_
    · rw [Set.mem_compl_iff, mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity),
        sub_zero, not_le] at hy
      exact hy.le
    · rw [Set.mem_compl_iff, mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity),
        sub_zero, not_le]
      exact hx

/-- The support of the shell cutoff lies in `{r/3 ≤ |x| ≤ 4r/3}`. -/
theorem tsupport_shellCutoff_subset {r : ℝ} (hr : 0 < r) :
    tsupport (shellCutoff (d := d) r) ⊆
      euclideanClosedBall 0 (4 * r / 3) \ euclideanBall 0 (r / 3) := by
  refine closure_minimal (fun x hx => ?_) ?_
  · by_contra hxn
    apply hx
    refine shellCutoff_eq_zero hr ?_
    rw [Set.mem_sdiff, mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity),
      mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity), sub_zero] at hxn
    by_cases h : vecEuclideanNorm x ≤ 4 * r / 3
    · left
      by_contra h'
      exact hxn ⟨h, fun h'' => h' h''.le⟩
    · exact Or.inr (le_of_lt (not_le.1 h))
  · exact (isClosed_euclideanClosedBall _ _).sdiff (isOpen_euclideanBall _ _)

theorem hasCompactSupport_shellCutoff {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (shellCutoff (d := d) r) :=
  (isCompact_euclideanClosedBall 0 (by positivity : (0 : ℝ) ≤ 4 * r / 3)).of_isClosed_subset
    (isClosed_tsupport _) ((tsupport_shellCutoff_subset hr).trans Set.sdiff_subset)

end PDE.Ch4Green
