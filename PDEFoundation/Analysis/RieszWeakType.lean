module

public import PDEFoundation.Analysis.RieszWeakTypeRadial
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Measure.Prod

/-! # Weak-type `(1, d/(d-1))` bound for the Riesz potential `I₁`

`rieszKernelOne z = |z| ^ (1 - d)` and `I₁ f x = ∫ |x - y| ^ (1 - d) f(y) dy`, with the
Euclidean norm `vecEuclideanNorm`. The bound is proved first for the extended-valued
Lebesgue-integral form `rieszLIntegralOne`, then transferred to the Bochner form
`rieszPotentialOne`.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory Set

namespace PDE

noncomputable section

variable {d : ℕ}

/-- The Riesz kernel `|z| ^ (1 - d)` of order one, with the Euclidean norm. -/
def rieszKernelOne (d : ℕ) (z : Vec d) : ℝ :=
  vecEuclideanNorm z ^ ((1 : ℝ) - d)

/-- The Riesz potential `I₁ f x = ∫ |x - y| ^ (1 - d) f y dy` (Bochner form). -/
def rieszPotentialOne (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∫ y, rieszKernelOne d (x - y) * f y

/-- The Riesz potential of a nonnegative function in `[0, ∞]`-valued form. -/
def rieszLIntegralOne (f : Vec d → ℝ) (x : Vec d) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (rieszKernelOne d (x - y)) * ENNReal.ofReal (f y)

theorem measurable_rieszKernelOne : Measurable (rieszKernelOne d) :=
  measurable_vecEuclideanNorm.pow_const _

theorem rieszKernelOne_nonneg (z : Vec d) : 0 ≤ rieszKernelOne d z :=
  Real.rpow_nonneg (Real.sqrt_nonneg _) _

/-- The kernel is monotone decreasing in the radius. -/
theorem rieszKernelOne_le_of_le {δ : ℝ} (hd : 2 ≤ d) (hδ : 0 < δ) {z : Vec d}
    (hz : δ ≤ vecEuclideanNorm z) : rieszKernelOne d z ≤ δ ^ ((1 : ℝ) - d) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  exact Real.rpow_le_rpow_of_nonpos hδ hz (by linarith)

/-- `∫_{B_R} |z|^{1-d} dz = d |B₁| R` for the ball centered at `0`. -/
theorem lintegral_euclideanBall_rieszKernelOne (hd : 2 ≤ d) {R : ℝ} (hR : 0 < R) :
    ∫⁻ z in euclideanBall (0 : Vec d) R, ENNReal.ofReal (rieszKernelOne d z) =
      ENNReal.ofReal ((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal * R) := by
  have : NeZero d := ⟨by omega⟩
  exact lintegral_euclideanBall_rieszKernel hR

/-- The same identity centered at an arbitrary point `y`. -/
theorem lintegral_euclideanBall_rieszKernelOne_center (hd : 2 ≤ d) (y : Vec d) {R : ℝ}
    (hR : 0 < R) :
    ∫⁻ x in euclideanBall y R, ENNReal.ofReal (rieszKernelOne d (x - y)) =
      ENNReal.ofReal ((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal * R) := by
  rw [← lintegral_euclideanBall_rieszKernelOne hd hR]
  have hmeas := (isOpen_euclideanBall (0 : Vec d) R).measurableSet
  have h := lintegral_sub_right_eq_self (μ := (volume : Measure (Vec d)))
    ((euclideanBall (0 : Vec d) R).indicator
      (fun z => ENNReal.ofReal (rieszKernelOne d z))) y
  rw [lintegral_indicator hmeas] at h
  rw [← h, ← lintegral_indicator (isOpen_euclideanBall y R).measurableSet]
  refine lintegral_congr fun x => ?_
  have : x ∈ euclideanBall y R ↔ x - y ∈ euclideanBall (0 : Vec d) R := by
    simp [mem_euclideanBall_iff_vecEuclideanNorm_lt hR]
  by_cases hx : x ∈ euclideanBall y R
  · simp [hx, this.mp hx]
  · simp [hx, mt this.mpr hx]

/-- `∫_V |x - y|^{1-d} dx ≤ d |B₁| D` when `V` lies in the closed ball of radius `D` about `y`
(for instance when `y ∈ V` and `V` has Euclidean diameter at most `D`). -/
theorem lintegral_rieszKernelOne_le_of_subset_closedBall (hd : 2 ≤ d) (y : Vec d) {D : ℝ}
    (hD : 0 < D) {V : Set (Vec d)} (hV : V ⊆ euclideanClosedBall y D) :
    ∫⁻ x in V, ENNReal.ofReal (rieszKernelOne d (x - y)) ≤
      ENNReal.ofReal ((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal * D) := by
  set c : ℝ := (d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal with hc
  have hε : ∀ ε : ℝ, 0 < ε → ∫⁻ x in V, ENNReal.ofReal (rieszKernelOne d (x - y)) ≤
      ENNReal.ofReal (c * (D + ε)) := by
    intro ε hε
    have hsub : V ⊆ euclideanBall y (D + ε) := by
      intro x hx
      have h1 := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hD.le).mp (hV hx)
      rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith)]
      linarith
    calc _ ≤ ∫⁻ x in euclideanBall y (D + ε), ENNReal.ofReal (rieszKernelOne d (x - y)) :=
          lintegral_mono_set hsub
      _ = _ := lintegral_euclideanBall_rieszKernelOne_center hd y (by linarith)
  have hlim : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal (c * (D + ε)))
      (nhdsWithin 0 (Ioi 0)) (nhds (ENNReal.ofReal (c * D))) := by
    have : Filter.Tendsto (fun ε : ℝ => c * (D + ε)) (nhds 0) (nhds (c * (D + 0))) :=
      (continuous_const.mul (continuous_const.add continuous_id)).tendsto 0
    rw [add_zero] at this
    exact (ENNReal.tendsto_ofReal this).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε' => hε ε hε')

/-- Real form: the kernel is integrable over `V` with `∫_V |x-y|^{1-d} dx ≤ d |B₁| D`. -/
theorem integrableOn_rieszKernelOne_of_subset_closedBall (hd : 2 ≤ d) (y : Vec d) {D : ℝ}
    (hD : 0 < D) {V : Set (Vec d)} (hV : V ⊆ euclideanClosedBall y D) :
    IntegrableOn (fun x => rieszKernelOne d (x - y)) V := by
  refine ⟨(measurable_rieszKernelOne.comp (measurable_id.sub_const y)).aestronglyMeasurable, ?_⟩
  have := lintegral_rieszKernelOne_le_of_subset_closedBall hd y hD hV
  refine lt_of_le_of_lt ?_ (lt_of_le_of_lt this ENNReal.ofReal_lt_top)
  refine le_of_eq (lintegral_congr fun x => ?_)
  rw [Real.enorm_eq_ofReal (rieszKernelOne_nonneg _)]

/-- Real form of the kernel bound. -/
theorem integral_rieszKernelOne_le_of_subset_closedBall (hd : 2 ≤ d) (y : Vec d) {D : ℝ}
    (hD : 0 < D) {V : Set (Vec d)} (hV : V ⊆ euclideanClosedBall y D) :
    ∫ x in V, rieszKernelOne d (x - y) ≤
      (d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal * D := by
  have hint := integrableOn_rieszKernelOne_of_subset_closedBall hd y hD hV
  have hnn : 0 ≤ᵐ[volume.restrict V] fun x => rieszKernelOne d (x - y) :=
    Filter.Eventually.of_forall fun x => rieszKernelOne_nonneg _
  rw [← ENNReal.ofReal_le_ofReal_iff (by
      have := (volume_euclideanBall_toReal_pos (0 : Vec d) (one_pos))
      positivity), ofReal_integral_eq_lintegral_ofReal hint hnn]
  exact lintegral_rieszKernelOne_le_of_subset_closedBall hd y hD hV

end

end PDE
