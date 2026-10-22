module

public import PDEFoundation.Sobolev.W1p.ConvexApprox.Convergence

/-! # Scalar mollification on the unit ball -/

@[expose] public section

namespace PDE

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-- The literal inward mollification sequence on the round unit ball. Its
sampling point is `(1 - ε) • x`; the convolution kernel has scale `ε * r`. -/
def unitBallScalarMollification {d : ℕ} (f : Vec d → ℝ) (n : ℕ) :
    Vec d → ℝ :=
  convexApproxSmoothRepresentative (euclideanBall (0 : Vec d) 1)
    (unitConvexApproxKernel (d := d)) f 0
    (1 / (2 * Real.sqrt d)) (unitConvexApproxScale (n + 1))

private theorem unitBall_mollification_closedCube_subset
    {d : ℕ} (hd : 0 < d) :
    Metric.closedBall (0 : Vec d) (1 / (2 * Real.sqrt d)) ⊆
      euclideanBall (0 : Vec d) 1 := by
  intro x hx
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hnorm : ‖x‖ ≤ 1 / (2 * Real.sqrt d) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2
  calc
    vecEuclideanNorm (x - 0) = vecEuclideanNorm x := by simp
    _ ≤ Real.sqrt d * ‖x‖ := vecEuclideanNorm_le_sqrt_natCast_mul_norm x
    _ ≤ Real.sqrt d * (1 / (2 * Real.sqrt d)) :=
      mul_le_mul_of_nonneg_left hnorm hsqrt.le
    _ = 1 / 2 := by field_simp
    _ < 1 := by norm_num

/-- Every member of the unit-ball scalar mollification sequence is globally
smooth. -/
theorem contDiff_unitBallScalarMollification
    {d : ℕ} (hd : 0 < d) {p : ENNReal} (hp : 1 ≤ p)
    (f : Vec d → ℝ)
    (hf : MemLp f p (volumeOn (euclideanBall (0 : Vec d) 1)))
    (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (unitBallScalarMollification f n) := by
  unfold unitBallScalarMollification
  apply contDiff_convexApproxSmoothRepresentative
    (isOpen_euclideanBall _ _).measurableSet
    (isConvexApproxKernel_unitConvexApproxKernel (d := d)) hp hf
  · have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (by positivity)
    positivity
  · exact unitConvexApproxScale_pos (n + 1)

/-- The literal smooth inward mollifications converge to the input in true
`L^p` on the round unit ball for every finite exponent `p ≥ 1`. -/
theorem tendsto_eLpNorm_unitBallScalarMollification_sub
    {d : ℕ} (hd : 0 < d) {p : ENNReal}
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (f : Vec d → ℝ)
    (hf : MemLp f p (volumeOn (euclideanBall (0 : Vec d) 1))) :
    Tendsto
      (fun n => eLpNorm
        (fun x => unitBallScalarMollification f n x - f x) p
        (volumeOn (euclideanBall (0 : Vec d) 1)))
      atTop (𝓝 0) := by
  let U := euclideanBall (0 : Vec d) 1
  let ρ := unitConvexApproxKernel (d := d)
  let r := 1 / (2 * Real.sqrt d)
  let ε : ℕ → ℝ := fun n => unitConvexApproxScale (n + 1)
  have hU : IsOpenBoundedConvexDomain U :=
    isOpenBoundedConvexDomain_euclideanBall 0 (by norm_num)
  have hρ : IsConvexApproxKernel ρ :=
    isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have hr : 0 < r := by
    dsimp only [r]
    have : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (by positivity)
    positivity
  have hball : Metric.closedBall (0 : Vec d) r ⊆ U := by
    exact unitBall_mollification_closedCube_subset hd
  have hε : Tendsto ε atTop (𝓝 0) := by
    exact tendsto_unitConvexApproxScale_zero.comp (tendsto_add_atTop_nat 1)
  have hεPos : ∀ᶠ n : ℕ in atTop, 0 < ε n :=
    Eventually.of_forall fun n => unitConvexApproxScale_pos (n + 1)
  have hεOne : ∀ᶠ n : ℕ in atTop, ε n < 1 :=
    ((tendsto_order.1 hε).2 1 zero_lt_one)
  have hraw :=
    tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_memLpOn
      hU hρ hp hpTop hf hball hr hε hεPos hεOne
  refine hraw.congr' ?_
  filter_upwards [hεOne] with n hn
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
  rw [unitBallScalarMollification,
    convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
      hU hρ hx hball hr (unitConvexApproxScale_pos (n + 1)) hn]

end

end PDE
