module

public import PDEFoundation.Measure.EuclideanFieldLpConvergence
public import PDEFoundation.Measure.UnitBallScalarMollification
public import PDEFoundation.Sobolev.W1p.ConvexApprox.SmoothRepresentative

/-! # Native vector mollification on the unit ball -/

@[expose] public section

namespace PDE

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-- Literal coordinatewise scalar mollification of a native vector field on the
round unit ball. -/
def unitBallVectorMollification {d m : ℕ} (F : Vec d → Vec m) (n : ℕ) :
    Vec d → Vec m :=
  fun x i => unitBallScalarMollification (fun y => F y i) n x

/-- Unit-ball vector mollifications are componentwise globally smooth, remain
in the exact Euclidean-magnitude `Lᵖ` space, and converge there to the input. -/
theorem unitBallVectorMollification_properties
    {d m : ℕ} (hd : 0 < d) {p : ENNReal}
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) (F : Vec d → Vec m)
    (hFcoord : ∀ i, AEStronglyMeasurable (fun x => F x i)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hF : MemLp (fun x => vecEuclideanNorm (F x)) p
      (volumeOn (euclideanBall (0 : Vec d) 1))) :
    (∀ n i, ContDiff ℝ (⊤ : ℕ∞)
      (fun x => unitBallVectorMollification F n x i)) ∧
    (∀ n, MemLp (fun x => vecEuclideanNorm (unitBallVectorMollification F n x)) p
      (volumeOn (euclideanBall (0 : Vec d) 1))) ∧
    Tendsto
      (fun n => eLpNorm
        (fun x => vecEuclideanNorm (unitBallVectorMollification F n x - F x)) p
        (volumeOn (euclideanBall (0 : Vec d) 1)))
      atTop (𝓝 0) := by
  let U := euclideanBall (0 : Vec d) 1
  have hFcoordLp (i : Fin m) : MemLp (fun x => F x i) p (volumeOn U) := by
    apply MemLp.of_le_mul (c := 1) hF (hFcoord i)
    filter_upwards with x
    simpa only [Real.norm_eq_abs, one_mul,
      abs_of_nonneg (vecEuclideanNorm_nonneg _)] using
      abs_apply_le_vecEuclideanNorm (F x) i
  have hsmooth (n : ℕ) (i : Fin m) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => unitBallVectorMollification F n x i) := by
    simpa only [unitBallVectorMollification] using
      contDiff_unitBallScalarMollification hd hp (fun x => F x i) (hFcoordLp i) n
  have hscaleLt (n : ℕ) : unitConvexApproxScale (n + 1) < 1 := by
    rw [unitConvexApproxScale]
    have hden : 0 < ((n + 1 : ℕ) : ℝ) + 1 := by positivity
    rw [div_lt_one hden]
    norm_num
    positivity
  have hball : Metric.closedBall (0 : Vec d) (1 / (2 * Real.sqrt d)) ⊆ U := by
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
  have hr : 0 < (1 / (2 * Real.sqrt d) : ℝ) := by
    have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (by positivity)
    positivity
  have houtCoordLp (n : ℕ) (i : Fin m) :
      MemLp (fun x => unitBallVectorMollification F n x i) p (volumeOn U) := by
    have hs := memLpOn_convexApproxSmoothing
      (isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) (by norm_num))
      (isConvexApproxKernel_unitConvexApproxKernel (d := d)) hp hpTop
      (hFcoordLp i) hball hr (unitConvexApproxScale_pos (n + 1)) (hscaleLt n)
    apply MemLp.ae_eq _ hs
    filter_upwards [ae_restrict_mem (isOpen_euclideanBall _ _).measurableSet] with x hx
    exact (convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
      (isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) (by norm_num))
      (isConvexApproxKernel_unitConvexApproxKernel (d := d)) hx hball hr
      (unitConvexApproxScale_pos (n + 1)) (hscaleLt n)).symm
  have houtMagLp (n : ℕ) :
      MemLp (fun x => vecEuclideanNorm (unitBallVectorMollification F n x)) p
        (volumeOn U) := by
    let G : Vec d → Vec m := unitBallVectorMollification F n
    have hHilbert : MemLp (fun x => (G x).toHilbertVec) p (volumeOn U) := by
      simpa only [Vec.toHilbertVec_apply, G] using
        (memLp_piLp_iff (f := fun x => (G x).toHilbertVec)
          (p := p) (μ := volumeOn U)).mpr (houtCoordLp n)
    exact hHilbert.norm.ae_eq (Filter.Eventually.of_forall fun x =>
      (Vec.vecEuclideanNorm_eq_norm_toHilbertVec (G x)).symm)
  have hcoordConv (i : Fin m) : Tendsto
      (fun n => eLpNorm
        (fun x => unitBallVectorMollification F n x i - F x i) p (volumeOn U))
      atTop (𝓝 0) := by
    simpa only [unitBallVectorMollification] using
      tendsto_eLpNorm_unitBallScalarMollification_sub hd hp hpTop
        (fun x => F x i) (hFcoordLp i)
  refine ⟨hsmooth, houtMagLp, ?_⟩
  apply tendsto_eLpNorm_euclideanField_sub_zero_of_coordinate hp hpTop
  · exact houtCoordLp
  · exact hFcoordLp
  · exact hcoordConv

end

end PDE
