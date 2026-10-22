module

public import EllipticRegularity.DeGiorgi.LogEnergy.Estimate
public import EllipticRegularity.DeGiorgi.LogEnergy.SharpCutoff
public import EllipticRegularity.DeGiorgi.LogPackage.Defs
public import PDEFoundation.Measure.BallVolume

/-!
# The logarithmic energy estimate on balls

Combines the test-function estimate `log_energy_cutoff` with the sharp radial cutoffs of
`SharpCutoff.lean` and lets the cutoff parameters tend to their limits.
-/

@[expose] public section

namespace PDE.DGNMLogEnergy

open MeasureTheory Filter Topology Set

variable {d : ℕ}

theorem euclideanBall_subset_unit {y : Vec d} {s : ℝ} (hs : 0 < s)
    (hys : vecEuclideanNorm y + s < 1) :
    euclideanBall y s ⊆ euclideanBall (0 : Vec d) 1 := by
  intro x hx
  have h1 : vecEuclideanNorm (x - y) < s := (mem_euclideanBall_iff_vecEuclideanNorm_lt hs).mp hx
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt one_pos, sub_zero]
  have := vecEuclideanNorm_add_le (x - y) y
  rw [sub_add_cancel] at this
  linarith

/-- The `L²` norm of the gradient of a cutoff is bounded by `K²` times the volume of its outer
ball. -/
theorem integral_gradSq_cutoff_le {y : Vec d} {r s K : ℝ}
    (η : QuantitativeSmoothCutoff (euclideanBall y r) (euclideanBall y s) K)
    {U : Set (Vec d)} (hUmeas : MeasurableSet U) (hsU : euclideanBall y s ⊆ U) (hs : 0 ≤ s)
    (hG : IntegrableOn (fun x => vecNormSq (classicalGradient η.toFun x)) U) :
    ∫ x in U, vecNormSq (classicalGradient η.toFun x) ≤ K ^ 2 * (volume (euclideanBall y s)).toReal := by
  have hBmeas : MeasurableSet (euclideanBall y s) := (isOpen_euclideanBall y s).measurableSet
  have hzero : ∀ x ∈ U \ euclideanBall y s, vecNormSq (classicalGradient η.toFun x) = 0 := by
    intro x hx
    rw [η.classicalGradient_eq_zero_of_not_mem_outer hx.2]
    simp [vecNormSq, vecDot]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hUmeas hsU hzero]
  have hfin : volume (euclideanBall y s) ≠ ⊤ := volume_euclideanBall_ne_top y hs
  have hbound : ∀ x, vecNormSq (classicalGradient η.toFun x) ≤ K ^ 2 := by
    intro x
    have h := η.gradient_bound x
    have hsq : vecEuclideanNorm (classicalGradient η.toFun x) ^ 2 =
        vecNormSq (classicalGradient η.toFun x) := Real.sq_sqrt (vecNormSq_nonneg _)
    rw [← hsq]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  have hci : IntegrableOn (fun _ : Vec d => K ^ 2) (euclideanBall y s) :=
    integrableOn_const hfin
  calc ∫ x in euclideanBall y s, vecNormSq (classicalGradient η.toFun x)
      ≤ ∫ x in euclideanBall y s, K ^ 2 :=
        setIntegral_mono_on (hG.mono_set hsU) hci hBmeas (fun x _ => hbound x)
    _ = K ^ 2 * (volume (euclideanBall y s)).toReal := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]; rfl

end PDE.DGNMLogEnergy
