module

public import PDEFoundation.Monotonicity.ACF.WeightedPolarId

/-!
# The kernel-averaged weighted bound

For `0 < r`, `0 < k`, `r + k < R`:

`J(r) ≤ ∫_{ρ>0} ker_{r,k}(ρ) · (flux(ρ) + ((d-2)/2) a(ρ)) / ρ^{d-1} dρ`,

where `ker_{r,k}` is a smooth averaging kernel (mass `1`, supported in `[r, r+k]`).  Letting
`k → 0` at Lebesgue points is done in `WeightedAssembly`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace PDE

noncomputable section

variable {r k : ℝ}

/-- The radial profile `(flux + ((d-2)/2) a) / ρ^{d-1}` against which the kernel is averaged. -/
def acfProfile (d : ℕ) (u : Vec d → ℝ) (G : Vec d → Vec d) (ρ : ℝ) : ℝ :=
  (acfSliceFlux u G ρ + (((d : ℝ) - 2) / 2) * acfSliceMass u ρ) / ρ ^ (d - 1)

theorem acf_energy_le_kernel {d : ℕ} (hd : 3 ≤ d) {R : ℝ} (hr : 0 < r) (hk : 0 < k)
    (hrk : r + k < R) (u : H1Function (euclideanBall (0 : Vec d) R))
    (hcont : ContinuousOn u.toFun (euclideanBall (0 : Vec d) R))
    (hnonneg : ∀ x ∈ euclideanBall (0 : Vec d) R, 0 ≤ u.toFun x)
    (hsub : IsWeakDivergenceFormSubharmonicOn (fun _ => (1 : Mat d))
      (euclideanBall (0 : Vec d) R) u) :
    acfWeightedEnergy u.grad r ≤
      ENNReal.ofReal (∫ ρ in Ioi (0 : ℝ), acfKer r k ρ * acfProfile d u.toFun u.grad ρ) := by
  have h1 := acfLimit_inequality hd hr hk hrk u hcont hnonneg hsub
  have h2 := acf_half_T_polar hd hr hk hrk u hcont
  have hrR : r ≤ R := by linarith
  have hX1 : acfWeightedEnergy u.grad r ≤ ∫⁻ x in euclideanBall (0 : Vec d) R,
      ENNReal.ofReal (acfQ (acfKappa d) 0 (vecNormSq x) * acfCut r k (vecNormSq x) *
        vecNormSq (u.grad x)) := by
    unfold acfWeightedEnergy
    have hmeas : MeasurableSet (euclideanBall (0 : Vec d) r) :=
      (isOpen_euclideanBall (0 : Vec d) r).measurableSet
    calc ∫⁻ x in euclideanBall (0 : Vec d) r,
          ENNReal.ofReal (vecNormSq (u.grad x) / vecEuclideanNorm x ^ (d - 2))
        = ∫⁻ x in euclideanBall (0 : Vec d) r, ENNReal.ofReal
            (acfQ (acfKappa d) 0 (vecNormSq x) * acfCut r k (vecNormSq x) *
              vecNormSq (u.grad x)) := by
          refine setLIntegral_congr_fun hmeas fun x hx => ?_
          have hx' : vecNormSq x < r ^ 2 := mem_euclideanBall_zero_iff.mp hx
          rw [acfCut_eq_one hr hk hx'.le, show vecNormSq x = vecEuclideanNorm x ^ 2 from
            (vecEuclideanNorm_sq x).symm, acfQ_zero_sq hd (vecEuclideanNorm_nonneg x)]
          congr 1
          rw [div_eq_inv_mul]; ring
      _ ≤ _ := lintegral_mono_set (euclideanBall_zero_subset hrR hr.le)
  refine hX1.trans (h1.trans (le_of_eq ?_))
  rw [h2]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
  have hρ0 : 0 < ρ := hρ
  simp only [acfProfile]
  rw [acfK0_sq (by omega) hρ0]
  have : ρ ^ (d - 1) ≠ 0 := by positivity
  field_simp
  ring

end

end PDE
