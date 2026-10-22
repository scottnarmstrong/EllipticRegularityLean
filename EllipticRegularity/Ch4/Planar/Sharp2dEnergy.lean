module

public import PDEFoundation
public import PDEFoundation.PDE.DGNM.Scaling
public import PDEFoundation.PDE.DGNM.Bridge

/-!
# Energy densities and blow-up for the planar sharp Hölder exponent

Integrability of the energy density `∇u · a ∇u`, its two-sided comparison with `|∇u|²`,
and its behaviour under the blow-up `y ↦ x₀ + y / 2` (in dimension two).
-/

@[expose] public section

namespace PDE.Ch4Planar

open MeasureTheory

/-- The upper energy bound `ξ · A ξ ≤ Λ |ξ|²` for a matrix satisfying (4.1) with
lower constant one. -/
theorem vecDot_matVecMul_le {d : ℕ} {Λ : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix 1 Λ A) (ξ : Vec d) :
    vecDot ξ (matVecMul A ξ) ≤ Λ * vecNormSq ξ := by
  calc vecDot ξ (matVecMul A ξ) ≤ |vecDot ξ (matVecMul A ξ)| := le_abs_self _
    _ ≤ vecEuclideanNorm ξ * vecEuclideanNorm (matVecMul A ξ) :=
      abs_vecDot_le_vecEuclideanNorm_mul ξ _
    _ ≤ vecEuclideanNorm ξ * (Λ * vecEuclideanNorm ξ) :=
      mul_le_mul_of_nonneg_left (vecEuclideanNorm_matVecMul_le_of_isEllipticMatrix hA ξ)
        (vecEuclideanNorm_nonneg ξ)
    _ = Λ * vecNormSq ξ := by
      calc vecEuclideanNorm ξ * (Λ * vecEuclideanNorm ξ) =
            Λ * (vecEuclideanNorm ξ * vecEuclideanNorm ξ) := by ring
        _ = Λ * vecNormSq ξ := by rw [← pow_two, vecEuclideanNorm_sq]

/-- The pairing of two `L²` vector fields is integrable. -/
theorem integrableOn_vecDot {d : ℕ} {U : Set (Vec d)} {F G : Vec d → Vec d}
    (hF : MemVectorL2On U F) (hG : MemVectorL2On U G) :
    IntegrableOn (fun x => vecDot (F x) (G x)) U := by
  unfold vecDot
  exact integrable_finsetSum _ fun i _ => integrableOn_mul_of_memL2On (hF i) (hG i)

/-- The energy density `∇u · a ∇u` is integrable on the domain. -/
theorem integrableOn_energyDensity {d : ℕ} {Λ : ℝ} {a : CoeffField d}
    {U : Set (Vec d)} (hU : MeasurableSet U)
    (hmeas : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hell : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x)) (u : H1Function U) :
    IntegrableOn (fun x => vecDot (u.grad x) (matVecMul (a x) (u.grad x))) U :=
  integrableOn_vecDot u.gradMemL2
    (DGNM.memVectorL2On_matVecMul_of_aemeasurable hU hmeas hell u.gradMemL2)

/-- `|∇u|²` is integrable on the domain. -/
theorem integrableOn_gradSq {d : ℕ} {U : Set (Vec d)} (u : H1Function U) :
    IntegrableOn (fun x => vecNormSq (u.grad x)) U :=
  integrableOn_vecDot u.gradMemL2 u.gradMemL2

/-- Energy of the blow-up `v(y) = u(x₀ + y/2)` on `B_s` equals the energy of `u` on
`B_{s/2}(x₀)`, in dimension two. -/
theorem blowUp_energy {U : Set (Vec 2)} (u : H1Function U) (a : CoeffField 2) (x₀ : Vec 2)
    (hball : euclideanBall x₀ (1 / 2) ⊆ U) (s : ℝ) :
    ∫ y in euclideanBall (0 : Vec 2) s,
        vecDot ((DGNM.blowUp u x₀ (by norm_num : (0 : ℝ) < 1 / 2) hball).grad y)
          (matVecMul (DGNM.blowUpCoeff a x₀ (1 / 2) y)
            ((DGNM.blowUp u x₀ (by norm_num : (0 : ℝ) < 1 / 2) hball).grad y)) =
      ∫ x in euclideanBall x₀ (1 / 2 * s), vecDot (u.grad x) (matVecMul (a x) (u.grad x)) := by
  have hr : (0 : ℝ) < 1 / 2 := by norm_num
  have hpt : ∀ y : Vec 2,
      vecDot ((DGNM.blowUp u x₀ hr hball).grad y)
          (matVecMul (DGNM.blowUpCoeff a x₀ (1 / 2) y) ((DGNM.blowUp u x₀ hr hball).grad y)) =
        (1 / 4 : ℝ) * (fun x => vecDot (u.grad x) (matVecMul (a x) (u.grad x)))
          ((1 / 2 : ℝ) • y + x₀) := by
    intro y
    simp only [DGNM.blowUp_grad, DGNM.blowUpCoeff_apply, DGNM.matVecMul_smul,
      DGNM.vecDot_smul_right, DGNM.vecDot_smul_left]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, DGNM.setIntegral_comp_affineScale_ball x₀ hr s
    (fun x => vecDot (u.grad x) (matVecMul (a x) (u.grad x)))]
  rw [← mul_assoc]
  norm_num

end PDE.Ch4Planar
