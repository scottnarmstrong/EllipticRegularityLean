module

public import PDEFoundation.PDE.OneDimensionalFlux
public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.Measure.EuclideanFieldMeasurability

@[expose] public section

namespace PDE
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- Measurable coefficients and bounded forcing already give a bounded weak
one-dimensional gradient through the actual constant total flux. -/
theorem exists_oneDimensional_gradient_bound_of_bounded_forcing
    {U : Set (Vec 1)} (hU : IsOpenBoundedConvexDomain U)
    (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    {a : CoeffField 1} {Lam M : ℝ}
    (ha : AEMeasurable (fun x => a x 0 0) (volumeOn U))
    (hell : ∀ᵐ x ∂volumeOn U, IsEllipticMatrix 1 Lam (a x))
    (u : H1Function U) (F : Vec 1 → Vec 1)
    (hFm : AEStronglyMeasurable (fun x => F x 0) (volumeOn U))
    (hFb : ∀ᵐ x ∂volumeOn U, |F x 0| ≤ M)
    (hsol : IsWeakDivergenceFormSolutionOn a U u 0 F) :
    ∃ c : ℝ,
      (fun x => (matVecMul (a x) (u.grad x)) 0 + F x 0) =ᵐ[volumeOn U]
        (fun _ => c) ∧
      (∀ᵐ x ∂volumeOn U, vecEuclideanNorm (u.grad x) ≤ |c| + M) ∧
      MemLp (fun x => vecEuclideanNorm (u.grad x)) ⊤ (volumeOn U) := by
  let : IsFiniteMeasure (volumeOn U) :=
    ⟨by simpa only [volumeOn, Measure.restrict_apply_univ] using hUTop⟩
  have hu1 : Integrable (fun x => u.grad x 0) (volumeOn U) :=
    memLp_one_iff_integrable.mp ((u.gradMemL2 0).mono_exponent (by norm_num))
  have haflux : Integrable (fun x => a x 0 0 * u.grad x 0) (volumeOn U) := by
    apply Integrable.mono' (hu1.norm.const_mul Lam)
    · exact ha.aestronglyMeasurable.mul (u.gradMemL2 0).aestronglyMeasurable
    · filter_upwards [hell] with x hx
      simp only [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (abs_apply_le_of_isEllipticMatrix hx 0 0) (abs_nonneg _)
  have hFint : Integrable (fun x => F x 0) (volumeOn U) := by
    apply Integrable.mono' (integrable_const M) hFm
    filter_upwards [hFb] with x hx
    simpa only [Real.norm_eq_abs] using hx
  have hflux : IntegrableOn
      (fun x => (matVecMul (a x) (u.grad x)) 0 + F x 0) U := by
    simpa [matVecMul] using! haflux.add hFint
  let c := integralAverage U
    (fun x => (matVecMul (a x) (u.grad x)) 0 + F x 0)
  have hc := oneDimensional_totalFlux_ae_eq_integralAverage hU hUPos hUTop hsol hflux
  have hb : ∀ᵐ x ∂volumeOn U, vecEuclideanNorm (u.grad x) ≤ |c| + M := by
    filter_upwards [hc, hell, hFb] with x hcx hax hFx
    have ha1 : 1 ≤ a x 0 0 := by
      have hh := hax.coercive (basisVec 0)
      simpa [vecNormSq, vecDot, matVecMul, basisVec] using hh
    have ha0 : 0 ≤ a x 0 0 := zero_le_one.trans ha1
    have hmul : a x 0 0 * u.grad x 0 = c - F x 0 := by
      simpa [matVecMul, c, eq_sub_iff_add_eq] using hcx
    have hnorm : vecEuclideanNorm (u.grad x) = |u.grad x 0| := by
      simp [vecEuclideanNorm, vecNormSq, vecDot, Real.sqrt_mul_self_eq_abs]
    rw [hnorm]
    calc
      |u.grad x 0| ≤ a x 0 0 * |u.grad x 0| := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right ha1 (abs_nonneg _)
      _ = |a x 0 0 * u.grad x 0| := by rw [abs_mul, abs_of_nonneg ha0]
      _ = |c - F x 0| := by rw [hmul]
      _ ≤ |c| + |F x 0| := abs_sub _ _
      _ ≤ |c| + M := add_le_add le_rfl hFx
  refine ⟨c, hc, hb, ?_⟩
  apply memLp_top_of_bound (aestronglyMeasurable_vecEuclideanNorm_of_coord
    (fun i => (u.gradMemL2 i).aestronglyMeasurable)) (|c| + M)
  filter_upwards [hb] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _)] using hx

end
end PDE
