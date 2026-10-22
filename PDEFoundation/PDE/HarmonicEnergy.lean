module

public import PDEFoundation.PDE.HarmonicApproximation
public import PDEFoundation.PDE.HarmonicEnergySmooth
public import PDEFoundation.Sobolev.W1p.GraphEnergy
public import PDEFoundation.Measure.BallVolume

/-! # Exact normalized energy comparison for weak harmonic functions -/

@[expose] public section

namespace PDE

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

variable {d : ℕ}

/-- Strong scalar `L²` convergence implies convergence of squared integrals. -/
theorem tendsto_setIntegral_sq_of_tendsto_eLpNorm
    {U : Set (Vec d)} {f : ℕ → Vec d → ℝ} {g : Vec d → ℝ}
    (hf : ∀ n, MemL2On U (f n)) (hg : MemL2On U g)
    (hconv : Tendsto (fun n => eLpNorm (fun x => f n x - g x) 2 (volumeOn U))
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in U, f n x ^ 2) atTop (𝓝 (∫ x in U, g x ^ 2)) := by
  have hLp : Tendsto (fun n => (hf n).toScalarLp) atTop (𝓝 hg.toScalarLp) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).mpr hconv
  have hnorm := hLp.norm.pow 2
  have heq (n : ℕ) : (∫ x in U, f n x ^ 2) = ‖(hf n).toScalarLp‖ ^ 2 :=
    integral_sq_eq_sq_norm_of_ae_eq _ _ (hf n).coeFn_toScalarLp
  have hlim : (∫ x in U, g x ^ 2) = ‖hg.toScalarLp‖ ^ 2 :=
    integral_sq_eq_sq_norm_of_ae_eq _ _ hg.coeFn_toScalarLp
  simpa only [← heq, ← hlim] using hnorm

/-- Coordinatewise strong `L²` convergence implies convergence of native
Euclidean gradient energies. -/
theorem tendsto_setIntegral_vecNormSq_of_tendsto_eLpNorm
    {U : Set (Vec d)} {F : ℕ → Vec d → Vec d} {G : Vec d → Vec d}
    (hF : ∀ n, MemVectorL2On U (F n)) (hG : MemVectorL2On U G)
    (hconv : ∀ i : Fin d, Tendsto
      (fun n => eLpNorm (fun x => F n x i - G x i) 2 (volumeOn U)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in U, vecNormSq (F n x)) atTop
      (𝓝 (∫ x in U, vecNormSq (G x))) := by
  have hsqF (n : ℕ) (i : Fin d) : IntegrableOn (fun x => F n x i ^ 2) U := by
    simpa only [pow_two] using integrableOn_mul_of_memL2On (hF n i) (hF n i)
  have hsqG (i : Fin d) : IntegrableOn (fun x => G x i ^ 2) U := by
    simpa only [pow_two] using integrableOn_mul_of_memL2On (hG i) (hG i)
  have hsum := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_setIntegral_sq_of_tendsto_eLpNorm (fun n => hF n i) (hG i) (hconv i))
  simp only [vecNormSq, vecDot, ← pow_two]
  simp_rw [integral_finsetSum Finset.univ (fun i _ => hsqF _ i),
    integral_finsetSum Finset.univ (fun i _ => hsqG i)]
  exact hsum

/-- The harmonic smooth approximants converge in energy on every subdomain,
including the original domain. -/
theorem tendsto_convexApproxSmoothW1p_integralAverage_grad_energy
    {U V : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (hVU : V ⊆ U)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) :
    Tendsto (fun n => integralAverage V (fun x => vecNormSq
      ((W1pFunction.convexApproxSmoothW1p hU (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        u.toW1pFunction x0 hr n).grad x))) atTop
      (𝓝 (integralAverage V (fun x => vecNormSq (u.grad x)))) := by
  let v := W1pFunction.convexApproxSmoothW1p hU
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) u.toW1pFunction x0 hr
  have hconv (i : Fin d) : Tendsto
      (fun n => eLpNorm (fun x => (v n).grad x i - u.grad x i) 2 (volumeOn V))
      atTop (𝓝 0) := by
    have hwhole := W1pFunction.tendsto_convexApproxSmoothW1p_grad_coord_eLpNorm_sub
      hU (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      u.toW1pFunction hball hr i
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hwhole
      (fun _ => bot_le)
    intro n
    exact eLpNorm_mono_measure _ (Measure.restrict_mono hVU le_rfl)
  have henergy := tendsto_setIntegral_vecNormSq_of_tendsto_eLpNorm
    (fun n i => memLpOn_mono hVU ((v n).grad_memLp i))
    (fun i => memLpOn_mono hVU (u.gradMemL2 i)) hconv
  exact henergy.const_mul _

/-- Exact constant-one comparison of normalized weak harmonic gradient energies
on concentric round balls strictly inside the equation domain. -/
theorem integralAverage_vecNormSq_weakHarmonic_grad_mono_of_lt [NeZero d]
    {z : Vec d} {R : ℝ} (hR : 0 < R) (u : H1Function (euclideanBall z R))
    (hu : ∀ φ : WeakTestFunction (euclideanBall z R),
      ∫ x in euclideanBall z R, vecDot (u.grad x) (φ.grad x) = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbR : b < R) :
    integralAverage (euclideanBall z a) (fun x => vecNormSq (u.grad x)) ≤
      integralAverage (euclideanBall z b) (fun x => vecNormSq (u.grad x)) := by
  let hU := isOpenBoundedConvexDomain_euclideanBall z hR
  obtain ⟨x0, r, hr, hball⟩ :=
    exists_metricClosedBall_subset_of_isOpenBoundedConvexDomain hU
      (euclideanBall_nonempty z hR)
  let v := W1pFunction.convexApproxSmoothW1p hU
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) u.toW1pFunction x0 hr
  have hmono (n : ℕ) :
      integralAverage (euclideanBall z a) (fun x => vecNormSq ((v n).grad x)) ≤
        integralAverage (euclideanBall z b) (fun x => vecNormSq ((v n).grad x)) := by
    rw [W1pFunction.convexApproxSmoothW1p_grad]
    exact integralAverage_vecNormSq_classicalGradient_mono
      (W1pFunction.contDiff_convexApproxSmoothW1p_toFun hU _ _ _ _ n) hR
      (fun x hx => euclideanCoordLaplacian_convexApproxSmoothW1p_eq_zero
        hU u hu hx hball hr n) ha hab hbR
  exact le_of_tendsto_of_tendsto
    (tendsto_convexApproxSmoothW1p_integralAverage_grad_energy hU u
      (euclideanBall_mono ha.le (hab.trans hbR.le)) hball hr)
    (tendsto_convexApproxSmoothW1p_integralAverage_grad_energy hU u
      (euclideanBall_mono (ha.trans_le hab).le hbR.le) hball hr)
    (Eventually.of_forall hmono)

/-- Exact normalized energy comparison, including the outer radius of the
weak harmonic equation domain. -/
theorem integralAverage_vecNormSq_weakHarmonic_grad_mono [NeZero d]
    {z : Vec d} {R : ℝ} (hR : 0 < R) (u : H1Function (euclideanBall z R))
    (hu : ∀ φ : WeakTestFunction (euclideanBall z R),
      ∫ x in euclideanBall z R, vecDot (u.grad x) (φ.grad x) = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbR : b ≤ R) :
    integralAverage (euclideanBall z a) (fun x => vecNormSq (u.grad x)) ≤
      integralAverage (euclideanBall z b) (fun x => vecNormSq (u.grad x)) := by
  rcases hbR.eq_or_lt with hbeq | hbR
  · subst b
    rcases (hab.eq_or_lt) with haeq | haR
    · subst a
      exact le_rfl
    let t : ℕ → ℝ := fun n => R - (R - a) * unitConvexApproxScale n / 2
    have hat (n : ℕ) : a ≤ t n := by
      have hs := unitConvexApproxScale_le_one n
      have hp := unitConvexApproxScale_pos n
      dsimp [t]
      nlinarith
    have htR (n : ℕ) : t n < R := by
      have hp := unitConvexApproxScale_pos n
      dsimp [t]
      nlinarith
    have htpos (n : ℕ) : 0 < t n := ha.trans_le (hat n)
    have htlim : Tendsto t atTop (𝓝 R) := by
      have h := (tendsto_const_nhds (x := R) (f := atTop)).sub
        ((tendsto_unitConvexApproxScale_zero.const_mul (R - a)).div_const 2)
      simpa only [mul_zero, zero_div, sub_zero, t] using h
    let A := integralAverage (euclideanBall z a) (fun x => vecNormSq (u.grad x))
    let I := ∫ x in euclideanBall z R, vecNormSq (u.grad x)
    have hbound (n : ℕ) : A * (volume (euclideanBall z (t n))).toReal ≤ I := by
      have hm := integralAverage_vecNormSq_weakHarmonic_grad_mono_of_lt
        hR u hu ha (hat n) (htR n)
      change A ≤ (volume (euclideanBall z (t n))).toReal⁻¹ *
        (∫ x in euclideanBall z (t n), vecNormSq (u.grad x)) at hm
      rw [← div_eq_inv_mul] at hm
      exact ((le_div_iff₀ (volume_euclideanBall_toReal_pos z (htpos n))).mp hm).trans
        (setIntegral_mono_set (integrableOn_vecNormSq_of_memVectorL2On u.gradMemL2)
          (Eventually.of_forall fun x => vecNormSq_nonneg (u.grad x))
          (euclideanBall_mono (htpos n).le (htR n).le).eventuallyLE)
    have hvol := (htlim.pow d).mul_const
      (volume (euclideanBall (0 : Vec d) 1)).toReal
    have hscaled : A * (volume (euclideanBall z R)).toReal ≤ I := by
      rw [volume_euclideanBall_toReal_eq_unit_mul_of_pos z hR]
      apply le_of_tendsto (hvol.const_mul A)
      apply Eventually.of_forall
      intro n
      simpa only [volume_euclideanBall_toReal_eq_unit_mul_of_pos z (htpos n)]
        using hbound n
    change A ≤ (volume (euclideanBall z R)).toReal⁻¹ * I
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ (volume_euclideanBall_toReal_pos z hR)).mpr hscaled
  · exact integralAverage_vecNormSq_weakHarmonic_grad_mono_of_lt hR u hu ha hab hbR

/-- Square-root normalized `L²` energy inherits the exact constant one. -/
theorem sqrt_integralAverage_vecNormSq_weakHarmonic_grad_mono [NeZero d]
    {z : Vec d} {R : ℝ} (hR : 0 < R) (u : H1Function (euclideanBall z R))
    (hu : ∀ φ : WeakTestFunction (euclideanBall z R),
      ∫ x in euclideanBall z R, vecDot (u.grad x) (φ.grad x) = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbR : b ≤ R) :
    Real.sqrt (integralAverage (euclideanBall z a) (fun x => vecNormSq (u.grad x))) ≤
      Real.sqrt (integralAverage (euclideanBall z b) (fun x => vecNormSq (u.grad x))) :=
  Real.sqrt_le_sqrt (integralAverage_vecNormSq_weakHarmonic_grad_mono hR u hu ha hab hbR)

end

end PDE
