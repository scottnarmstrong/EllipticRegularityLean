module

public import PDEFoundation.PDE.DGNM.Absorb
public import PDEFoundation.PDE.DGNM.Composites
public import PDEFoundation.Sobolev.Cutoff.Ball
public import PDEFoundation.Measure.BallVolume

/-!
# Chain-rule tests `η² G(u)` and the logarithmic energy estimate

* `subharmonic_chainTest` / `superharmonic_chainTest`: for any `v ∈ H¹` with
  `v ≥ 0` a.e. and `∇v = G'(u) ∇u` (e.g. the composites of `Composites.lean`),
  `∫ η² G'(u) ∇u·a∇u + ∫ 2η v (a∇u·∇η) ≤ 0` (resp. `≥ 0`), all pieces
  integrable.
* `superharmonic_log_energy`: for a supersolution `u ≥ δ > 0` a.e.,
  `∫ η² ∇log u · a ∇log u ≤ 4Λ ∫ |∇η|²` (manuscript Proposition 4.11 Step 2,
  Proposition 4.16), with `∇ log u = u⁻¹ ∇u`; and the Euclidean corollary
  `∫ η² |∇ log u|² ≤ 4Λ ∫ |∇η|²`, and the ball form
  `∫_{B_R(x₀)} |∇ log u|² ≤ 4Λ (32/R)² |B_{2R}(x₀)|` when `B_{2R}(x₀) ⊆ U`.
-/

@[expose] public section

namespace PDE

namespace DGNM

open MeasureTheory

variable {d : ℕ} {U : Set (Vec d)} {Λ : ℝ} {a : CoeffField d}

private theorem chain_main_eq {u v : H1Function U} {G' : ℝ → ℝ}
    (hvgrad : ∀ x, v.grad x = G' (u x) • u.grad x) (η : Vec d → ℝ) :
    (fun x => η x ^ 2 * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) =
      fun x => η x ^ 2 * G' (u x) * vecDot (u.grad x) (matVecMul (a x) (u.grad x)) := by
  funext x
  rw [hvgrad, vecDot_smul_right, vecDot_comm (matVecMul (a x) (u.grad x))]
  ring

/-- **Chain-rule test, subharmonic.** If `v ≥ 0` a.e. and `∇v = G'(u) ∇u`,
then `∫ η² G'(u) ∇u·a∇u + ∫ 2ηv (a∇u·∇η) ≤ 0`, all pieces integrable. -/
theorem subharmonic_chainTest (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsub : IsWeakDivergenceFormSubharmonicOn a U u)
    (v : H1Function U) (G' : ℝ → ℝ) (hvgrad : ∀ x, v.grad x = G' (u x) • u.grad x)
    (hv : ∀ᵐ x ∂volumeOn U, 0 ≤ v x)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ U) :
    IntegrableOn (fun x => η x ^ 2 * G' (u x) *
        vecDot (u.grad x) (matVecMul (a x) (u.grad x))) U ∧
      IntegrableOn (fun x => 2 * η x * v x *
        vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x)) U ∧
      (∫ x in U, η x ^ 2 * G' (u x) * vecDot (u.grad x) (matVecMul (a x) (u.grad x))) +
          ∫ x in U, 2 * η x * v x *
            vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x) ≤ 0 := by
  have h := subharmonic_sqTest hU ha hEll hsub v hv hη hηc hηU
  rw [chain_main_eq hvgrad] at h
  exact h

/-- **Chain-rule test, superharmonic.** If `v ≥ 0` a.e. and `∇v = G'(u) ∇u`,
then `0 ≤ ∫ η² G'(u) ∇u·a∇u + ∫ 2ηv (a∇u·∇η)`, all pieces integrable. -/
theorem superharmonic_chainTest (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u)
    (v : H1Function U) (G' : ℝ → ℝ) (hvgrad : ∀ x, v.grad x = G' (u x) • u.grad x)
    (hv : ∀ᵐ x ∂volumeOn U, 0 ≤ v x)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ U) :
    IntegrableOn (fun x => η x ^ 2 * G' (u x) *
        vecDot (u.grad x) (matVecMul (a x) (u.grad x))) U ∧
      IntegrableOn (fun x => 2 * η x * v x *
        vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x)) U ∧
      0 ≤ (∫ x in U, η x ^ 2 * G' (u x) *
          vecDot (u.grad x) (matVecMul (a x) (u.grad x))) +
          ∫ x in U, 2 * η x * v x *
            vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x) := by
  have h := superharmonic_sqTest hU ha hEll hsuper v hv hη hηc hηU
  rw [chain_main_eq hvgrad] at h
  exact h

theorem memVectorL2On_classicalGradient {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) : MemVectorL2On U (classicalGradient η) := by
  intro i
  have hContinuous : Continuous (fun x => classicalGradient η x i) := by
    simpa only [classicalGradient_apply] using
      (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hCompact : HasCompactSupport (fun x => classicalGradient η x i) := by
    simpa only [classicalGradient_apply] using
      hηc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  exact (hContinuous.memLp_of_hasCompactSupport hCompact).restrict U

/-- **Logarithmic energy estimate.** For a supersolution `u ≥ δ > 0` a.e.,
`∫ η² ∇log u · a∇log u ≤ 4Λ ∫ |∇η|²` with `∇ log u = u⁻¹ ∇u`. -/
theorem superharmonic_log_energy (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u)
    {δ : ℝ} (hδ : 0 < δ) (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ U) :
    ∫ x in U, η x ^ 2 * vecDot ((u x)⁻¹ • u.grad x)
        (matVecMul (a x) ((u x)⁻¹ • u.grad x)) ≤
      4 * Λ * ∫ x in U, vecNormSq (classicalGradient η x) := by
  set v := invOfLowerBound hU u hδ hu
  set w := logOfLowerBound hU u hδ hu
  have hv0 : ∀ᵐ x ∂volumeOn U, 0 ≤ v x := hu.mono fun x hx => by
    change 0 ≤ (u x)⁻¹
    exact inv_nonneg.mpr (hδ.le.trans hx)
  obtain ⟨h1, h2, hle⟩ := superharmonic_chainTest hU ha hEll hsuper v
    (fun t => -(t ^ 2)⁻¹) (fun _ => rfl) hv0 hη hηc hηU
  set ξ : Vec d → Vec d := fun x => (u x)⁻¹ • u.grad x with hξdef
  have hξ : MemVectorL2On U ξ := w.gradMemL2
  have hmain : ∫ x in U, η x ^ 2 * (fun t => -(t ^ 2)⁻¹) (u x) *
      vecDot (u.grad x) (matVecMul (a x) (u.grad x)) =
      -∫ x in U, η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x)) := by
    rw [← integral_neg]
    congr 1
    funext x
    simp only [hξdef, matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
    by_cases h0 : u x = 0
    · simp [h0]
    · field_simp
  have hcross : ∫ x in U, 2 * η x * v x *
      vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x) =
      2 * ∫ x in U, η x * (fun _ => (1 : ℝ)) x *
        vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    simp only [hξdef, matVecMul_smul, vecDot_smul_left]
    change 2 * η x * (u x)⁻¹ * _ = _
    ring
  rw [hmain, hcross] at hle
  have htest : 1 * (∫ x in U, η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) +
      (-2) * (∫ x in U, η x * (fun _ => (1 : ℝ)) x *
        vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x)) ≤ 0 := by
    linarith
  have hωη : MemVectorL2On U (fun x => (fun _ => (1 : ℝ)) x • classicalGradient η x) := by
    simpa only [one_smul] using memVectorL2On_classicalGradient (U := U) hη hηc
  have habs := absorb hU.measurableSet ha hEll hξ hη hηc hωη one_pos htest
  simpa only [one_pow, one_mul, div_one, neg_sq, show (2 : ℝ) ^ 2 = 4 by norm_num]
    using habs

/-- **Logarithmic energy estimate, Euclidean form.** For a supersolution
`u ≥ δ > 0` a.e., `∫ η² |u⁻¹ ∇u|² ≤ 4Λ ∫ |∇η|²`. -/
theorem superharmonic_log_energy_euclidean (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u)
    {δ : ℝ} (hδ : 0 < δ) (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ U) :
    ∫ x in U, η x ^ 2 * vecNormSq ((u x)⁻¹ • u.grad x) ≤
      4 * Λ * ∫ x in U, vecNormSq (classicalGradient η x) := by
  have hE := superharmonic_log_energy hU ha hEll hsuper hδ hu hη hηc hηU
  set w := logOfLowerBound hU u hδ hu
  have hξ : MemVectorL2On U (fun x => (u x)⁻¹ • u.grad x) := w.gradMemL2
  have hηTop : MemLpOn U ⊤ η := memLpOn_top_of_contDiff hη hηc
  have hA : MemVectorL2On U (fun x => η x • ((u x)⁻¹ • u.grad x)) := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using (hξ i).fun_mul hηTop
  have hint1 : IntegrableOn (fun x => η x ^ 2 * vecNormSq ((u x)⁻¹ • u.grad x)) U := by
    simpa only [vecNormSq_smul] using integrableOn_vecNormSq_of_memVectorL2On hA
  have hF := memVectorL2On_matVecMul_of_aemeasurable hU.measurableSet ha hEll hξ
  have hη2 : MemLpOn U ⊤ (fun x => η x ^ 2) := by
    have hsq : (fun x => η x ^ 2) = η * η := by
      funext x
      simp only [Pi.mul_apply, pow_two]
    rw [hsq]
    exact hηTop.mul hηTop
  have hint2 : IntegrableOn (fun x => η x ^ 2 * vecDot ((u x)⁻¹ • u.grad x)
      (matVecMul (a x) ((u x)⁻¹ • u.grad x))) U := by
    have hC : MemVectorL2On U (fun x => η x ^ 2 • ((u x)⁻¹ • u.grad x)) := by
      intro i
      simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using (hξ i).fun_mul hη2
    simpa only [vecDot_smul_left] using integrableOn_vecDot_of_memVectorL2On hC hF
  refine le_trans (setIntegral_mono_on hint1 hint2 hU.measurableSet fun x hx => ?_) hE
  exact mul_le_mul_of_nonneg_left (vecNormSq_le_vecDot_matVecMul (hEll x hx) _)
    (sq_nonneg _)

/-- **Logarithmic energy on balls.** For a supersolution `u ≥ δ > 0` a.e. on
`U ⊇ euclideanBall x₀ (2R)`:
`∫_{B_R(x₀)} |u⁻¹ ∇u|² ≤ 4Λ (32/R)² |B_{2R}(x₀)|`. -/
theorem superharmonic_log_energy_ball (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u)
    {δ : ℝ} (hδ : 0 < δ) (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x)
    {x₀ : Vec d} {R : ℝ} (hR : 0 < R) (hball : euclideanBall x₀ (2 * R) ⊆ U) :
    ∫ x in euclideanBall x₀ R, vecNormSq ((u x)⁻¹ • u.grad x) ≤
      4 * Λ * (32 / R) ^ 2 * (volume (euclideanBall x₀ (2 * R))).toReal := by
  have hRR : R < 2 * R := by linarith
  let η := quantitativeBallCutoff x₀ hR.le hRR
  have hK : 32 / (2 * R - R) = 32 / R := by congr 1; ring
  have hE := superharmonic_log_energy_euclidean hU ha hEll hsuper hδ hu η.smooth
    η.hasCompactSupport (η.tsupport_subset.trans hball)
  set w := logOfLowerBound hU u hδ hu
  have hξ : MemVectorL2On U (fun x => (u x)⁻¹ • u.grad x) := w.gradMemL2
  have hηTop : MemLpOn U ⊤ η.toFun := memLpOn_top_of_contDiff η.smooth η.hasCompactSupport
  have hA : MemVectorL2On U (fun x => η.toFun x • ((u x)⁻¹ • u.grad x)) := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using (hξ i).fun_mul hηTop
  have hint1 : IntegrableOn
      (fun x => η.toFun x ^ 2 * vecNormSq ((u x)⁻¹ • u.grad x)) U := by
    simpa only [vecNormSq_smul] using integrableOn_vecNormSq_of_memVectorL2On hA
  have hinner : euclideanBall x₀ R ⊆ U :=
    (euclideanBall_mono hR.le hRR.le).trans hball
  have h1 : ∫ x in euclideanBall x₀ R, vecNormSq ((u x)⁻¹ • u.grad x) =
      ∫ x in euclideanBall x₀ R, η.toFun x ^ 2 * vecNormSq ((u x)⁻¹ • u.grad x) :=
    setIntegral_congr_fun (measurableSet_euclideanBall x₀ R) fun x hx => by
      simp only [η.eq_one_on_inner x hx, one_pow, one_mul]
  have h2 : ∫ x in euclideanBall x₀ R, η.toFun x ^ 2 * vecNormSq ((u x)⁻¹ • u.grad x) ≤
      ∫ x in U, η.toFun x ^ 2 * vecNormSq ((u x)⁻¹ • u.grad x) :=
    setIntegral_mono_set hint1
      (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _))
      (Filter.Eventually.of_forall hinner)
  have hgradInt : IntegrableOn (fun x => vecNormSq (classicalGradient η.toFun x))
      (euclideanBall x₀ (2 * R)) :=
    integrableOn_vecNormSq_of_memVectorL2On
      (memVectorL2On_classicalGradient η.smooth η.hasCompactSupport)
  have h3 : ∫ x in U, vecNormSq (classicalGradient η.toFun x) =
      ∫ x in euclideanBall x₀ (2 * R), vecNormSq (classicalGradient η.toFun x) :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hball
      fun x hx => by
        rw [η.classicalGradient_eq_zero_of_not_mem_outer hx.2]
        simp [vecNormSq, vecDot]
  have h4 : ∫ x in euclideanBall x₀ (2 * R), vecNormSq (classicalGradient η.toFun x) ≤
      ∫ _ in euclideanBall x₀ (2 * R), (32 / R) ^ 2 := by
    refine setIntegral_mono_on hgradInt ?_ (measurableSet_euclideanBall x₀ _) fun x _ => ?_
    · exact integrableOn_const (volume_euclideanBall_ne_top x₀ (by linarith))
    · rw [← vecEuclideanNorm_sq, ← hK]
      exact pow_le_pow_left₀ (vecEuclideanNorm_nonneg _) (η.gradient_bound x) 2
  rw [setIntegral_const, smul_eq_mul] at h4
  have hΛ : 0 ≤ Λ := by
    obtain ⟨y, hy⟩ : (euclideanBall x₀ (2 * R)).Nonempty :=
      euclideanBall_nonempty x₀ (by linarith)
    exact (hEll y (hball hy)).Lam_pos.le
  calc _ = _ := h1
    _ ≤ _ := h2
    _ ≤ 4 * Λ * ∫ x in U, vecNormSq (classicalGradient η.toFun x) := hE
    _ ≤ 4 * Λ * ((volume (euclideanBall x₀ (2 * R))).toReal * (32 / R) ^ 2) := by
      rw [h3]
      exact mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by ring

end DGNM

end PDE
