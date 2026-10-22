module

public import PDEFoundation.PDE.BallDirichletGradient
public import PDEFoundation.PDE.CoefficientForcingScale
public import PDEFoundation.PDE.PerturbationL2
public import PDEFoundation.Measure.ForcingScale
public import PDEFoundation.Sobolev.H1.Pairing

/-! # Lax--Milgram for general elliptic coefficients on the unit ball

The perturbative Dirichlet operator of the foundation solves the zero-boundary
divergence-form problem for coefficients within `delta < 1` of the identity.
A general elliptic field with `IsEllipticMatrix 1 Λ` is brought into that class
by the scalar rescaling `a ↦ Λ⁻² a`. -/

@[expose] public section

open scoped ENNReal

namespace PDE.MeyersDuality

open MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem vecNormSq_sub_smul_expand (s : ℝ) (y x : Vec d) :
    vecNormSq (s • y - x) =
      s ^ 2 * vecNormSq y - 2 * s * vecDot x y + vecNormSq x := by
  have h : s • y - x = s • y + (-1 : ℝ) • x := by
    rw [neg_one_smul, sub_eq_add_neg]
  rw [h, vecNormSq_add_expand, vecNormSq_smul, vecNormSq_smul]
  have : vecDot (s • y) ((-1 : ℝ) • x) = -(s * vecDot x y) := by
    simp only [vecDot, Pi.smul_apply, smul_eq_mul, ← Finset.sum_neg_distrib,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [this]
  ring

/-- Rescaling an elliptic matrix by `Λ⁻²` lands in the identity-perturbation class. -/
theorem isMatrixPerturbationLE_inv_sq_smul_of_isEllipticMatrix
    {Λ : ℝ} {A : Mat d} (hA : IsEllipticMatrix 1 Λ A) :
    IsMatrixPerturbationLE (Real.sqrt (1 - (Λ ^ 2)⁻¹)) ((Λ ^ 2)⁻¹ • A) (1 : Mat d) := by
  intro ξ
  have hΛ : 0 < Λ := hA.Lam_pos
  set s : ℝ := (Λ ^ 2)⁻¹ with hs
  have hsΛ : s * Λ ^ 2 = 1 := by rw [hs]; field_simp
  have hmul : matVecMul (s • A - (1 : Mat d)) ξ = s • matVecMul A ξ - ξ := by
    change (s • A - (1 : Mat d)).mulVec ξ = s • A.mulVec ξ - ξ
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hup := vecNormSq_matVecMul_le_of_isEllipticMatrix hA ξ
  have hlow := hA.coercive ξ
  rw [one_mul] at hlow
  have hsq : vecNormSq (matVecMul (s • A - (1 : Mat d)) ξ) ≤ (1 - s) * vecNormSq ξ := by
    rw [hmul, vecNormSq_sub_smul_expand]
    have hs0 : 0 ≤ s := by rw [hs]; positivity
    have h1 : s ^ 2 * vecNormSq (matVecMul A ξ) ≤ s ^ 2 * (Λ ^ 2 * vecNormSq ξ) :=
      mul_le_mul_of_nonneg_left hup (sq_nonneg s)
    have h2 : s ^ 2 * (Λ ^ 2 * vecNormSq ξ) = s * vecNormSq ξ := by
      calc s ^ 2 * (Λ ^ 2 * vecNormSq ξ) = s * (s * Λ ^ 2) * vecNormSq ξ := by ring
        _ = s * vecNormSq ξ := by rw [hsΛ]; ring
    have h3 : 2 * s * vecNormSq ξ ≤ 2 * s * vecDot ξ (matVecMul A ξ) :=
      mul_le_mul_of_nonneg_left hlow (by positivity)
    nlinarith
  have hs1 : s ≤ 1 := by
    have hΛ1 : 1 ≤ Λ := hA.lam_le_Lam
    rw [hs]
    have : 1 ≤ Λ ^ 2 := by nlinarith
    exact inv_le_one_of_one_le₀ this
  unfold vecEuclideanNorm
  calc Real.sqrt (vecNormSq (matVecMul (s • A - 1) ξ))
      ≤ Real.sqrt ((1 - s) * vecNormSq ξ) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (1 - s) * Real.sqrt (vecNormSq ξ) :=
      Real.sqrt_mul (by linarith) _

/-- Multiplication by a measurable a.e. elliptic field preserves native `L²`. -/
theorem memVectorL2On_matVecMul_of_ae_elliptic
    {Λ : ℝ} {U : Set (Vec d)} (hU : MeasurableSet U) {a : CoeffField d}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hell : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {G : Vec d → Vec d} (hG : MemVectorL2On U G) :
    MemVectorL2On U (fun x => matVecMul (a x) (G x)) := by
  classical
  intro i
  have hsum : MemLpOn U (2 : ℝ≥0∞)
      (fun x => ∑ j : Fin d, a x i j * G x j) := by
    refine MeasureTheory.memLp_finsetSum
      (s := Finset.univ)
      (f := fun j : Fin d => fun x : Vec d => a x i j * G x j) ?_
    intro j _
    have hGj : MemLpOn U (2 : ℝ≥0∞) (fun x => G x j) := hG j
    have hterm_meas : AEStronglyMeasurable (fun x => a x i j * G x j) (volumeOn U) :=
      (ha i j).aestronglyMeasurable.mul hGj.aestronglyMeasurable
    have hmem : ∀ᵐ x ∂ volumeOn U, x ∈ U :=
      (MeasureTheory.ae_restrict_iff' hU).2 (Filter.Eventually.of_forall fun x hx => hx)
    have hbound : ∀ᵐ x ∂ volumeOn U, ‖a x i j * G x j‖ ≤ Λ * ‖G x j‖ := by
      filter_upwards [hmem] with x hx
      calc ‖a x i j * G x j‖ = |a x i j| * ‖G x j‖ := by
            rw [norm_mul, Real.norm_eq_abs]
        _ ≤ Λ * ‖G x j‖ :=
          mul_le_mul_of_nonneg_right (abs_apply_le_of_isEllipticMatrix (hell x hx) i j)
            (norm_nonneg _)
    exact MeasureTheory.MemLp.of_le_mul hGj hterm_meas hbound
  simpa only [matVecMul] using hsum

theorem memVectorL2On_smul {U : Set (Vec d)} {F : Vec d → Vec d}
    (hF : MemVectorL2On U F) (c : ℝ) : MemVectorL2On U (fun x => c • F x) := by
  intro i
  have := (hF i).const_mul c
  simpa only [Pi.smul_apply, smul_eq_mul] using this

/-- An `L²`-forced smooth-test weak solution on the unit ball with elliptic coefficients
tests against all of `H¹₀`. -/
theorem IsWeakDivergenceFormSolutionOn.toH10 {Λ : ℝ} {a : CoeffField d}
    {U : Set (Vec d)} (hU : MeasurableSet U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hell : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} {F : Vec d → Vec d} (hF : MemVectorL2On U F)
    (hsol : IsWeakDivergenceFormSolutionOn a U u 0 F) :
    IsWeakDivergenceFormH10SolutionOn a U u 0 F := by
  have hL2 : IsWeakDivergenceFormL2SolutionOn a U u 0 F :=
    { flux_memL2 := memVectorL2On_matVecMul_of_ae_elliptic hU ha hell u.gradMemL2
      source_memL2 := MemLp.zero
      forcing_memL2 := hF
      identity := fun φ => (hsol φ).2 }
  exact hL2.toH10SolutionOn

/-- Existence of a zero-boundary weak solution for a general elliptic field on the unit ball
with `L²` divergence forcing (Lax--Milgram, via the perturbative operator after rescaling). -/
theorem exists_h10_solution_of_elliptic (hd : 0 < d) {Λ : ℝ} {a : CoeffField d}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x))
    {F : Vec d → Vec d} (hF : MemVectorL2On (euclideanBall (0 : Vec d) 1) F) :
    ∃ w : H10Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) w.toH1Function 0 F := by
  have h0 : (0 : Vec d) ∈ euclideanBall (0 : Vec d) 1 := by
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt one_pos]
    simp [vecEuclideanNorm, vecNormSq, vecDot]
  have hA0 := hell 0 h0
  have hΛ : 0 < Λ := hA0.Lam_pos
  set s : ℝ := (Λ ^ 2)⁻¹ with hs
  have hspos : 0 < s := by rw [hs]; positivity
  have hs1 : s ≤ 1 := by
    have hΛ1 : 1 ≤ Λ := hA0.lam_le_Lam
    rw [hs]
    have : 1 ≤ Λ ^ 2 := by nlinarith
    exact inv_le_one_of_one_le₀ this
  have hδ0 : 0 ≤ Real.sqrt (1 - s) := Real.sqrt_nonneg _
  have hδ1 : Real.sqrt (1 - s) < 1 := by
    rw [Real.sqrt_lt' one_pos]; nlinarith
  have hb : ∀ i j, AEMeasurable (fun x => (s • a x) i j)
      (volumeOn (euclideanBall (0 : Vec d) 1)) := by
    intro i j
    simpa only [Matrix.smul_apply, smul_eq_mul] using (ha i j).const_mul s
  have hclose : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
      IsMatrixPerturbationLE (Real.sqrt (1 - s)) (s • a x) (1 : Mat d) := by
    have hmem : ∀ᵐ x ∂ volumeOn (euclideanBall (0 : Vec d) 1),
        x ∈ euclideanBall (0 : Vec d) 1 :=
      (MeasureTheory.ae_restrict_iff' (measurableSet_euclideanBall _ _)).2
        (Filter.Eventually.of_forall fun x hx => hx)
    filter_upwards [hmem] with x hx
    exact isMatrixPerturbationLE_inv_sq_smul_of_isEllipticMatrix (hell x hx)
  obtain ⟨w, -, hw⟩ := exists_ballDirichletGradient_solution hd 0 1 one_pos
    (fun x => s • a x) (Real.sqrt (1 - s)) hδ0 hδ1 hb hclose
    (fun x => s • F x) (memVectorL2On_smul hF s)
  refine ⟨w, ?_⟩
  have hsm := (hw.toIsWeakDivergenceFormSolutionOn (isOpen_euclideanBall _ _)).smul_coefficient_source_forcing
    s⁻¹
  have e1 : (fun x => s⁻¹ • (s • a x)) = a := by
    funext x; rw [smul_smul, inv_mul_cancel₀ hspos.ne', one_smul]
  have e2 : (fun x => s⁻¹ • (s • F x)) = F := by
    funext x; rw [smul_smul, inv_mul_cancel₀ hspos.ne', one_smul]
  have e3 : (fun x : Vec d => s⁻¹ * (0 : Vec d → ℝ) x) = 0 := by
    funext x; simp
  rw [e1, e2, e3] at hsm
  exact hsm

end

end PDE.MeyersDuality
