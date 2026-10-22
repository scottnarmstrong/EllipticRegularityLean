module

public import EllipticRegularity.DeGiorgi.OneStep.Energy
public import EllipticRegularity.DeGiorgi.OneStep.Sob

/-!
# The unified one-step estimate for `w = u ^ σ`

Given the tested inequality for the cutoff `η` (sub/super form encoded by the sign `τ`),
this proves `‖w‖_{L^{2*}(B_r)} ≤ C_S √Θ ‖w‖_{L²(B_s)}` with the explicit
`Θ = 2 (4σ²Λ/(2σ-1)² + 1) (32/(s-r))²`.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace PDE.DGNMOneStep

open MeasureTheory PDE

variable {d : ℕ} {U : Set (Vec d)}

/-- The unified one-step estimate. -/
theorem core (hd : 3 ≤ d) (hU : IsOpenBoundedConvexDomain U) {Λ : ℝ} (hΛ : 0 ≤ Λ) {a : CoeffField d}
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    (u w v : H1Function U) {σ τ : ℝ} (hσ : σ ≠ 0)
    (hτ : τ ^ 2 = 1) (hpos : 0 < τ * (2 * σ - 1)) {R : ℝ} (hRU : euclideanBall (0 : Vec d) R ⊆ U)
    (hreg : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) R),
      0 < u x ∧ w x = u x ^ σ ∧ w.grad x = (σ * u x ^ (σ - 1)) • u.grad x ∧
        v x = u x ^ (2 * σ - 1) ∧
        v.grad x = ((2 * σ - 1) * u x ^ (2 * σ - 2)) • u.grad x)
    (htest : ∀ {η : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ U →
      IntegrableOn (fun x => η x ^ 2 *
        vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) U ∧
      IntegrableOn (fun x => 2 * η x * v x *
        vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x))
          U ∧
      τ * ((∫ x in U, η x ^ 2 *
          vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) +
        ∫ x in U, 2 * η x * v x *
          vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x)) ≤ 0)
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hsR : s ≤ R) :
    eLpNorm w.toFun (ENNReal.ofReal (sobolevConjugate d 2))
        (volumeOn (euclideanBall (0 : Vec d) r)) ≤
      ENNReal.ofReal ((zeroBoundarySobolevConstantTwo d : ℝ) *
        Real.sqrt (2 * (4 * σ ^ 2 * Λ / (2 * σ - 1) ^ 2 + 1) * (32 / (s - r)) ^ 2)) *
        eLpNorm w.toFun 2 (volumeOn (euclideanBall (0 : Vec d) s)) := by
  have hs0 : 0 ≤ s := hr.trans hrs.le
  have hball : euclideanBall (0 : Vec d) s ⊆ U :=
    (euclideanBall_mono hs0 hsR).trans hRU
  have hballR : euclideanBall (0 : Vec d) s ⊆ euclideanBall (0 : Vec d) R :=
    euclideanBall_mono hs0 hsR
  set η := quantitativeBallCutoff (0 : Vec d) hr hrs with hη
  have hηU : tsupport η.toFun ⊆ U := η.tsupport_subset.trans hball
  obtain ⟨hint1, hint2, hsign⟩ := htest η.smooth η.hasCompactSupport hηU
  have hreg' : ∀ᵐ x ∂volumeOn U, η x ≠ 0 →
      0 < u x ∧ w x = u x ^ σ ∧ w.grad x = (σ * u x ^ (σ - 1)) • u.grad x ∧
        v x = u x ^ (2 * σ - 1) ∧
        v.grad x = ((2 * σ - 1) * u x ^ (2 * σ - 2)) • u.grad x := by
    have h1 := (ae_restrict_iff' (isOpen_euclideanBall (0 : Vec d) R).measurableSet).mp hreg
    have h2 : ∀ᵐ x ∂(volume : Measure (Vec d)), x ∈ U → (η x ≠ 0 →
        0 < u x ∧ w x = u x ^ σ ∧ w.grad x = (σ * u x ^ (σ - 1)) • u.grad x ∧
          v x = u x ^ (2 * σ - 1) ∧
          v.grad x = ((2 * σ - 1) * u x ^ (2 * σ - 2)) • u.grad x) := by
      filter_upwards [h1] with x hx _ hηx
      have hmem : x ∈ tsupport η.toFun := subset_tsupport _ (Function.mem_support.mpr hηx)
      exact hx (hballR (η.tsupport_subset hmem))
    exact (ae_restrict_iff' hU.measurableSet).mpr h2
  obtain ⟨hJ1int, hJ1⟩ := energy_of_test hU hEll hΛ u w v hσ hτ hpos η hball hreg'
    ⟨hint1, hint2, hsign⟩
  -- integrability of `η² |∇w|²`
  have hηTop : MemLpOn U ∞ η.toFun := W1pFunction.cutoff_memLpTop η
  have hweighted : MemVectorL2On U (fun x => η x • w.grad x) := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using (w.gradMemL2 i).fun_mul hηTop
  have hweightedInt : IntegrableOn (fun x => η x ^ 2 * vecNormSq (w.grad x)) U := by
    have hraw := integrableOn_vecNormSq_of_memVectorL2On hweighted
    simpa only [vecNormSq_smul] using hraw
  have hle : (∫ x in U, η x ^ 2 * vecNormSq (w.grad x)) ≤
      ∫ x in U, η x ^ 2 * vecDot (w.grad x) (matVecMul (a x) (w.grad x)) := by
    apply integral_mono_ae hweightedInt hJ1int
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact mul_le_mul_of_nonneg_left (DGNM.vecNormSq_le_vecDot_matVecMul (hEll x hx) _)
      (sq_nonneg _)
  set θ : ℝ := 4 * σ ^ 2 * Λ / (2 * σ - 1) ^ 2 with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hprod := H1Function.setIntegral_vecNormSq_mulCutoffToH10_grad_le w η hU hball
  have hK : (32 / (s - r)) ^ 2 = (32 / (s - r)) ^ 2 := rfl
  have hE : ∫ x in U, vecNormSq
        ((w.mulCutoffToH10 hU η hball).toH1Function.grad x) ≤
      (2 * (θ + 1) * (32 / (s - r)) ^ 2) * ∫ x in euclideanBall (0 : Vec d) s, w x ^ 2 := by
    have hW0 : 0 ≤ ∫ x in euclideanBall (0 : Vec d) s, w x ^ 2 :=
      integral_nonneg fun x => sq_nonneg _
    have hK0 : 0 ≤ (32 / (s - r)) ^ 2 := sq_nonneg _
    calc _ ≤ 2 * (∫ x in U, η x ^ 2 * vecNormSq (w.grad x)) +
          2 * (32 / (s - r)) ^ 2 * (∫ x in euclideanBall (0 : Vec d) s, (w x) ^ 2) := hprod
      _ ≤ 2 * (θ * ((32 / (s - r)) ^ 2 * ∫ x in euclideanBall (0 : Vec d) s, w x ^ 2)) +
          2 * (32 / (s - r)) ^ 2 * (∫ x in euclideanBall (0 : Vec d) s, (w x) ^ 2) := by
        have := hle.trans hJ1
        linarith
      _ = _ := by ring
  have hΘ : 0 ≤ 2 * (θ + 1) * (32 / (s - r)) ^ 2 := by positivity
  exact sobolev_step hd hU w hr hrs hball hΘ hE

end PDE.DGNMOneStep
