module

public import EllipticRegularity.DeGiorgi.OneStep.Core
public import EllipticRegularity.DeGiorgi.OneStep.Conv
public import EllipticRegularity.DeGiorgi.OneStep.PowerFn
public import EllipticRegularity.DeGiorgi.OneStep.PowerFn2
public import PDEFoundation.Sobolev.H1.Composition

/-!
# Assembly pieces for the Moser one-step estimates

* `exists_wv`: the `H¹` functions `w = G₁(u)` and `v = G₂(u)` with the expected gradients;
* `htest_sub`, `htest_super`: the tested inequalities in the form consumed by `core`;
* `finish`: the conversion of the `core` estimate into the reverse Hölder step for `f`.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace PDE.DGNMOneStep

open MeasureTheory PDE

variable {d : ℕ} {U : Set (Vec d)}

/-- The `H¹` functions `w = u ^ σ` and `v = u ^ (2σ-1)` on a region where `u` ranges in `S`. -/
theorem exists_wv (hU : IsOpenBoundedConvexDomain U) (u : H1Function U) {S : Set ℝ}
    (hSpos : ∀ t ∈ S, 0 < t) {σ : ℝ} {G₁ G₂ : ℝ → ℝ}
    (hG₁ : ContDiff ℝ 1 G₁) (hB₁ : ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |deriv G₁ t| ≤ B)
    (hG₂ : ContDiff ℝ 1 G₂) (hB₂ : ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |deriv G₂ t| ≤ B)
    (hn₂ : ∀ t, 0 ≤ G₂ t)
    (hp₁ : ∀ t ∈ S, G₁ t = t ^ σ ∧ deriv G₁ t = σ * t ^ (σ - 1))
    (hp₂ : ∀ t ∈ S, G₂ t = t ^ (2 * σ - 1) ∧ deriv G₂ t = (2 * σ - 1) * t ^ (2 * σ - 1 - 1))
    {R : ℝ} (hS : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) R), u x ∈ S) :
    ∃ w v : H1Function U, (∀ x, 0 ≤ v x) ∧
      ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) R),
        0 < u x ∧ w x = u x ^ σ ∧ w.grad x = (σ * u x ^ (σ - 1)) • u.grad x ∧
          v x = u x ^ (2 * σ - 1) ∧
          v.grad x = ((2 * σ - 1) * u x ^ (2 * σ - 2)) • u.grad x := by
  obtain ⟨B₁, hB₁0, hB₁⟩ := hB₁
  obtain ⟨B₂, hB₂0, hB₂⟩ := hB₂
  refine ⟨u.compContDiffOfDerivBounded hU hG₁ hB₁0 hB₁,
    u.compContDiffOfDerivBounded hU hG₂ hB₂0 hB₂, fun x => hn₂ _, ?_⟩
  filter_upwards [hS] with x hx
  obtain ⟨h1, h2⟩ := hp₁ _ hx
  obtain ⟨h3, h4⟩ := hp₂ _ hx
  have e : 2 * σ - 1 - 1 = 2 * σ - 2 := by ring
  rw [e] at h4
  refine ⟨hSpos _ hx, ?_, ?_, ?_, ?_⟩
  · simpa using h1
  · funext i
    simp [h2]
  · simpa using h3
  · funext i
    simp [h4]

/-- The tested inequality for a subsolution (sign `τ = 1`). -/
theorem htest_sub (hU : IsOpenBoundedConvexDomain U) {Λ : ℝ} {a : CoeffField d}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x)) {u : H1Function U}
    (hsub : IsWeakDivergenceFormSubharmonicOn a U u) (v : H1Function U) (hv : ∀ x, 0 ≤ v x)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ U) :
    IntegrableOn (fun x => η x ^ 2 *
      vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) U ∧
    IntegrableOn (fun x => 2 * η x * v x *
      vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x)) U ∧
    (1 : ℝ) * ((∫ x in U, η x ^ 2 * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) +
      ∫ x in U, 2 * η x * v x *
        vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x)) ≤ 0 := by
  obtain ⟨h1, h2, h3⟩ := DGNM.subharmonic_sqTest hU ha hEll hsub v
    (Filter.Eventually.of_forall hv) hη hηc hηU
  exact ⟨h1, h2, by linarith⟩

/-- The tested inequality for a supersolution (sign `τ = -1`). -/
theorem htest_super (hU : IsOpenBoundedConvexDomain U) {Λ : ℝ} {a : CoeffField d}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x)) {u : H1Function U}
    (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u) (v : H1Function U)
    (hv : ∀ x, 0 ≤ v x)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ U) :
    IntegrableOn (fun x => η x ^ 2 *
      vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) U ∧
    IntegrableOn (fun x => 2 * η x * v x *
      vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x)) U ∧
    (-1 : ℝ) * ((∫ x in U, η x ^ 2 * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) +
      ∫ x in U, 2 * η x * v x *
        vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x)) ≤ 0 := by
  obtain ⟨h1, h2, h3⟩ := DGNM.superharmonic_sqTest hU ha hEll hsuper v
    (Filter.Eventually.of_forall hv) hη hηc hηU
  exact ⟨h1, h2, by linarith⟩

/-- The dimensional constant of the one-step estimates. -/
noncomputable def oneStepConst (d : ℕ) : ℝ := 2048 * (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2

theorem oneStepConst_pos (d : ℕ) : 0 < oneStepConst d := by
  unfold oneStepConst
  have := zeroBoundarySobolevConstantTwo_pos d
  have h : (0 : ℝ) < (zeroBoundarySobolevConstantTwo d : ℝ) := by exact_mod_cast this
  positivity

/-- The final conversion: the `core` estimate for `w` gives the reverse Hölder step for `f`
whenever `w = f ^ (p/2)` a.e. on `B_R`. -/
theorem finish (hd : 3 ≤ d) (hU : IsOpenBoundedConvexDomain U) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    {a : CoeffField d} (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    (u w v : H1Function U) {σ τ : ℝ} (hσ : σ ≠ 0) (hτ : τ ^ 2 = 1)
    (hpos : 0 < τ * (2 * σ - 1)) {R : ℝ} (hRU : euclideanBall (0 : Vec d) R ⊆ U)
    (hreg : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) R),
      0 < u x ∧ w x = u x ^ σ ∧ w.grad x = (σ * u x ^ (σ - 1)) • u.grad x ∧
        v x = u x ^ (2 * σ - 1) ∧
        v.grad x = ((2 * σ - 1) * u x ^ (2 * σ - 2)) • u.grad x)
    (htest : ∀ {η : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ U →
      IntegrableOn (fun x => η x ^ 2 *
        vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) U ∧
      IntegrableOn (fun x => 2 * η x * v x *
        vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x)) U ∧
      τ * ((∫ x in U, η x ^ 2 *
          vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) +
        ∫ x in U, 2 * η x * v x *
          vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x)) ≤ 0)
    (f : Vec d → ℝ) {p κ : ℝ} (hp : 0 < p) (hp2 : 4 * σ ^ 2 = p ^ 2)
    (hκ : (2 * σ - 1) ^ 2 = κ ^ 2)
    (hf : AEStronglyMeasurable f (volumeOn U))
    (hf0 : ∀ᵐ x ∂volumeOn U, 0 ≤ f x)
    (hwf : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) R), w x = f x ^ (p / 2))
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hsR : s ≤ R) :
    eLpNorm f (ENNReal.ofReal (p * ((d : ℝ) / (d - 2)))) (volumeOn (euclideanBall (0 : Vec d) r)) ≤
      ENNReal.ofReal ((oneStepConst d / (s - r) ^ 2 * (Λ * p ^ 2 / κ ^ 2 + 1)) ^ (1 / p)) *
        eLpNorm f (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) s)) := by
  have hs0 : 0 ≤ s := hr.trans hrs.le
  have hrR : euclideanBall (0 : Vec d) r ⊆ euclideanBall (0 : Vec d) R :=
    euclideanBall_mono hr (hrs.le.trans hsR)
  have hsR' : euclideanBall (0 : Vec d) s ⊆ euclideanBall (0 : Vec d) R :=
    euclideanBall_mono hs0 hsR
  have hrU : euclideanBall (0 : Vec d) r ⊆ U := hrR.trans hRU
  have hsU : euclideanBall (0 : Vec d) s ⊆ U := hsR'.trans hRU
  have hcore := core hd hU hΛ hEll u w v hσ hτ hpos hRU hreg htest hr hrs hsR
  have hwr : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) r), w x = f x ^ (p / 2) :=
    ae_restrict_of_ae_restrict_of_subset hrR hwf
  have hws : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) s), w x = f x ^ (p / 2) :=
    ae_restrict_of_ae_restrict_of_subset hsR' hwf
  have hcore' : eLpNorm (fun x => f x ^ (p / 2)) (ENNReal.ofReal (sobolevConjugate d 2))
        (volumeOn (euclideanBall (0 : Vec d) r)) ≤
      ENNReal.ofReal ((zeroBoundarySobolevConstantTwo d : ℝ) *
        Real.sqrt (2 * (4 * σ ^ 2 * Λ / (2 * σ - 1) ^ 2 + 1) * (32 / (s - r)) ^ 2)) *
        eLpNorm (fun x => f x ^ (p / 2)) 2 (volumeOn (euclideanBall (0 : Vec d) s)) := by
    rw [← eLpNorm_congr_ae hwr, ← eLpNorm_congr_ae hws]
    exact hcore
  have hq : 0 < sobolevConjugate d 2 := by
    apply sobolevConjugate_pos (by norm_num)
    exact_mod_cast (by omega : 2 < d)
  have hCS : 0 ≤ (zeroBoundarySobolevConstantTwo d : ℝ) := NNReal.coe_nonneg _
  have hsr : 0 < s - r := sub_pos.mpr hrs
  set Z : ℝ := 2 * (4 * σ ^ 2 * Λ / (2 * σ - 1) ^ 2 + 1) * (32 / (s - r)) ^ 2 with hZ
  have hZ0 : 0 ≤ Z := by
    have hθ : 0 ≤ 4 * σ ^ 2 * Λ / (2 * σ - 1) ^ 2 := by positivity
    positivity
  have hmeas₁ : AEStronglyMeasurable f (volumeOn (euclideanBall (0 : Vec d) r)) :=
    hf.mono_measure (Measure.restrict_mono hrU le_rfl)
  have hmeas₂ : AEStronglyMeasurable f (volumeOn (euclideanBall (0 : Vec d) s)) :=
    hf.mono_measure (Measure.restrict_mono hsU le_rfl)
  have hres := eLpNorm_le_of_rpow_half hp hq (by positivity) hmeas₁ hmeas₂
    (ae_restrict_of_ae_restrict_of_subset hrU hf0)
    (ae_restrict_of_ae_restrict_of_subset hsU hf0) hcore'
  have hexp : p * (sobolevConjugate d 2 / 2) = p * ((d : ℝ) / (d - 2)) := by
    have : (d : ℝ) - 2 ≠ 0 := by
      have : (2 : ℝ) < d := by exact_mod_cast (by omega : 2 < d)
      linarith
    unfold sobolevConjugate
    field_simp
  have hconst : ((zeroBoundarySobolevConstantTwo d : ℝ) * Real.sqrt Z) ^ (2 / p) =
      (oneStepConst d / (s - r) ^ 2 * (Λ * p ^ 2 / κ ^ 2 + 1)) ^ (1 / p) := by
    have h1 : (zeroBoundarySobolevConstantTwo d : ℝ) * Real.sqrt Z =
        (oneStepConst d / (s - r) ^ 2 * (Λ * p ^ 2 / κ ^ 2 + 1)) ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq hCS, ← Real.sqrt_mul (sq_nonneg _)]
      congr 1
      rw [hZ, ← hκ, ← hp2]
      unfold oneStepConst
      field_simp
      ring
    rw [h1, ← Real.rpow_mul (by
      have : 0 ≤ oneStepConst d := (oneStepConst_pos d).le
      have hκ0 : 0 ≤ Λ * p ^ 2 / κ ^ 2 := by positivity
      positivity)]
    congr 1
    field_simp
  rw [hexp, hconst] at hres
  exact hres

end PDE.DGNMOneStep
