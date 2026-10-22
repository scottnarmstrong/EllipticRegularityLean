module

public import PDEFoundation.PDE.DGNM.ChainTests

/-!
# Energy estimates for powers (the Moser test computations)

* `subharmonic_rpow_energy` (manuscript Proposition 4.13, Step 1): for a
  subsolution with `δ ≤ u ≤ M` a.e. (`0 < δ`) and `p > 1`, testing with
  `η² u^{p-1}` gives, with `w = u^{p/2}`,
  `∫ |∇(η w)|² ≤ (2Λp²/(p-1)² + 2) ∫ u^p |∇η|²`.
* `superharmonic_rpow_energy` (manuscript Proposition 4.14, Step 1, (4.70)): for
  a supersolution with `u ≥ δ > 0` a.e. and `p > -1`, `p ≠ 0`, testing with
  `η² u^{-(1+p)}` gives, with `w = u^{-p/2}`,
  `∫ |∇(η w)|² ≤ (2Λp²/(1+p)² + 2) ∫ u^{-p} |∇η|²`.

Here `∇(η w) = η ∇w + w ∇η` and `∇w = (s u^{s-1}) ∇u` (`s = p/2`, resp.
`s = -p/2`) are written out; they are literally the gradients of the `H¹`
functions `rpowOfBounds hU u hδ hδM hu (p/2)` (resp.
`rpowOfLowerBound hU u hδ hu (-p/2) _`) multiplied by `η`.
-/

@[expose] public section

namespace PDE

namespace DGNM

open MeasureTheory

variable {d : ℕ} {U : Set (Vec d)} {Λ : ℝ} {a : CoeffField d}

private theorem rpow_add_self {t : ℝ} (ht : 0 < t) (s : ℝ) :
    t ^ s * t ^ s = t ^ (s + s) :=
  (Real.rpow_add ht s s).symm

/-- **Moser energy estimate for subsolutions.** -/
theorem subharmonic_rpow_energy (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsub : IsWeakDivergenceFormSubharmonicOn a U u)
    {δ M : ℝ} (hδ : 0 < δ) (hδM : δ ≤ M) (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x ∧ u x ≤ M)
    {p : ℝ} (hp : 1 < p)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ U) :
    ∫ x in U, vecNormSq (η x • ((p / 2 * u x ^ (p / 2 - 1)) • u.grad x) +
        u x ^ (p / 2) • classicalGradient η x) ≤
      (2 * Λ * p ^ 2 / (p - 1) ^ 2 + 2) *
        ∫ x in U, u x ^ p * vecNormSq (classicalGradient η x) := by
  set v := rpowOfBounds hU u hδ hδM hu (p - 1)
  set w := rpowOfBounds hU u hδ hδM hu (p / 2)
  have hpos : ∀ᵐ x ∂volumeOn U, 0 < u x := hu.mono fun x hx => lt_of_lt_of_le hδ hx.1
  have hv0 : ∀ᵐ x ∂volumeOn U, 0 ≤ v x := hpos.mono fun x hx =>
    Real.rpow_nonneg hx.le _
  obtain ⟨-, -, hle⟩ := subharmonic_chainTest hU ha hEll hsub v
    (fun t => (p - 1) * t ^ (p - 1 - 1)) (fun _ => rfl) hv0 hη hηc hηU
  set ξ : Vec d → Vec d := fun x => (p / 2 * u x ^ (p / 2 - 1)) • u.grad x with hξdef
  set ω : Vec d → ℝ := fun x => u x ^ (p / 2) with hωdef
  have hξ : MemVectorL2On U ξ := w.gradMemL2
  have hω : MemL2On U ω := w.memL2
  have hωη : MemVectorL2On U (fun x => ω x • classicalGradient η x) := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using
      hω.fun_mul (memLpOn_top_classicalGradient hη hηc i)
  have hp0 : p ≠ 0 := by linarith
  have hmain : ∫ x in U, η x ^ 2 * (fun t => (p - 1) * t ^ (p - 1 - 1)) (u x) *
      vecDot (u.grad x) (matVecMul (a x) (u.grad x)) =
      (4 * (p - 1) / p ^ 2) * ∫ x in U, η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (hpos.mono fun x hx => ?_)
    simp only [hξdef, matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
    have hexp : u x ^ (p - 1 - 1) = u x ^ (p / 2 - 1) * u x ^ (p / 2 - 1) := by
      rw [rpow_add_self hx]
      congr 1
      ring
    rw [hexp]
    field_simp
    ring
  have hcross : ∫ x in U, 2 * η x * v x *
      vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x) =
      (4 / p) * ∫ x in U, η x * ω x *
        vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (hpos.mono fun x hx => ?_)
    simp only [hξdef, hωdef, matVecMul_smul, vecDot_smul_left]
    change 2 * η x * u x ^ (p - 1) * _ = _
    have hexp : u x ^ (p - 1) = u x ^ (p / 2) * u x ^ (p / 2 - 1) := by
      rw [← Real.rpow_add hx]
      congr 1
      ring
    rw [hexp]
    field_simp
    ring
  rw [hmain, hcross] at hle
  have hc₁ : 0 < 4 * (p - 1) / p ^ 2 := by
    have : 0 < p - 1 := by linarith
    positivity
  have hE := absorb_energy hU.measurableSet ha hEll hξ hη hηc hωη hc₁ hle
  have hratio : (4 / p) ^ 2 * Λ / (4 * (p - 1) / p ^ 2) ^ 2 = Λ * p ^ 2 / (p - 1) ^ 2 := by
    have : p - 1 ≠ 0 := by linarith
    field_simp
  rw [hratio] at hE
  have hRHS : ∫ x in U, ω x ^ 2 * vecNormSq (classicalGradient η x) =
      ∫ x in U, u x ^ p * vecNormSq (classicalGradient η x) := by
    refine integral_congr_ae (hpos.mono fun x hx => ?_)
    change (u x ^ (p / 2)) ^ 2 * _ = u x ^ p * _
    rw [pow_two, rpow_add_self hx, add_halves]
  rw [hRHS] at hE
  calc _ ≤ (2 * (Λ * p ^ 2 / (p - 1) ^ 2) + 2) *
        ∫ x in U, u x ^ p * vecNormSq (classicalGradient η x) := hE
    _ = _ := by ring

/-- **Moser energy estimate for supersolutions** (manuscript (4.70)). -/
theorem superharmonic_rpow_energy (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u)
    {δ : ℝ} (hδ : 0 < δ) (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x)
    {p : ℝ} (hp : -1 < p) (hp0 : p ≠ 0)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ U) :
    ∫ x in U, vecNormSq (η x • ((-p / 2 * u x ^ (-p / 2 - 1)) • u.grad x) +
        u x ^ (-p / 2) • classicalGradient η x) ≤
      (2 * Λ * p ^ 2 / (1 + p) ^ 2 + 2) *
        ∫ x in U, u x ^ (-p) * vecNormSq (classicalGradient η x) := by
  set v := rpowOfLowerBound hU u hδ hu (-(1 + p)) (by linarith)
  set w := rpowOfLowerBound hU u hδ hu (-p / 2) (by linarith)
  have hpos : ∀ᵐ x ∂volumeOn U, 0 < u x := hu.mono fun x hx => lt_of_lt_of_le hδ hx
  have hv0 : ∀ᵐ x ∂volumeOn U, 0 ≤ v x := hpos.mono fun x hx =>
    Real.rpow_nonneg hx.le _
  obtain ⟨-, -, hle⟩ := superharmonic_chainTest hU ha hEll hsuper v
    (fun t => -(1 + p) * t ^ (-(1 + p) - 1)) (fun _ => rfl) hv0 hη hηc hηU
  set ξ : Vec d → Vec d := fun x => (-p / 2 * u x ^ (-p / 2 - 1)) • u.grad x with hξdef
  set ω : Vec d → ℝ := fun x => u x ^ (-p / 2) with hωdef
  have hξ : MemVectorL2On U ξ := w.gradMemL2
  have hω : MemL2On U ω := w.memL2
  have hωη : MemVectorL2On U (fun x => ω x • classicalGradient η x) := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using
      hω.fun_mul (memLpOn_top_classicalGradient hη hηc i)
  have hmain : ∫ x in U, η x ^ 2 * (fun t => -(1 + p) * t ^ (-(1 + p) - 1)) (u x) *
      vecDot (u.grad x) (matVecMul (a x) (u.grad x)) =
      -((4 * (1 + p) / p ^ 2) *
        ∫ x in U, η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) := by
    rw [← integral_const_mul, ← integral_neg]
    refine integral_congr_ae (hpos.mono fun x hx => ?_)
    simp only [hξdef, matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
    have hexp : u x ^ (-(1 + p) - 1) = u x ^ (-p / 2 - 1) * u x ^ (-p / 2 - 1) := by
      rw [rpow_add_self hx]
      congr 1
      ring
    rw [hexp]
    field_simp
    ring
  have hcross : ∫ x in U, 2 * η x * v x *
      vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x) =
      -((4 / p) * ∫ x in U, η x * ω x *
        vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x)) := by
    rw [← integral_const_mul, ← integral_neg]
    refine integral_congr_ae (hpos.mono fun x hx => ?_)
    simp only [hξdef, hωdef, matVecMul_smul, vecDot_smul_left]
    change 2 * η x * u x ^ (-(1 + p)) * _ = _
    have hexp : u x ^ (-(1 + p)) = u x ^ (-p / 2) * u x ^ (-p / 2 - 1) := by
      rw [← Real.rpow_add hx]
      congr 1
      ring
    rw [hexp]
    field_simp
    ring
  rw [hmain, hcross] at hle
  have htest : (4 * (1 + p) / p ^ 2) *
      (∫ x in U, η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) +
      (4 / p) * (∫ x in U, η x * ω x *
        vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x)) ≤ 0 := by
    linarith
  have hc₁ : 0 < 4 * (1 + p) / p ^ 2 := by
    have : 0 < 1 + p := by linarith
    have : 0 < p ^ 2 := by positivity
    positivity
  have hE := absorb_energy hU.measurableSet ha hEll hξ hη hηc hωη hc₁ htest
  have hratio : (4 / p) ^ 2 * Λ / (4 * (1 + p) / p ^ 2) ^ 2 =
      Λ * p ^ 2 / (1 + p) ^ 2 := by
    have : 1 + p ≠ 0 := by linarith
    field_simp
  rw [hratio] at hE
  have hRHS : ∫ x in U, ω x ^ 2 * vecNormSq (classicalGradient η x) =
      ∫ x in U, u x ^ (-p) * vecNormSq (classicalGradient η x) := by
    refine integral_congr_ae (hpos.mono fun x hx => ?_)
    change (u x ^ (-p / 2)) ^ 2 * _ = u x ^ (-p) * _
    rw [pow_two, rpow_add_self hx]
    congr 2
    ring
  rw [hRHS] at hE
  calc _ ≤ (2 * (Λ * p ^ 2 / (1 + p) ^ 2) + 2) *
        ∫ x in U, u x ^ (-p) * vecNormSq (classicalGradient η x) := hE
    _ = _ := by ring

end DGNM

end PDE
