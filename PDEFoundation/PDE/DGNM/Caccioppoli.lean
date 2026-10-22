module

public import PDEFoundation.PDE.DGNM.ProductTest
public import PDEFoundation.Sobolev.H1.Truncation

/-!
# Caccioppoli inequalities for the subsolution predicate

For `u` subharmonic (smooth-test predicate, a.e.-measurable coefficients,
`IsEllipticMatrix 1 Λ` on `U`), a level `k`, and a globally smooth cutoff `η`
compactly supported in `U`, with `w = (u - k)₊` and `∇w = 1_{u > k} ∇u`:

* `caccioppoli_positivePart` (manuscript Lemma 4.1):
  `∫ η² ∇w · a ∇w ≤ 4Λ ∫ w² |∇η|²`;
* `caccioppoli_energy_positivePart` (manuscript (4.37)):
  `∫ |∇(η w)|² ≤ (8Λ + 2) ∫ w² |∇η|²`, where `∇(η w) = η ∇w + w ∇η`;
* `caccioppoli_energy_positivePart_ten`: the same with `10 Λ`;
* `caccioppoli_energy_positivePart_cutoff`: the same for a
  `QuantitativeSmoothCutoff inner outer K`, bounded by `10 Λ K² ∫_outer w²`.

All `|·|` are Euclidean (`vecNormSq`). The cutoff class is: globally smooth,
compact support, `tsupport η ⊆ U` (no sign or size condition is needed).
-/

@[expose] public section

namespace PDE

namespace DGNM

open MeasureTheory

variable {d : ℕ} {U : Set (Vec d)} {Λ : ℝ} {a : CoeffField d}

/-- Pointwise Young bound for the Caccioppoli cross term, with the
energy-adapted flux bound `|Aξ|² ≤ Λ ξ·Aξ`. -/
theorem abs_two_mul_mul_vecDot_le_caccioppoli {η w : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix 1 Λ A) (ξ ζ : Vec d) :
    |2 * η * w * vecDot (matVecMul A ξ) ζ| ≤
      (η ^ 2 * vecDot ξ (matVecMul A ξ)) / 2 +
        2 * Λ * w ^ 2 * vecNormSq ζ := by
  have hflux := vecNormSq_matVecMul_le_mul_vecDot_of_isEllipticMatrix hA ξ
  have hdotSq := sq_vecDot_le_vecNormSq_mul_vecNormSq (matVecMul A ξ) ζ
  have hE : 0 ≤ vecDot ξ (matVecMul A ξ) := vecDot_matVecMul_self_nonneg hA ξ
  have hΛ : 0 ≤ Λ := hA.Lam_pos.le
  have hfac : 0 ≤ 4 * η ^ 2 * w ^ 2 := by positivity
  have hsq :
      (2 * η * w * vecDot (matVecMul A ξ) ζ) ^ 2 ≤
        (η ^ 2 * vecDot ξ (matVecMul A ξ)) * (4 * Λ * w ^ 2 * vecNormSq ζ) := by
    calc
      (2 * η * w * vecDot (matVecMul A ξ) ζ) ^ 2 =
          (4 * η ^ 2 * w ^ 2) * vecDot (matVecMul A ξ) ζ ^ 2 := by ring
      _ ≤ (4 * η ^ 2 * w ^ 2) *
          (vecNormSq (matVecMul A ξ) * vecNormSq ζ) :=
        mul_le_mul_of_nonneg_left hdotSq hfac
      _ ≤ (4 * η ^ 2 * w ^ 2) *
          ((Λ * vecDot ξ (matVecMul A ξ)) * vecNormSq ζ) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hflux (vecNormSq_nonneg ζ)) hfac
      _ = (η ^ 2 * vecDot ξ (matVecMul A ξ)) *
          (4 * Λ * w ^ 2 * vecNormSq ζ) := by ring
  have hyoung := abs_le_add_halves_of_sq_le_mul
    (A := η ^ 2 * vecDot ξ (matVecMul A ξ))
    (B := 4 * Λ * w ^ 2 * vecNormSq ζ) hsq
    (mul_nonneg (sq_nonneg η) hE)
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hΛ) (sq_nonneg w))
      (vecNormSq_nonneg ζ))
  linarith

/-- The positive-part gradient `1_{u>k} ∇u`. -/
private theorem positivePart_flux_eq (u : H1Function U) (k : ℝ) (A : Mat d)
    (x : Vec d) :
    vecDot (matVecMul A (u.grad x)) ({y | k < u y}.indicator u.grad x) =
      vecDot ({y | k < u y}.indicator u.grad x)
        (matVecMul A ({y | k < u y}.indicator u.grad x)) := by
  by_cases hx : k < u x
  · have hmem : x ∈ {y | k < u y} := hx
    rw [Set.indicator_of_mem hmem, vecDot_comm]
  · have hmem : x ∉ {y | k < u y} := hx
    rw [Set.indicator_of_notMem hmem, vecDot_zero_right, vecDot_zero_left]

private theorem positivePart_cross_eq (u : H1Function U) (k η : ℝ) (A : Mat d)
    (ζ : Vec d) (x : Vec d) :
    2 * η * max (u x - k) 0 * vecDot (matVecMul A (u.grad x)) ζ =
      2 * η * max (u x - k) 0 *
        vecDot (matVecMul A ({y | k < u y}.indicator u.grad x)) ζ := by
  by_cases hx : k < u x
  · have hmem : x ∈ {y | k < u y} := hx
    rw [Set.indicator_of_mem hmem]
  · have hw : max (u x - k) 0 = 0 := max_eq_right (by linarith [not_lt.mp hx])
    rw [hw]
    ring

/-- **The `η² (u-k)₊` test, expanded.** For `u` subharmonic, with
`w = (u-k)₊` and `∇w = 1_{u>k} ∇u`:
`∫ η² ∇w·a∇w + ∫ 2ηw (a∇w·∇η) ≤ 0`, both pieces integrable. -/
theorem subharmonic_positivePart_sqTest (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsub : IsWeakDivergenceFormSubharmonicOn a U u)
    (k : ℝ) {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    IntegrableOn (fun x => η x ^ 2 * vecDot ({y | k < u y}.indicator u.grad x)
        (matVecMul (a x) ({y | k < u y}.indicator u.grad x))) U ∧
      IntegrableOn (fun x => 2 * η x * max (u x - k) 0 *
        vecDot (matVecMul (a x) ({y | k < u y}.indicator u.grad x))
          (classicalGradient η x)) U ∧
      (∫ x in U, η x ^ 2 * vecDot ({y | k < u y}.indicator u.grad x)
          (matVecMul (a x) ({y | k < u y}.indicator u.grad x))) +
        ∫ x in U, 2 * η x * max (u x - k) 0 *
          vecDot (matVecMul (a x) ({y | k < u y}.indicator u.grad x))
            (classicalGradient η x) ≤ 0 := by
  let v := u.positivePartSubConst hU k
  have hv0 : ∀ᵐ x ∂volumeOn U, 0 ≤ v x :=
    Filter.Eventually.of_forall fun x => by
      change 0 ≤ (u.positivePartSubConst hU k).toFun x
      rw [H1Function.positivePartSubConst_toFun]
      exact le_max_right _ _
  obtain ⟨h1, h2, hle⟩ := subharmonic_sqTest hU ha hEll hsub v hv0 hη hηc hηU
  have hmain_eq :
      (fun x => η x ^ 2 * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) =
        fun x => η x ^ 2 * vecDot ({y | k < u y}.indicator u.grad x)
          (matVecMul (a x) ({y | k < u y}.indicator u.grad x)) := by
    funext x
    change η x ^ 2 * vecDot (matVecMul (a x) (u.grad x))
      ((u.positivePartSubConst hU k).grad x) = _
    rw [H1Function.positivePartSubConst_grad, positivePart_flux_eq]
  have hcross_eq :
      (fun x => 2 * η x * v x *
        vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x)) =
        fun x => 2 * η x * max (u x - k) 0 *
          vecDot (matVecMul (a x) ({y | k < u y}.indicator u.grad x))
            (classicalGradient η x) := by
    funext x
    change 2 * η x * (u.positivePartSubConst hU k).toFun x *
      vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x) = _
    rw [H1Function.positivePartSubConst_toFun]
    exact positivePart_cross_eq u k (η x) (a x) _ x
  rw [hmain_eq] at h1 hle
  rw [hcross_eq] at h2 hle
  exact ⟨h1, h2, hle⟩

/-- **Caccioppoli inequality** (manuscript Lemma 4.1) for the
subharmonic predicate, at an arbitrary level `k`:
`∫ η² ∇(u-k)₊ · a ∇(u-k)₊ ≤ 4Λ ∫ (u-k)₊² |∇η|²`. -/
theorem caccioppoli_positivePart (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsub : IsWeakDivergenceFormSubharmonicOn a U u)
    (k : ℝ) {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    ∫ x in U, η x ^ 2 * vecDot ({y | k < u y}.indicator u.grad x)
        (matVecMul (a x) ({y | k < u y}.indicator u.grad x)) ≤
      4 * Λ * ∫ x in U, max (u x - k) 0 ^ 2 * vecNormSq (classicalGradient η x) := by
  set ξ : Vec d → Vec d := fun x => {y | k < u y}.indicator u.grad x with hξ
  set w : Vec d → ℝ := fun x => max (u x - k) 0 with hw
  obtain ⟨h1, h2, hle⟩ := subharmonic_positivePart_sqTest hU ha hEll hsub k hη hηc hηU
  -- the quadratic error term
  have hDηTop (i : Fin d) : MemLpOn U ⊤ (fun x => classicalGradient η x i) :=
    memLpOn_top_classicalGradient hη hηc i
  have hwL2 : MemL2On U w := by
    simpa only [w, H1Function.positivePartSubConst_toFun] using
      (u.positivePartSubConst hU k).memL2
  have hG : MemVectorL2On U (fun x => w x • classicalGradient η x) := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using hwL2.fun_mul (hDηTop i)
  have hGsq : IntegrableOn
      (fun x => w x ^ 2 * vecNormSq (classicalGradient η x)) U := by
    simpa only [vecNormSq_smul] using integrableOn_vecNormSq_of_memVectorL2On hG
  have hmem : ∀ᵐ x ∂volumeOn U, x ∈ U :=
    (ae_restrict_iff' hU.measurableSet).2 (Filter.Eventually.of_forall fun _ hx => hx)
  have hpointwise : ∀ᵐ x ∂volumeOn U,
      |2 * η x * w x * vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x)| ≤
        (η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) / 2 +
          2 * Λ * (w x ^ 2 * vecNormSq (classicalGradient η x)) := by
    filter_upwards [hmem] with x hx
    have := abs_two_mul_mul_vecDot_le_caccioppoli (η := η x) (w := w x)
      (hEll x hx) (ξ x) (classicalGradient η x)
    linarith
  have hboundInt : IntegrableOn (fun x =>
      (η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) / 2 +
        2 * Λ * (w x ^ 2 * vecNormSq (classicalGradient η x))) U :=
    (h1.div_const 2).add (hGsq.const_mul (2 * Λ))
  have hbound := integral_mono_ae h2.abs hboundInt hpointwise
  have habs := abs_integral_le_integral_abs (μ := volumeOn U)
    (f := fun x => 2 * η x * w x *
      vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x))
  rw [integral_add (h1.div_const 2) (hGsq.const_mul (2 * Λ)), integral_div,
    integral_const_mul] at hbound
  have hneg := neg_abs_le (∫ x in U, 2 * η x * w x *
      vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x))
  linarith

/-- The gradient of `η (u-k)₊` as an `H¹` product. -/
theorem positivePart_mulCutoff_grad (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (k : ℝ) {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) :
    ((u.positivePartSubConst hU k).mulContDiffHasCompactSupport hη hηc).grad =
      fun x => η x • {y | k < u y}.indicator u.grad x +
        max (u x - k) 0 • classicalGradient η x := by
  rw [H1Function.mulContDiffHasCompactSupport_grad,
    H1Function.positivePartSubConst_grad]
  rfl

/-- **Caccioppoli energy inequality** (manuscript (4.37)):
`∫ |∇(η (u-k)₊)|² ≤ (8Λ + 2) ∫ (u-k)₊² |∇η|²`, with
`∇(η w) = η ∇w + w ∇η` written out explicitly. -/
theorem caccioppoli_energy_positivePart (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsub : IsWeakDivergenceFormSubharmonicOn a U u)
    (k : ℝ) {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    ∫ x in U, vecNormSq (η x • {y | k < u y}.indicator u.grad x +
        max (u x - k) 0 • classicalGradient η x) ≤
      (8 * Λ + 2) * ∫ x in U, max (u x - k) 0 ^ 2 *
        vecNormSq (classicalGradient η x) := by
  set ξ : Vec d → Vec d := fun x => {y | k < u y}.indicator u.grad x with hξ
  set w : Vec d → ℝ := fun x => max (u x - k) 0 with hw
  have hcacc := caccioppoli_positivePart hU ha hEll hsub k hη hηc hηU
  have hηTop : MemLpOn U ⊤ η := memLpOn_top_of_contDiff hη hηc
  have hDηTop (i : Fin d) : MemLpOn U ⊤ (fun x => classicalGradient η x i) :=
    memLpOn_top_classicalGradient hη hηc i
  have hwL2 : MemL2On U w := by
    simpa only [w, H1Function.positivePartSubConst_toFun] using
      (u.positivePartSubConst hU k).memL2
  have hξL2 : MemVectorL2On U ξ := by
    simpa only [ξ, H1Function.positivePartSubConst_grad] using
      (u.positivePartSubConst hU k).gradMemL2
  have hA : MemVectorL2On U (fun x => η x • ξ x) := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using (hξL2 i).fun_mul hηTop
  have hB : MemVectorL2On U (fun x => w x • classicalGradient η x) := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using hwL2.fun_mul (hDηTop i)
  have hAB : MemVectorL2On U (fun x => η x • ξ x + w x • classicalGradient η x) := by
    intro i
    exact (hA i).add (hB i)
  have hAsq : IntegrableOn (fun x => η x ^ 2 * vecNormSq (ξ x)) U := by
    simpa only [vecNormSq_smul] using integrableOn_vecNormSq_of_memVectorL2On hA
  have hBsq : IntegrableOn
      (fun x => w x ^ 2 * vecNormSq (classicalGradient η x)) U := by
    simpa only [vecNormSq_smul] using integrableOn_vecNormSq_of_memVectorL2On hB
  have hABsq := integrableOn_vecNormSq_of_memVectorL2On hAB
  -- the weighted energy is integrable (from the Caccioppoli test)
  have hE : IntegrableOn
      (fun x => η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) U := by
    have hF := memVectorL2On_matVecMul_of_aemeasurable hU.measurableSet ha hEll hξL2
    have hC : MemVectorL2On U (fun x => η x ^ 2 • ξ x) := by
      intro i
      have hη2 : MemLpOn U ⊤ (fun x => η x ^ 2) := by
        have hsq : (fun x => η x ^ 2) = η * η := by
          funext x
          simp only [Pi.mul_apply, pow_two]
        rw [hsq]
        exact hηTop.mul hηTop
      simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using (hξL2 i).fun_mul hη2
    have := integrableOn_vecDot_of_memVectorL2On hC hF
    simpa only [vecDot_smul_left] using this
  have hmem : ∀ᵐ x ∂volumeOn U, x ∈ U :=
    (ae_restrict_iff' hU.measurableSet).2 (Filter.Eventually.of_forall fun _ hx => hx)
  have hpointwise : ∀ᵐ x ∂volumeOn U,
      vecNormSq (η x • ξ x + w x • classicalGradient η x) ≤
        2 * (η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) +
          2 * (w x ^ 2 * vecNormSq (classicalGradient η x)) := by
    filter_upwards [hmem] with x hx
    have h1 := vecNormSq_add_le (η x • ξ x) (w x • classicalGradient η x)
    have h2 := vecNormSq_le_vecDot_matVecMul (hEll x hx) (ξ x)
    rw [vecNormSq_smul, vecNormSq_smul] at h1
    have h3 : η x ^ 2 * vecNormSq (ξ x) ≤
        η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x)) :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    linarith
  have hmono : ∫ x in U, vecNormSq (η x • ξ x + w x • classicalGradient η x) ≤
      ∫ x in U, (2 * (η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) +
          2 * (w x ^ 2 * vecNormSq (classicalGradient η x))) :=
    integral_mono_ae hABsq ((hE.const_mul 2).add (hBsq.const_mul 2)) hpointwise
  rw [integral_add (hE.const_mul 2) (hBsq.const_mul 2), integral_const_mul,
    integral_const_mul] at hmono
  linarith

/-- The Caccioppoli energy inequality with the rounded constant `10 Λ`
(`8Λ + 2 ≤ 10Λ` because `Λ ≥ 1`). -/
theorem caccioppoli_energy_positivePart_ten (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsub : IsWeakDivergenceFormSubharmonicOn a U u)
    (k : ℝ) {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    ∫ x in U, vecNormSq (η x • {y | k < u y}.indicator u.grad x +
        max (u x - k) 0 • classicalGradient η x) ≤
      10 * Λ * ∫ x in U, max (u x - k) 0 ^ 2 *
        vecNormSq (classicalGradient η x) := by
  have hbase := caccioppoli_energy_positivePart hU ha hEll hsub k hη hηc hηU
  rcases U.eq_empty_or_nonempty with hUe | ⟨x₀, hx₀⟩
  · subst hUe
    simp only [Measure.restrict_empty, integral_zero_measure, mul_zero, le_refl]
  · have hΛ : 1 ≤ Λ := (hEll x₀ hx₀).lam_le_Lam
    have hI : 0 ≤ ∫ x in U, max (u x - k) 0 ^ 2 * vecNormSq (classicalGradient η x) :=
      setIntegral_nonneg hU.measurableSet fun x _ =>
        mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _)
    nlinarith

/-- The Caccioppoli energy inequality for a quantitative cutoff
`η : QuantitativeSmoothCutoff inner outer K` with `outer ⊆ U` measurable:
`∫_U |∇(η (u-k)₊)|² ≤ 10 Λ K² ∫_outer (u-k)₊²`. -/
theorem caccioppoli_energy_positivePart_cutoff (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsub : IsWeakDivergenceFormSubharmonicOn a U u)
    (k : ℝ) {inner outer : Set (Vec d)} {K : ℝ}
    (η : QuantitativeSmoothCutoff inner outer K) (houter : outer ⊆ U)
    (houterMeas : MeasurableSet outer) :
    ∫ x in U, vecNormSq (η x • {y | k < u y}.indicator u.grad x +
        max (u x - k) 0 • classicalGradient η.toFun x) ≤
      10 * Λ * K ^ 2 * ∫ x in outer, max (u x - k) 0 ^ 2 := by
  rcases U.eq_empty_or_nonempty with hUe | ⟨x₀, hx₀⟩
  · subst hUe
    have houterE : outer = ∅ := Set.subset_empty_iff.mp houter
    subst houterE
    simp only [Measure.restrict_empty, integral_zero_measure, mul_zero, le_refl]
  have hΛ : 0 ≤ Λ := (hEll x₀ hx₀).Lam_pos.le
  have hbase := caccioppoli_energy_positivePart_ten hU ha hEll hsub k η.smooth
    η.hasCompactSupport (η.tsupport_subset.trans houter)
  have hwL2 : MemL2On U (fun x => max (u x - k) 0) := by
    simpa only [H1Function.positivePartSubConst_toFun] using
      (u.positivePartSubConst hU k).memL2
  have hDηTop (i : Fin d) : MemLpOn U ⊤ (fun x => classicalGradient η.toFun x i) :=
    memLpOn_top_classicalGradient η.smooth η.hasCompactSupport i
  have hB : MemVectorL2On U
      (fun x => max (u x - k) 0 • classicalGradient η.toFun x) := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using hwL2.fun_mul (hDηTop i)
  have hBsq : IntegrableOn
      (fun x => max (u x - k) 0 ^ 2 * vecNormSq (classicalGradient η.toFun x)) U := by
    simpa only [vecNormSq_smul] using integrableOn_vecNormSq_of_memVectorL2On hB
  have hwsq : IntegrableOn (fun x => max (u x - k) 0 ^ 2) U := by
    simpa only [pow_two] using integrableOn_mul_of_memL2On hwL2 hwL2
  have hrestrict :
      ∫ x in U, max (u x - k) 0 ^ 2 * vecNormSq (classicalGradient η.toFun x) =
        ∫ x in outer, max (u x - k) 0 ^ 2 *
          vecNormSq (classicalGradient η.toFun x) :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet houter
      fun x hx => by
        rw [η.classicalGradient_eq_zero_of_not_mem_outer hx.2]
        simp [vecNormSq, vecDot]
  have hle : ∫ x in outer, max (u x - k) 0 ^ 2 *
        vecNormSq (classicalGradient η.toFun x) ≤
      ∫ x in outer, K ^ 2 * max (u x - k) 0 ^ 2 :=
    setIntegral_mono_on (hBsq.mono_set houter) ((hwsq.mono_set houter).const_mul _)
      houterMeas fun x _ => by
        have hg : vecNormSq (classicalGradient η.toFun x) ≤ K ^ 2 := by
          rw [← vecEuclideanNorm_sq]
          exact pow_le_pow_left₀ (vecEuclideanNorm_nonneg _) (η.gradient_bound x) 2
        nlinarith [sq_nonneg (max (u x - k) 0)]
  rw [integral_const_mul] at hle
  calc _ ≤ 10 * Λ * ∫ x in U, max (u x - k) 0 ^ 2 *
          vecNormSq (classicalGradient η.toFun x) := hbase
    _ ≤ 10 * Λ * (K ^ 2 * ∫ x in outer, max (u x - k) 0 ^ 2) := by
      rw [hrestrict]
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 10 * Λ * K ^ 2 * ∫ x in outer, max (u x - k) 0 ^ 2 := by ring

end DGNM

end PDE
