module

public import PDEFoundation.PDE.Ch4.SqTest
public import PDEFoundation.PDE.DGNM.Caccioppoli

/-!
# Caccioppoli inequalities for subsolutions on bounded open sets

Open-set versions of `PDE.DGNM.caccioppoli_positivePart` and
`PDE.DGNM.caccioppoli_energy_positivePart` (manuscript Lemma 4.1, (4.37)),
valid on an arbitrary bounded open set `U` (annuli, ...) and for Lipschitz cutoffs.

Hypotheses on the cutoff `η`: `EucLip L η`, `0 ≤ L`, `|η| ≤ M`, compact support with
`tsupport η ⊆ U`; `∇η` is `classicalGradient η` (a.e. gradient, Euclidean length `≤ L`).
`w = (u - k)₊` with `∇w = 1_{u>k} ∇u`; all `|·|` are Euclidean.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory

namespace PDE.Ch4Infra

variable {d : ℕ} {U : Set (Vec d)} {Λ : ℝ} {a : CoeffField d}

private theorem positivePart_flux_eq (u : H1Function U) (k : ℝ) (A : Mat d) (x : Vec d) :
    vecDot (matVecMul A (u.grad x)) ({y | k < u y}.indicator u.grad x) =
      vecDot ({y | k < u y}.indicator u.grad x)
        (matVecMul A ({y | k < u y}.indicator u.grad x)) := by
  by_cases hx : k < u x
  · have hmem : x ∈ {y | k < u y} := hx
    rw [Set.indicator_of_mem hmem, vecDot_comm]
  · have hmem : x ∉ {y | k < u y} := hx
    rw [Set.indicator_of_notMem hmem, DGNM.vecDot_zero_right, DGNM.vecDot_zero_left]

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

/-- **The `η² (u-k)₊` test, expanded.** -/
theorem subharmonic_positivePart_sqTest_open (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsub : IsWeakDivergenceFormSubharmonicOn a U u)
    (k : ℝ) {L M : ℝ} {η : Vec d → ℝ} (hη : EucLip L η) (hL : 0 ≤ L) (hM : ∀ x, |η x| ≤ M)
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
  let v := positivePartOpen hU u k (memL2On_positivePart_of_finite u hfin k)
  have hv0 : ∀ᵐ x ∂volumeOn U, 0 ≤ v.toFun x :=
    Filter.Eventually.of_forall fun x => le_max_right _ _
  obtain ⟨h1, h2, hle⟩ := subharmonic_sqTest_lip hU hfin ha hEll hsub v hv0 hη hL hM hηc hηU
  have hmain_eq :
      (fun x => η x ^ 2 * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) =
        fun x => η x ^ 2 * vecDot ({y | k < u y}.indicator u.grad x)
          (matVecMul (a x) ({y | k < u y}.indicator u.grad x)) := by
    funext x
    exact congrArg (fun t => η x ^ 2 * t) (positivePart_flux_eq u k (a x) x)
  have hcross_eq :
      (fun x => 2 * η x * v.toFun x *
        vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x)) =
        fun x => 2 * η x * max (u x - k) 0 *
          vecDot (matVecMul (a x) ({y | k < u y}.indicator u.grad x))
            (classicalGradient η x) := by
    funext x
    exact positivePart_cross_eq u k (η x) (a x) _ x
  rw [hmain_eq] at h1 hle
  rw [hcross_eq] at h2 hle
  exact ⟨h1, h2, hle⟩

/-- **Caccioppoli inequality** (manuscript Lemma 4.1) on a bounded open set, Lipschitz cutoff:
`∫ η² ∇(u-k)₊ · a ∇(u-k)₊ ≤ 4Λ ∫ (u-k)₊² |∇η|²`. -/
theorem caccioppoli_positivePart_open (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsub : IsWeakDivergenceFormSubharmonicOn a U u)
    (k : ℝ) {L M : ℝ} {η : Vec d → ℝ} (hη : EucLip L η) (hL : 0 ≤ L) (hM : ∀ x, |η x| ≤ M)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    ∫ x in U, η x ^ 2 * vecDot ({y | k < u y}.indicator u.grad x)
        (matVecMul (a x) ({y | k < u y}.indicator u.grad x)) ≤
      4 * Λ * ∫ x in U, max (u x - k) 0 ^ 2 * vecNormSq (classicalGradient η x) := by
  set ξ : Vec d → Vec d := fun x => {y | k < u y}.indicator u.grad x with hξ
  set w : Vec d → ℝ := fun x => max (u x - k) 0 with hw
  obtain ⟨h1, h2, hle⟩ :=
    subharmonic_positivePart_sqTest_open hU hfin ha hEll hsub k hη hL hM hηc hηU
  have hwL2 : MemL2On U w := memL2On_positivePart_of_finite u hfin k
  have hG : MemVectorL2On U (fun x => w x • classicalGradient η x) := fun i => by
    simpa only [Pi.smul_apply, smul_eq_mul, classicalGradient] using
      memL2On_mul_partialDeriv hη hL hwL2 i
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
    have := DGNM.abs_two_mul_mul_vecDot_le_caccioppoli (η := η x) (w := w x)
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

end PDE.Ch4Infra
