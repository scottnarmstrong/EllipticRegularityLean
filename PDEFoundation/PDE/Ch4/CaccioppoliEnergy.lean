module

public import PDEFoundation.PDE.Ch4.Caccioppoli

/-!
# Caccioppoli energy inequality on bounded open sets (Lipschitz cutoffs)

`∫ |∇(η (u-k)₊)|² ≤ (8Λ + 2) ∫ (u-k)₊² |∇η|²`, with `∇(η w) = η ∇w + w ∇η` written out, and the
variants with constant `10 Λ` and with the cutoff class "Lipschitz constant `K`, `0 ≤ η ≤ 1`,
support in `outer ⊆ U`".
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory

namespace PDE.Ch4Infra

variable {d : ℕ} {U : Set (Vec d)} {Λ : ℝ} {a : CoeffField d}

/-- **Caccioppoli energy inequality** (manuscript (4.37)) on a bounded open set. -/
theorem caccioppoli_energy_positivePart_open (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsub : IsWeakDivergenceFormSubharmonicOn a U u)
    (k : ℝ) {L M : ℝ} {η : Vec d → ℝ} (hη : EucLip L η) (hL : 0 ≤ L) (hM : ∀ x, |η x| ≤ M)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    ∫ x in U, vecNormSq (η x • {y | k < u y}.indicator u.grad x +
        max (u x - k) 0 • classicalGradient η x) ≤
      (8 * Λ + 2) * ∫ x in U, max (u x - k) 0 ^ 2 *
        vecNormSq (classicalGradient η x) := by
  set ξ : Vec d → Vec d := fun x => {y | k < u y}.indicator u.grad x with hξ
  set w : Vec d → ℝ := fun x => max (u x - k) 0 with hw
  have hcacc := caccioppoli_positivePart_open hU hfin ha hEll hsub k hη hL hM hηc hηU
  have hηcont : Continuous η := hη.continuous hL
  have hwL2 : MemL2On U w := memL2On_positivePart_of_finite u hfin k
  have hξL2 : MemVectorL2On U ξ := posPartGrad_gradMemL2 u k
  have hA : MemVectorL2On U (fun x => η x • ξ x) := fun i => by
    simpa only [Pi.smul_apply, smul_eq_mul] using memL2On_mul_bounded (hξL2 i) hηcont hM
  have hB : MemVectorL2On U (fun x => w x • classicalGradient η x) := fun i => by
    simpa only [Pi.smul_apply, smul_eq_mul, classicalGradient] using
      memL2On_mul_partialDeriv hη hL hwL2 i
  have hAB : MemVectorL2On U (fun x => η x • ξ x + w x • classicalGradient η x) := fun i =>
    (hA i).add (hB i)
  have hBsq : IntegrableOn
      (fun x => w x ^ 2 * vecNormSq (classicalGradient η x)) U := by
    simpa only [vecNormSq_smul] using integrableOn_vecNormSq_of_memVectorL2On hB
  have hABsq := integrableOn_vecNormSq_of_memVectorL2On hAB
  -- the weighted energy is integrable
  have hE : IntegrableOn
      (fun x => η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) U := by
    have hF := DGNM.memVectorL2On_matVecMul_of_aemeasurable hU.measurableSet ha hEll hξL2
    have hC : MemVectorL2On U (fun x => η x ^ 2 • ξ x) := fun i => by
      simpa only [Pi.smul_apply, smul_eq_mul] using
        memL2On_mul_bounded (hξL2 i) (by fun_prop : Continuous fun x => η x ^ 2) (abs_sq_le hM)
    have := integrableOn_vecDot_of_memVectorL2On hC hF
    simpa only [DGNM.vecDot_smul_left] using this
  have hmem : ∀ᵐ x ∂volumeOn U, x ∈ U :=
    (ae_restrict_iff' hU.measurableSet).2 (Filter.Eventually.of_forall fun _ hx => hx)
  have hpointwise : ∀ᵐ x ∂volumeOn U,
      vecNormSq (η x • ξ x + w x • classicalGradient η x) ≤
        2 * (η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) +
          2 * (w x ^ 2 * vecNormSq (classicalGradient η x)) := by
    filter_upwards [hmem] with x hx
    have h1 := vecNormSq_add_le (η x • ξ x) (w x • classicalGradient η x)
    have h2 := DGNM.vecNormSq_le_vecDot_matVecMul (hEll x hx) (ξ x)
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

/-- The energy inequality with the rounded constant `10 Λ`. -/
theorem caccioppoli_energy_positivePart_ten_open (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsub : IsWeakDivergenceFormSubharmonicOn a U u)
    (k : ℝ) {L M : ℝ} {η : Vec d → ℝ} (hη : EucLip L η) (hL : 0 ≤ L) (hM : ∀ x, |η x| ≤ M)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    ∫ x in U, vecNormSq (η x • {y | k < u y}.indicator u.grad x +
        max (u x - k) 0 • classicalGradient η x) ≤
      10 * Λ * ∫ x in U, max (u x - k) 0 ^ 2 * vecNormSq (classicalGradient η x) := by
  have hbase := caccioppoli_energy_positivePart_open hU hfin ha hEll hsub k hη hL hM hηc hηU
  rcases U.eq_empty_or_nonempty with hUe | ⟨x₀, hx₀⟩
  · subst hUe
    simp only [Measure.restrict_empty, integral_zero_measure, mul_zero, le_refl]
  · have hΛ : 1 ≤ Λ := (hEll x₀ hx₀).lam_le_Lam
    have hI : 0 ≤ ∫ x in U, max (u x - k) 0 ^ 2 * vecNormSq (classicalGradient η x) :=
      setIntegral_nonneg hU.measurableSet fun x _ =>
        mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _)
    nlinarith

/-- Every value of `classicalGradient η` of an `L`-Lipschitz `η` has Euclidean length `≤ L`
(at nondifferentiable points `fderiv` is `0`). -/
theorem EucLip.vecEuclideanNorm_classicalGradient_le' {L : ℝ} {η : Vec d → ℝ} (hη : EucLip L η)
    (hL : 0 ≤ L) (x : Vec d) : vecEuclideanNorm (classicalGradient η x) ≤ L := by
  by_cases hx : DifferentiableAt ℝ η x
  · exact hη.vecEuclideanNorm_classicalGradient_le hL hx
  · have : classicalGradient η x = 0 := by
      funext i
      simp [classicalGradient, fderiv_zero_of_not_differentiableAt hx]
    rw [this]
    have : vecEuclideanNorm (0 : Vec d) = 0 := by
      simp [vecEuclideanNorm, vecNormSq, vecDot]
    rw [this]; exact hL

/-- **Caccioppoli energy inequality with a cutoff between `inner` and `outer`**: for a
`K`-Lipschitz `η` with `|η| ≤ 1` and `tsupport η ⊆ outer ⊆ U`,
`∫_U |∇(η (u-k)₊)|² ≤ 10 Λ K² ∫_outer (u-k)₊²`. -/
theorem caccioppoli_energy_positivePart_cutoff_open (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsub : IsWeakDivergenceFormSubharmonicOn a U u)
    (k : ℝ) {K : ℝ} {η : Vec d → ℝ} (hη : EucLip K η) (hK : 0 ≤ K) (hM : ∀ x, |η x| ≤ 1)
    {outer : Set (Vec d)} (hηc : HasCompactSupport η) (hηo : tsupport η ⊆ outer)
    (houter : outer ⊆ U) (houterMeas : MeasurableSet outer) :
    ∫ x in U, vecNormSq (η x • {y | k < u y}.indicator u.grad x +
        max (u x - k) 0 • classicalGradient η x) ≤
      10 * Λ * K ^ 2 * ∫ x in outer, max (u x - k) 0 ^ 2 := by
  rcases U.eq_empty_or_nonempty with hUe | ⟨x₀, hx₀⟩
  · subst hUe
    have houterE : outer = ∅ := Set.subset_empty_iff.mp houter
    subst houterE
    simp only [Measure.restrict_empty, integral_zero_measure, mul_zero, le_refl]
  have hΛ : 0 ≤ Λ := (hEll x₀ hx₀).Lam_pos.le
  have hbase := caccioppoli_energy_positivePart_ten_open hU hfin ha hEll hsub k hη hK hM hηc
    (hηo.trans houter)
  have hwL2 : MemL2On U (fun x => max (u x - k) 0) := memL2On_positivePart_of_finite u hfin k
  have hB : MemVectorL2On U (fun x => max (u x - k) 0 • classicalGradient η x) := fun i => by
    simpa only [Pi.smul_apply, smul_eq_mul, classicalGradient] using
      memL2On_mul_partialDeriv hη hK hwL2 i
  have hBsq : IntegrableOn
      (fun x => max (u x - k) 0 ^ 2 * vecNormSq (classicalGradient η x)) U := by
    simpa only [vecNormSq_smul] using integrableOn_vecNormSq_of_memVectorL2On hB
  have hwsq : IntegrableOn (fun x => max (u x - k) 0 ^ 2) U := by
    simpa only [pow_two] using integrableOn_mul_of_memL2On hwL2 hwL2
  have hrestrict :
      ∫ x in U, max (u x - k) 0 ^ 2 * vecNormSq (classicalGradient η x) =
        ∫ x in outer, max (u x - k) 0 ^ 2 * vecNormSq (classicalGradient η x) :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet houter
      fun x hx => by
        have hxt : x ∉ tsupport η := fun h => hx.2 (hηo h)
        have : classicalGradient η x = 0 := by
          funext i; simp [classicalGradient, fderiv_of_notMem_tsupport ℝ hxt]
        rw [this]
        simp [vecNormSq, vecDot]
  have hle : ∫ x in outer, max (u x - k) 0 ^ 2 * vecNormSq (classicalGradient η x) ≤
      ∫ x in outer, K ^ 2 * max (u x - k) 0 ^ 2 :=
    setIntegral_mono_on (hBsq.mono_set houter) ((hwsq.mono_set houter).const_mul _)
      houterMeas fun x _ => by
        have hg : vecNormSq (classicalGradient η x) ≤ K ^ 2 := by
          rw [← vecEuclideanNorm_sq]
          exact pow_le_pow_left₀ (vecEuclideanNorm_nonneg _)
            (hη.vecEuclideanNorm_classicalGradient_le' hK x) 2
        nlinarith [sq_nonneg (max (u x - k) 0)]
  rw [integral_const_mul] at hle
  calc _ ≤ 10 * Λ * ∫ x in U, max (u x - k) 0 ^ 2 *
          vecNormSq (classicalGradient η x) := hbase
    _ ≤ 10 * Λ * (K ^ 2 * ∫ x in outer, max (u x - k) 0 ^ 2) := by
      rw [hrestrict]
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 10 * Λ * K ^ 2 * ∫ x in outer, max (u x - k) 0 ^ 2 := by ring

end PDE.Ch4Infra
