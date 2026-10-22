module

public import EllipticRegularity.Ch4.GreenDecay.Restrict
public import PDEFoundation.PDE.Ch4.CaccioppoliEnergy
public import PDEFoundation.Sobolev.Ch4.Cutoff
public import PDEFoundation.Sobolev.H1.Mean

/-!
# Caccioppoli inequality for solutions on bounded open sets

For a smooth-test solution `u` of `-div (b ∇u) = 0` in a bounded open set `U`, a Lipschitz cutoff `η`
with compact support in `U` and a constant `c`,
`∫ η² ∇u · b ∇u ≤ 4 Λ ∫ (u - c)² |∇η|²`  (manuscript (4.138)).
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4GreenDecay

open MeasureTheory PDE PDE.Ch4Infra

noncomputable section

variable {d : ℕ} {U : Set (Vec d)} {Λ : ℝ} {a : CoeffField d}

/-- **Caccioppoli inequality for solutions** (4.138). -/
theorem caccioppoli_solution_open (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsol : IsWeakDivergenceFormSolutionOn a U u (0 : Vec d → ℝ) 0)
    (c : ℝ) {L M : ℝ} {η : Vec d → ℝ} (hη : EucLip L η) (hL : 0 ≤ L) (hM : ∀ x, |η x| ≤ M)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    ∫ x in U, η x ^ 2 * vecDot (matVecMul (a x) (u.grad x)) (u.grad x) ≤
      4 * Λ * ∫ x in U, (u.toFun x - c) ^ 2 * vecNormSq (classicalGradient η x) := by
  have : IsFiniteMeasure (volumeOn U) := ⟨by simpa [volumeOn] using hfin.lt_top⟩
  let v : H1Function U := u.addConst (-c)
  have hv : ∀ x, v.toFun x = u.toFun x - c := fun x => by
    change u x + -c = _
    ring
  have hvg : ∀ x, v.grad x = u.grad x := fun x => H1Function.grad_addConst u (-c) x
  obtain ⟨h1, h2, heq⟩ := solution_sqTest_lip hU ha hEll hsol v hη hL hM hηc hηU
  simp_rw [hvg, hv] at h1 h2 heq
  set w : Vec d → ℝ := fun x => u.toFun x - c with hw
  have hwL2 : MemL2On U w := by
    have := v.memL2
    have hfun : v.toFun = w := funext hv
    rwa [hfun] at this
  have hG : MemVectorL2On U (fun x => w x • classicalGradient η x) := fun i => by
    simpa only [Pi.smul_apply, smul_eq_mul, classicalGradient] using
      memL2On_mul_partialDeriv hη hL hwL2 i
  have hGsq : IntegrableOn
      (fun x => w x ^ 2 * vecNormSq (classicalGradient η x)) U := by
    simpa only [vecNormSq_smul] using integrableOn_vecNormSq_of_memVectorL2On hG
  have hmem : ∀ᵐ x ∂volumeOn U, x ∈ U :=
    (ae_restrict_iff' hU.measurableSet).2 (Filter.Eventually.of_forall fun _ hx => hx)
  set ξ : Vec d → Vec d := u.grad with hξ
  have hpointwise : ∀ᵐ x ∂volumeOn U,
      |2 * η x * w x * vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x)| ≤
        (η x ^ 2 * vecDot (matVecMul (a x) (ξ x)) (ξ x)) / 2 +
          2 * Λ * (w x ^ 2 * vecNormSq (classicalGradient η x)) := by
    filter_upwards [hmem] with x hx
    have := DGNM.abs_two_mul_mul_vecDot_le_caccioppoli (η := η x) (w := w x)
      (hEll x hx) (ξ x) (classicalGradient η x)
    rw [vecDot_comm (ξ x)] at this
    linarith
  have h1' : IntegrableOn (fun x => η x ^ 2 * vecDot (matVecMul (a x) (ξ x)) (ξ x)) U := h1
  have hboundInt : IntegrableOn (fun x =>
      (η x ^ 2 * vecDot (matVecMul (a x) (ξ x)) (ξ x)) / 2 +
        2 * Λ * (w x ^ 2 * vecNormSq (classicalGradient η x))) U :=
    (h1'.div_const 2).add (hGsq.const_mul (2 * Λ))
  have hbound := integral_mono_ae h2.abs hboundInt hpointwise
  have habs := abs_integral_le_integral_abs (μ := volumeOn U)
    (f := fun x => 2 * η x * w x *
      vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x))
  rw [integral_add (h1'.div_const 2) (hGsq.const_mul (2 * Λ)), integral_div,
    integral_const_mul] at hbound
  have hneg := neg_abs_le (∫ x in U, 2 * η x * w x *
      vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x))
  have heq' : (∫ x in U, η x ^ 2 * vecDot (matVecMul (a x) (ξ x)) (ξ x)) +
      ∫ x in U, 2 * η x * w x * vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x) = 0 := heq
  linarith

/-- **Caccioppoli inequality for solutions with a cutoff between `inner` and `outer`**:
for a `K`-Lipschitz `η` with `|η| ≤ 1` and `tsupport η ⊆ outer ⊆ U`,
`∫_U η² ∇u · b ∇u ≤ 4 Λ K² ∫_outer (u - c)²`. -/
theorem caccioppoli_solution_cutoff_open (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsol : IsWeakDivergenceFormSolutionOn a U u (0 : Vec d → ℝ) 0)
    (c : ℝ) {K : ℝ} {η : Vec d → ℝ} (hη : EucLip K η) (hK : 0 ≤ K) (hM : ∀ x, |η x| ≤ 1)
    {outer : Set (Vec d)} (hηc : HasCompactSupport η) (hηo : tsupport η ⊆ outer)
    (houter : outer ⊆ U) (houterMeas : MeasurableSet outer) :
    ∫ x in U, η x ^ 2 * vecDot (matVecMul (a x) (u.grad x)) (u.grad x) ≤
      4 * Λ * K ^ 2 * ∫ x in outer, (u.toFun x - c) ^ 2 := by
  rcases U.eq_empty_or_nonempty with hUe | ⟨x₀, hx₀⟩
  · subst hUe
    have houterE : outer = ∅ := Set.subset_empty_iff.mp houter
    subst houterE
    simp only [Measure.restrict_empty, integral_zero_measure, mul_zero, le_refl]
  have hΛ : 0 ≤ Λ := (hEll x₀ hx₀).Lam_pos.le
  have hbase := caccioppoli_solution_open hU hfin ha hEll hsol c hη hK hM hηc (hηo.trans houter)
  have : IsFiniteMeasure (volumeOn U) := ⟨by simpa [volumeOn] using hfin.lt_top⟩
  have hwL2 : MemL2On U (fun x => u.toFun x - c) := by
    have h := (u.addConst (-c)).memL2
    have hfun : (u.addConst (-c)).toFun = fun x => u.toFun x - c := by
      funext x; change u.toFun x + -c = _; ring
    rwa [hfun] at h
  have hB : MemVectorL2On U (fun x => (u.toFun x - c) • classicalGradient η x) := fun i => by
    simpa only [Pi.smul_apply, smul_eq_mul, classicalGradient] using
      memL2On_mul_partialDeriv hη hK hwL2 i
  have hBsq : IntegrableOn
      (fun x => (u.toFun x - c) ^ 2 * vecNormSq (classicalGradient η x)) U := by
    simpa only [vecNormSq_smul] using integrableOn_vecNormSq_of_memVectorL2On hB
  have hwsq : IntegrableOn (fun x => (u.toFun x - c) ^ 2) U := by
    simpa only [pow_two] using integrableOn_mul_of_memL2On hwL2 hwL2
  have hrestrict :
      ∫ x in U, (u.toFun x - c) ^ 2 * vecNormSq (classicalGradient η x) =
        ∫ x in outer, (u.toFun x - c) ^ 2 * vecNormSq (classicalGradient η x) :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet houter
      fun x hx => by
        have hxt : x ∉ tsupport η := fun h => hx.2 (hηo h)
        have : classicalGradient η x = 0 := by
          funext i; simp [classicalGradient, fderiv_of_notMem_tsupport ℝ hxt]
        rw [this]
        simp [vecNormSq, vecDot]
  have hle : ∫ x in outer, (u.toFun x - c) ^ 2 * vecNormSq (classicalGradient η x) ≤
      ∫ x in outer, K ^ 2 * (u.toFun x - c) ^ 2 :=
    setIntegral_mono_on (hBsq.mono_set houter) ((hwsq.mono_set houter).const_mul _)
      houterMeas fun x _ => by
        have hg : vecNormSq (classicalGradient η x) ≤ K ^ 2 := by
          rw [← vecEuclideanNorm_sq']
          exact pow_le_pow_left₀ (vecEuclideanNorm_nonneg _)
            (EucLip.vecEuclideanNorm_classicalGradient_le' hη hK x) 2
        nlinarith [sq_nonneg (u.toFun x - c)]
  rw [integral_const_mul] at hle
  calc _ ≤ 4 * Λ * ∫ x in U, (u.toFun x - c) ^ 2 *
          vecNormSq (classicalGradient η x) := hbase
    _ ≤ 4 * Λ * (K ^ 2 * ∫ x in outer, (u.toFun x - c) ^ 2) := by
      rw [hrestrict]
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 4 * Λ * K ^ 2 * ∫ x in outer, (u.toFun x - c) ^ 2 := by ring

end

end PDE.Ch4GreenDecay
