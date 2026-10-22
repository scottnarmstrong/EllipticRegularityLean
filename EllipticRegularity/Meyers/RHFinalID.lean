module

public import EllipticRegularity.Meyers.RHIdentity
public import PDEFoundation.Sobolev.H1.RepresentativeCongruence

/-!
# The basic identity for an admissible smooth cutoff

A variant of `cutoff_energy_le` in which the smooth compactly supported multiplier `η` need not be
supported in `U`; instead the product `η (u - c)` is assumed to be (the value of) an `H¹₀(U)`
function, which then serves as the test function.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.MeyersRH

open MeasureTheory

private theorem vecDot_add_right_fin {d : ℕ} (x y z : Vec d) :
    vecDot x (y + z) = vecDot x y + vecDot x z := by
  simp only [vecDot, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem vecDot_add_left_fin {d : ℕ} (x y z : Vec d) :
    vecDot (x + y) z = vecDot x z + vecDot y z := by
  simp only [vecDot, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem vecDot_smul_right_fin {d : ℕ} (x y : Vec d) (c : ℝ) :
    vecDot x (c • y) = c * vecDot x y := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The basic identity of Lemma 4.5 for an admissible smooth compactly supported `η ≥ 0`. -/
theorem cutoff_energy_le_admissible
    {d : ℕ} {Λ c : ℝ} {U : Set (Vec d)} {a : CoeffField d}
    (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn 1 Λ U a)
    (u : H1Function U) (f : Vec d → Vec d) (hf : MemVectorL2On U f)
    (hsol : IsWeakDivergenceFormSolutionOn a U u (0 : Vec d → ℝ) f)
    (η : Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hη0 : ∀ x, 0 ≤ η x)
    (hφ : ∃ v : H10Function U, v.toFun = fun x => η x * (u x - c)) :
    ∫ x in U, η x * vecDot (u.grad x) (matVecMul (a x) (u.grad x)) ≤
      2 * |∫ x in U, (u x - c) *
          vecDot (matVecMul (a x) (u.grad x) + f x) (classicalGradient η x)| +
        ∫ x in U, η x * vecNormSq (f x) := by
  obtain ⟨φ, hφval⟩ := hφ
  let flux : Vec d → Vec d := fun x => matVecMul (a x) (u.grad x)
  let g1 : Vec d → Vec d := fun x => η x • u.grad x
  let G : Vec d → Vec d := fun x => (u x - c) • classicalGradient η x
  have hflux : MemVectorL2On U flux :=
    memVectorL2On_matVecMul_of_isEllipticFieldOn hEll u.gradMemL2
  have hηTop : MemLpOn U ∞ η :=
    (hη.continuous.memLp_of_hasCompactSupport hηc).restrict U
  have hDηTop (i : Fin d) : MemLpOn U ∞ (fun x => classicalGradient η x i) := by
    have hcont : Continuous (fun x => classicalGradient η x i) := by
      simpa only [classicalGradient_apply] using
        (hη.continuous_fderiv (by simp)).clm_apply continuous_const
    have hcomp : HasCompactSupport (fun x => classicalGradient η x i) := by
      simpa only [classicalGradient_apply] using
        hηc.fderiv_apply (𝕜 := ℝ) (basisVec i)
    exact (hcont.memLp_of_hasCompactSupport hcomp).restrict U
  have hw : MemL2On U (fun x => u x - c) := by
    simpa only [H1Function.subConst_apply] using! (u.subConst hU c).memL2
  have hg1 : MemVectorL2On U g1 := memVectorL2On_smul_of_memLpTop hηTop u.gradMemL2
  have hG : MemVectorL2On U G := by
    intro i
    simpa only [G, Pi.smul_apply, smul_eq_mul, mul_comm] using hw.fun_mul (hDηTop i)
  have hηf : MemVectorL2On U (fun x => η x • f x) := memVectorL2On_smul_of_memLpTop hηTop hf
  -- the gradient of the test function
  let w : H1Function U := (u.subConst hU c).mulContDiffHasCompactSupport hη hηc
  have hwval : w.toFun = φ.toH1Function.toFun := by
    rw [hφval]
    funext x
    simp only [w, H1Function.mulContDiffHasCompactSupport_toFun, H1Function.subConst_apply]
  have hwgrad : w.grad = fun x => g1 x + G x := by
    funext x
    simp only [w, H1Function.mulContDiffHasCompactSupport_grad, H1Function.subConst_apply,
      H1Function.grad_subConst, g1, G]
  have hgradae : ∀ᵐ x ∂(volumeOn U), φ.toH1Function.grad x = g1 x + G x := by
    have hall : ∀ᵐ x ∂(volumeOn U), ∀ i : Fin d, w.grad x i = φ.toH1Function.grad x i :=
      ae_all_iff.2 fun i =>
        H1Function.grad_coord_ae_eq_of_toFun_eq hU.isOpen w φ.toH1Function hwval i
    filter_upwards [hall] with x hx
    funext i
    rw [← hx i, hwgrad]
  have hf0 : MemL2On U (0 : Vec d → ℝ) := MemLp.zero
  have htest := (hsol.toH10SolutionOn_of_isEllipticFieldOn hEll hf0 hf) φ
  have hweak : (∫ x in U, vecDot (flux x) (φ.toH1Function.grad x)) +
      ∫ x in U, vecDot (f x) (φ.toH1Function.grad x) = 0 := by
    have h := htest.2
    simp only [Pi.zero_apply, zero_mul, integral_zero, zero_sub] at h
    change (∫ x in U, vecDot (flux x) (φ.toH1Function.grad x)) = _ at h
    linarith
  have hc1 : ∫ x in U, vecDot (flux x) (φ.toH1Function.grad x) =
      ∫ x in U, vecDot (flux x) (g1 x + G x) :=
    integral_congr_ae (hgradae.mono fun x hx => by simp only [hx])
  have hc2 : ∫ x in U, vecDot (f x) (φ.toH1Function.grad x) =
      ∫ x in U, vecDot (f x) (g1 x + G x) :=
    integral_congr_ae (hgradae.mono fun x hx => by simp only [hx])
  rw [hc1, hc2] at hweak
  -- integrability
  have iFg1 := integrableOn_vecDot_of_memVectorL2On hflux hg1
  have iFG := integrableOn_vecDot_of_memVectorL2On hflux hG
  have ifg1 := integrableOn_vecDot_of_memVectorL2On hf hg1
  have ifG := integrableOn_vecDot_of_memVectorL2On hf hG
  have hsplit : (∫ x in U, vecDot (flux x) (g1 x)) +
      ((∫ x in U, vecDot (flux x) (G x)) + ∫ x in U, vecDot (f x) (G x)) +
      (∫ x in U, vecDot (f x) (g1 x)) = 0 := by
    have e1 : ∫ x in U, vecDot (flux x) (g1 x + G x) =
        (∫ x in U, vecDot (flux x) (g1 x)) + ∫ x in U, vecDot (flux x) (G x) := by
      rw [← integral_add iFg1 iFG]
      exact integral_congr_ae
        (Filter.Eventually.of_forall fun x => vecDot_add_right_fin _ _ _)
    have e2 : ∫ x in U, vecDot (f x) (g1 x + G x) =
        (∫ x in U, vecDot (f x) (g1 x)) + ∫ x in U, vecDot (f x) (G x) := by
      rw [← integral_add ifg1 ifG]
      exact integral_congr_ae
        (Filter.Eventually.of_forall fun x => vecDot_add_right_fin _ _ _)
    rw [e1, e2] at hweak
    linarith
  have hI1 : ∫ x in U, vecDot (flux x) (g1 x) =
      ∫ x in U, η x * vecDot (u.grad x) (matVecMul (a x) (u.grad x)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [g1, flux]
    rw [vecDot_smul_right_fin, vecDot_comm]
  have hI2 : (∫ x in U, vecDot (flux x) (G x)) + ∫ x in U, vecDot (f x) (G x) =
      ∫ x in U, (u x - c) *
          vecDot (matVecMul (a x) (u.grad x) + f x) (classicalGradient η x) := by
    rw [← integral_add iFG ifG]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [G, flux]
    rw [vecDot_smul_right_fin, vecDot_smul_right_fin, vecDot_add_left_fin]
    ring
  rw [hI1, hI2] at hsplit
  set I1 := ∫ x in U, η x * vecDot (u.grad x) (matVecMul (a x) (u.grad x)) with hI1def
  set I2 := ∫ x in U, (u x - c) *
          vecDot (matVecMul (a x) (u.grad x) + f x) (classicalGradient η x) with hI2def
  set I3 := ∫ x in U, vecDot (f x) (g1 x) with hI3def
  have hI3 : |I3| ≤ (∫ x in U, η x * vecNormSq (f x)) / 2 + I1 / 2 := by
    have iηf := integrableOn_vecDot_of_memVectorL2On hf hηf
    have iηfsq : IntegrableOn (fun x => η x * vecNormSq (f x)) U := by
      refine (integrableOn_congr_fun_ae (Filter.Eventually.of_forall fun x => ?_)).mp iηf
      show vecDot (f x) (η x • f x) = η x * vecNormSq (f x)
      rw [vecDot_smul_right_fin]; rfl
    have iI1 : IntegrableOn
        (fun x => η x * vecDot (u.grad x) (matVecMul (a x) (u.grad x))) U := by
      refine (integrableOn_congr_fun_ae (Filter.Eventually.of_forall fun x => ?_)).mp iFg1
      show vecDot (flux x) (g1 x) = _
      simp only [g1, flux]
      rw [vecDot_smul_right_fin, vecDot_comm]
    have hle : |I3| ≤ ∫ x in U, ‖vecDot (f x) (g1 x)‖ := by
      rw [hI3def, ← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
    refine hle.trans ?_
    have hbound : ∀ x ∈ U, ‖vecDot (f x) (g1 x)‖ ≤
        η x * vecNormSq (f x) / 2 +
          η x * vecDot (u.grad x) (matVecMul (a x) (u.grad x)) / 2 := by
      intro x hx
      have hA := hEll.elliptic hx
      have hη0x := hη0 x
      have hcoer : vecNormSq (u.grad x) ≤ vecDot (u.grad x) (matVecMul (a x) (u.grad x)) := by
        simpa using hA.coercive (u.grad x)
      have hy := abs_vecDot_le_add_halves_vecNormSq (f x) (u.grad x)
      simp only [g1, Real.norm_eq_abs]
      rw [vecDot_smul_right_fin, abs_mul, abs_of_nonneg hη0x]
      calc η x * |vecDot (f x) (u.grad x)| ≤
          η x * (vecNormSq (f x) / 2 + vecNormSq (u.grad x) / 2) :=
            mul_le_mul_of_nonneg_left hy hη0x
        _ ≤ _ := by nlinarith
    calc ∫ x in U, ‖vecDot (f x) (g1 x)‖ ≤
        ∫ x in U, (η x * vecNormSq (f x) / 2 +
          η x * vecDot (u.grad x) (matVecMul (a x) (u.grad x)) / 2) := by
          refine setIntegral_mono_on ?_ ?_ hU.measurableSet hbound
          · exact (ifg1.norm)
          · exact (iηfsq.div_const 2).add (iI1.div_const 2)
      _ = _ := by
          rw [integral_add (iηfsq.div_const 2) (iI1.div_const 2), integral_div, integral_div]
  linarith [abs_nonneg I2, le_abs_self I2, neg_abs_le I2, le_abs_self I3, neg_abs_le I3]

end PDE.MeyersRH
