module

public import EllipticRegularity.Meyers.EnergyBounds
public import PDEFoundation.PDE.WeakDivergenceForm
public import PDEFoundation.Sobolev.H1.ZeroBoundaryCutoff

/-!
# The basic identity of the Meyers reverse Hölder inequality

For `u ∈ H¹(U)` solving `-∇·a∇u = ∇·f` with `f ∈ L²`, a smooth compactly supported cutoff
`η ≥ 0` (supported in `U`) and a constant `c`, testing the equation with `η (u - c)` gives
`∫ η w² ≤ 2 |∫ (u - c) (a∇u + f)·∇η| + ∫ η |f|²`, where `w² = ∇u · a∇u`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.MeyersRH

open MeasureTheory

private theorem vecDot_add_right' {d : ℕ} (x y z : Vec d) :
    vecDot x (y + z) = vecDot x y + vecDot x z := by
  simp only [vecDot, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem vecDot_add_left' {d : ℕ} (x y z : Vec d) :
    vecDot (x + y) z = vecDot x z + vecDot y z := by
  simp only [vecDot, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem vecDot_smul_right' {d : ℕ} (x y : Vec d) (c : ℝ) :
    vecDot x (c • y) = c * vecDot x y := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem vecDot_smul_left' {d : ℕ} (x y : Vec d) (c : ℝ) :
    vecDot (c • x) y = c * vecDot x y := by
  rw [vecDot_comm, vecDot_smul_right', vecDot_comm]

theorem memVectorL2On_smul_of_memLpTop {d : ℕ} {U : Set (Vec d)} {F : Vec d → Vec d}
    {g : Vec d → ℝ} (hg : MemLpOn U ∞ g) (hF : MemVectorL2On U F) :
    MemVectorL2On U (fun x => g x • F x) := by
  intro i
  simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using (hF i).fun_mul hg

/-- The basic identity of Lemma 4.5 (Step 1), in inequality form. -/
theorem cutoff_energy_le
    {d : ℕ} {Λ K c : ℝ} {U inner outer : Set (Vec d)} {a : CoeffField d}
    (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn 1 Λ U a)
    (u : H1Function U) (f : Vec d → Vec d) (hf : MemVectorL2On U f)
    (hsol : IsWeakDivergenceFormSolutionOn a U u (0 : Vec d → ℝ) f)
    (η : QuantitativeSmoothCutoff inner outer K) (houter : outer ⊆ U) :
    ∫ x in U, η x * vecDot (u.grad x) (matVecMul (a x) (u.grad x)) ≤
      2 * |∫ x in U, (u x - c) *
          vecDot (matVecMul (a x) (u.grad x) + f x) (classicalGradient η.toFun x)| +
        ∫ x in U, η x * vecNormSq (f x) := by
  let flux : Vec d → Vec d := fun x => matVecMul (a x) (u.grad x)
  let g1 : Vec d → Vec d := fun x => η x • u.grad x
  let G : Vec d → Vec d := fun x => (u x - c) • classicalGradient η.toFun x
  have hflux : MemVectorL2On U flux :=
    memVectorL2On_matVecMul_of_isEllipticFieldOn hEll u.gradMemL2
  have hηTop : MemLpOn U ∞ η.toFun := W1pFunction.cutoff_memLpTop η
  have hDηTop (i : Fin d) : MemLpOn U ∞ (fun x => classicalGradient η.toFun x i) :=
    W1pFunction.cutoff_gradient_memLpTop η i
  have hw : MemL2On U (fun x => u x - c) := by
    simpa only [H1Function.subConst_apply] using! (u.subConst hU c).memL2
  have hg1 : MemVectorL2On U g1 := memVectorL2On_smul_of_memLpTop hηTop u.gradMemL2
  have hG : MemVectorL2On U G := by
    intro i
    simpa only [G, Pi.smul_apply, smul_eq_mul, mul_comm] using hw.fun_mul (hDηTop i)
  have hηf : MemVectorL2On U (fun x => η x • f x) := memVectorL2On_smul_of_memLpTop hηTop hf
  -- the test function
  let φ : H10Function U := (u.subConst hU c).mulCutoffToH10 hU η houter
  have hφgrad : φ.toH1Function.grad = fun x => g1 x + G x := by
    rw [show φ = (u.subConst hU c).mulCutoffToH10 hU η houter from rfl,
      H1Function.mulCutoffToH10_grad]
    funext x
    simp only [H1Function.subConst_apply, H1Function.grad_subConst, g1, G]
  have hf0 : MemL2On U (0 : Vec d → ℝ) := MemLp.zero
  have htest := (hsol.toH10SolutionOn_of_isEllipticFieldOn hEll hf0 hf) φ
  have hweak : (∫ x in U, vecDot (flux x) (φ.toH1Function.grad x)) +
      ∫ x in U, vecDot (f x) (φ.toH1Function.grad x) = 0 := by
    have h := htest.2
    simp only [Pi.zero_apply, zero_mul, integral_zero, zero_sub] at h
    change (∫ x in U, vecDot (flux x) (φ.toH1Function.grad x)) = _ at h
    linarith
  rw [hφgrad] at hweak
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
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => vecDot_add_right' _ _ _)
    have e2 : ∫ x in U, vecDot (f x) (g1 x + G x) =
        (∫ x in U, vecDot (f x) (g1 x)) + ∫ x in U, vecDot (f x) (G x) := by
      rw [← integral_add ifg1 ifG]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => vecDot_add_right' _ _ _)
    change (∫ x in U, vecDot (flux x) (g1 x + G x)) +
      ∫ x in U, vecDot (f x) (g1 x + G x) = 0 at hweak
    rw [e1, e2] at hweak
    linarith
  -- rewrite the three integrals
  have hI1 : ∫ x in U, vecDot (flux x) (g1 x) =
      ∫ x in U, η x * vecDot (u.grad x) (matVecMul (a x) (u.grad x)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [g1, flux]
    rw [vecDot_smul_right', vecDot_comm]
  have hI2 : (∫ x in U, vecDot (flux x) (G x)) + ∫ x in U, vecDot (f x) (G x) =
      ∫ x in U, (u x - c) *
          vecDot (matVecMul (a x) (u.grad x) + f x) (classicalGradient η.toFun x) := by
    rw [← integral_add iFG ifG]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [G, flux]
    rw [vecDot_smul_right', vecDot_smul_right', vecDot_add_left']
    ring
  rw [hI1, hI2] at hsplit
  set I1 := ∫ x in U, η x * vecDot (u.grad x) (matVecMul (a x) (u.grad x)) with hI1def
  set I2 := ∫ x in U, (u x - c) *
          vecDot (matVecMul (a x) (u.grad x) + f x) (classicalGradient η.toFun x) with hI2def
  set I3 := ∫ x in U, vecDot (f x) (g1 x) with hI3def
  have hI3 : |I3| ≤ (∫ x in U, η x * vecNormSq (f x)) / 2 + I1 / 2 := by
    have iηf := integrableOn_vecDot_of_memVectorL2On hf hηf
    have iηfsq : IntegrableOn (fun x => η x * vecNormSq (f x)) U := by
      refine (integrableOn_congr_fun_ae (Filter.Eventually.of_forall fun x => ?_)).mp iηf
      show vecDot (f x) (η x • f x) = η x * vecNormSq (f x)
      rw [vecDot_smul_right']; rfl
    have iI1 : IntegrableOn (fun x => η x * vecDot (u.grad x) (matVecMul (a x) (u.grad x))) U := by
      refine (integrableOn_congr_fun_ae (Filter.Eventually.of_forall fun x => ?_)).mp iFg1
      show vecDot (flux x) (g1 x) = _
      simp only [g1, flux]
      rw [vecDot_smul_right', vecDot_comm]
    have hle : |I3| ≤ ∫ x in U, ‖vecDot (f x) (g1 x)‖ := by
      rw [hI3def, ← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
    refine hle.trans ?_
    have hbound : ∀ x ∈ U, ‖vecDot (f x) (g1 x)‖ ≤
        η x * vecNormSq (f x) / 2 +
          η x * vecDot (u.grad x) (matVecMul (a x) (u.grad x)) / 2 := by
      intro x hx
      have hA := hEll.elliptic hx
      have hη0 := η.nonneg x
      have hcoer : vecNormSq (u.grad x) ≤ vecDot (u.grad x) (matVecMul (a x) (u.grad x)) := by
        simpa using hA.coercive (u.grad x)
      have hy := abs_vecDot_le_add_halves_vecNormSq (f x) (u.grad x)
      simp only [g1, Real.norm_eq_abs]
      rw [vecDot_smul_right', abs_mul, abs_of_nonneg hη0]
      calc η x * |vecDot (f x) (u.grad x)| ≤
          η x * (vecNormSq (f x) / 2 + vecNormSq (u.grad x) / 2) :=
            mul_le_mul_of_nonneg_left hy hη0
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
