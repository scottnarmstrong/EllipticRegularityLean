module

public import EllipticRegularity.Parabolic.Sobolev.EndpointProof
public import EllipticRegularity.Parabolic.Sobolev.ParabolicGN
public import PDEFoundation.Measure.FiniteVectorConvergence
public import PDEFoundation.Measure.EuclideanFieldNormTendsto
public import PDEFoundation.Measure.LpTendsto
public import PDEFoundation.Sobolev.Inequalities.SobolevWholeSpaceDensity
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Endpoint parabolic Gagliardo--Nirenberg estimates

This file passes the compactly supported smooth endpoint inequalities to
whole-space `H¹` representatives using the project's supported smooth density
certificate, and records the integral-energy forms used in time integration.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE.Parabolic

open Filter MeasureTheory Set

/-- In dimension two, the whole-space `H¹` Gagliardo--Nirenberg inequality
at the parabolic spatial exponent `4`. -/
theorem h1_two_dimensional_gagliardo_nirenberg
    (u : H1Function (Set.univ : Set (Vec 2))) :
    (eLpNorm u.toFun 4 volume) ^ (2 : ℝ) ≤
      ENNReal.ofReal (4 * (sobolevOneConstant 2 : ℝ)) *
        eLpNorm u.toFun 2 volume *
          eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 volume := by
  let uw : W1pFunction (Set.univ : Set (Vec 2)) 2 :=
    u.toW1pFunction
  obtain ⟨ha⟩ := W1pFunction.hasSupportedSmoothApproximation_univ
    (by norm_num) (by norm_num) uw
  let ψ : ℕ → Vec 2 → ℝ := ha.approx
  have hψSmooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (ψ n) := ha.approx_smooth n
  have hψCont (n : ℕ) : Continuous (ψ n) := (hψSmooth n).continuous
  have huMem : MemLp u.toFun 2 volume := by
    simpa only [MemL2On, MemLpOn, volumeOn,
      Measure.restrict_univ] using u.memL2
  have hψMem (n : ℕ) : MemLp (ψ n) 2 volume := by
    exact (hψCont n).memLp_of_hasCompactSupport (ha.approx_hasCompactSupport n)
  have hValueTendsto :
      Tendsto (fun n => eLpNorm (ψ n - u.toFun) 2 volume)
        atTop (𝓝 0) := by
    simpa only [ψ, uw, H1Function.toW1pFunction_toFun, volumeOn,
      Measure.restrict_univ] using ha.tendsto_value
  have hValueNormTendsto :
      Tendsto (fun n => eLpNorm (ψ n) 2 volume) atTop
        (𝓝 (eLpNorm u.toFun 2 volume)) :=
    tendsto_eLpNorm_of_tendsto_sub (by norm_num)
      (fun n => (hψCont n).aestronglyMeasurable)
      huMem.aestronglyMeasurable huMem.eLpNorm_ne_top hValueTendsto
  have hGradNormMem :
      MemLp (fun x => vecEuclideanNorm (u.grad x)) 2 volume := by
    simpa only [volumeOn, Measure.restrict_univ, ENNReal.ofReal_ofNat] using
      u.gradMemL2.memLp_vecEuclideanNorm
  have hψC1 (n : ℕ) : ContDiff ℝ 1 (ψ n) :=
    (hψSmooth n).of_le (by norm_num)
  have hGradCoordMeas (n : ℕ) (i : Fin 2) :
      AEStronglyMeasurable
        (fun x => classicalGradient (ψ n) x i - u.grad x i) volume := by
    have hleft : AEStronglyMeasurable
        (fun x => classicalGradient (ψ n) x i) volume := by
      exact ((hψC1 n).continuous_fderiv (by norm_num)).clm_apply
        continuous_const |>.aestronglyMeasurable
    have hright : AEStronglyMeasurable (fun x => u.grad x i) volume := by
      simpa only [GradMemL2On, MemLpOn, volumeOn,
        Measure.restrict_univ] using (u.gradMemL2 i).aestronglyMeasurable
    exact hleft.sub hright
  have hGradCoordTendsto (i : Fin 2) :
      Tendsto
        (fun n => eLpNorm
          (fun x => classicalGradient (ψ n) x i - u.grad x i) 2 volume)
        atTop (𝓝 0) := by
    simpa only [ψ, uw, classicalGradient_apply, H1Function.toW1pFunction_grad,
      volumeOn, Measure.restrict_univ] using ha.tendsto_grad i
  have hGradDiffTendsto :
      Tendsto
        (fun n => eLpNorm
          (fun x => vecEuclideanNorm (classicalGradient (ψ n) x - u.grad x))
          2 volume)
        atTop (𝓝 0) :=
    tendsto_eLpNorm_vecEuclideanNorm_sub_zero_of_coordinate
      (by norm_num) hGradCoordMeas hGradCoordTendsto
  have hGradSeqCoordMem (n : ℕ) (i : Fin 2) :
      MemLp (fun x => classicalGradient (ψ n) x i) 2 volume := by
    have hcont : Continuous (fun x => classicalGradient (ψ n) x i) :=
      ((hψC1 n).continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hcompact : HasCompactSupport
        (fun x => classicalGradient (ψ n) x i) := by
      simpa only [classicalGradient_apply] using
        (ha.approx_hasCompactSupport n).fderiv_apply
          (𝕜 := ℝ) (basisVec i)
    exact hcont.memLp_of_hasCompactSupport hcompact
  have hGradNormTendsto :
      Tendsto
        (fun n => eLpNorm
          (fun x => vecEuclideanNorm (classicalGradient (ψ n) x)) 2 volume)
        atTop
        (𝓝 (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 volume)) :=
    tendsto_eLpNorm_vecEuclideanNorm_of_sub (by norm_num)
      hGradSeqCoordMem
      (fun i => by
        simpa only [GradMemL2On, MemLpOn, volumeOn,
          Measure.restrict_univ] using u.gradMemL2 i)
      hGradDiffTendsto
  have hInMeasure : TendstoInMeasure volume ψ atTop u.toFun :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := (2 : ℝ≥0∞))
      (by norm_num) hValueTendsto
  obtain ⟨σ, hσmono, hσae⟩ := hInMeasure.exists_seq_tendsto_ae
  let high : ℕ → ℝ≥0∞ := fun n => eLpNorm (ψ (σ n)) 4 volume
  let rhs : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (4 * (sobolevOneConstant 2 : ℝ)) *
      eLpNorm (ψ (σ n)) 2 volume *
        eLpNorm (fun x => vecEuclideanNorm (classicalGradient (ψ (σ n)) x))
          2 volume
  let rhsLim : ℝ≥0∞ :=
    ENNReal.ofReal (4 * (sobolevOneConstant 2 : ℝ)) *
      eLpNorm u.toFun 2 volume *
        eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 volume
  have hRhsTendsto : Tendsto rhs atTop (𝓝 rhsLim) := by
    have hval := hValueNormTendsto.comp hσmono.tendsto_atTop
    have hgrad := hGradNormTendsto.comp hσmono.tendsto_atTop
    have hprod := ENNReal.Tendsto.mul hval
      (Or.inr hGradNormMem.eLpNorm_ne_top) hgrad
      (Or.inr huMem.eLpNorm_ne_top)
    have hconst := ENNReal.Tendsto.const_mul
      (a := ENNReal.ofReal (4 * (sobolevOneConstant 2 : ℝ))) hprod
      (Or.inr ENNReal.ofReal_ne_top)
    simpa only [rhs, rhsLim, Function.comp_apply, mul_assoc] using hconst
  have hRootTendsto :
      Tendsto (fun n => rhs n ^ (1 / 2 : ℝ)) atTop
        (𝓝 (rhsLim ^ (1 / 2 : ℝ))) := by
    exact (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto _ |>.comp
      hRhsTendsto
  have hrootBound (n : ℕ) : high n ≤ rhs n ^ (1 / 2 : ℝ) := by
    have hsmooth := smooth_two_dimensional_gagliardo_nirenberg
      (hψSmooth (σ n)) (ha.approx_hasCompactSupport (σ n))
    have hroot := ENNReal.rpow_le_rpow hsmooth
      (by norm_num : 0 ≤ (1 / 2 : ℝ))
    rw [← ENNReal.rpow_mul] at hroot
    have hexp : (2 : ℝ) * (1 / 2 : ℝ) = 1 := by norm_num
    simpa only [high, rhs, hexp, ENNReal.rpow_one,
      mul_assoc] using hroot
  have hliminfBound :
      Filter.liminf (fun n => high n) atTop ≤ rhsLim ^ (1 / 2 : ℝ) := by
    calc
      Filter.liminf (fun n => high n) atTop ≤
          Filter.liminf (fun n => rhs n ^ (1 / 2 : ℝ)) atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hrootBound)
      _ = rhsLim ^ (1 / 2 : ℝ) := hRootTendsto.liminf_eq
  have hFatou : eLpNorm u.toFun 4 volume ≤ Filter.liminf high atTop :=
    Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun n => (hψCont (σ n)).aestronglyMeasurable)
      u.toFun huMem.aestronglyMeasurable hσae
  have hnormRoot : eLpNorm u.toFun 4 volume ≤ rhsLim ^ (1 / 2 : ℝ) :=
    hFatou.trans hliminfBound
  have hnormSq := ENNReal.rpow_le_rpow hnormRoot
    (by norm_num : 0 ≤ (2 : ℝ))
  rw [← ENNReal.rpow_mul] at hnormSq
  have hexp : (1 / 2 : ℝ) * 2 = 1 := by norm_num
  simpa only [hexp, ENNReal.rpow_one, rhsLim, mul_assoc] using hnormSq

/-- In dimension one, the whole-space `H¹` Gagliardo--Nirenberg inequality
at the parabolic spatial exponent `6`, in powered `Lᵖ`-norm form. -/
theorem h1_one_dimensional_gagliardo_nirenberg_energy
    (u : H1Function (Set.univ : Set (Vec 1))) :
    (eLpNorm u.toFun 6 volume) ^ (6 : ℝ) ≤
      ENNReal.ofReal 4 * (eLpNorm u.toFun 2 volume) ^ 4 *
        (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 volume) ^ 2 := by
  let uw : W1pFunction (Set.univ : Set (Vec 1)) 2 := u.toW1pFunction
  obtain ⟨ha⟩ := W1pFunction.hasSupportedSmoothApproximation_univ
    (by norm_num) (by norm_num) uw
  let ψ : ℕ → Vec 1 → ℝ := ha.approx
  have hψSmooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (ψ n) := ha.approx_smooth n
  have hψCont (n : ℕ) : Continuous (ψ n) := (hψSmooth n).continuous
  have huMem : MemLp u.toFun 2 volume := by
    simpa only [MemL2On, MemLpOn, volumeOn,
      Measure.restrict_univ] using u.memL2
  have hValueTendsto :
      Tendsto (fun n => eLpNorm (ψ n - u.toFun) 2 volume)
        atTop (𝓝 0) := by
    simpa only [ψ, uw, H1Function.toW1pFunction_toFun, volumeOn,
      Measure.restrict_univ] using ha.tendsto_value
  have hValueNormTendsto :
      Tendsto (fun n => eLpNorm (ψ n) 2 volume) atTop
        (𝓝 (eLpNorm u.toFun 2 volume)) :=
    tendsto_eLpNorm_of_tendsto_sub (by norm_num)
      (fun n => (hψCont n).aestronglyMeasurable)
      huMem.aestronglyMeasurable huMem.eLpNorm_ne_top hValueTendsto
  have hGradNormMem :
      MemLp (fun x => vecEuclideanNorm (u.grad x)) 2 volume := by
    simpa only [volumeOn, Measure.restrict_univ, ENNReal.ofReal_ofNat] using
      u.gradMemL2.memLp_vecEuclideanNorm
  have hψC1 (n : ℕ) : ContDiff ℝ 1 (ψ n) :=
    (hψSmooth n).of_le (by norm_num)
  have hGradCoordMeas (n : ℕ) (i : Fin 1) :
      AEStronglyMeasurable
        (fun x => classicalGradient (ψ n) x i - u.grad x i) volume := by
    have hleft : AEStronglyMeasurable
        (fun x => classicalGradient (ψ n) x i) volume := by
      exact ((hψC1 n).continuous_fderiv (by norm_num)).clm_apply
        continuous_const |>.aestronglyMeasurable
    have hright : AEStronglyMeasurable (fun x => u.grad x i) volume := by
      simpa only [GradMemL2On, MemLpOn, volumeOn,
        Measure.restrict_univ] using (u.gradMemL2 i).aestronglyMeasurable
    exact hleft.sub hright
  have hGradCoordTendsto (i : Fin 1) :
      Tendsto
        (fun n => eLpNorm
          (fun x => classicalGradient (ψ n) x i - u.grad x i) 2 volume)
        atTop (𝓝 0) := by
    simpa only [ψ, uw, classicalGradient_apply, H1Function.toW1pFunction_grad,
      volumeOn, Measure.restrict_univ] using ha.tendsto_grad i
  have hGradDiffTendsto :
      Tendsto
        (fun n => eLpNorm
          (fun x => vecEuclideanNorm (classicalGradient (ψ n) x - u.grad x))
          2 volume)
        atTop (𝓝 0) :=
    tendsto_eLpNorm_vecEuclideanNorm_sub_zero_of_coordinate
      (by norm_num) hGradCoordMeas hGradCoordTendsto
  have hGradSeqCoordMem (n : ℕ) (i : Fin 1) :
      MemLp (fun x => classicalGradient (ψ n) x i) 2 volume := by
    have hcont : Continuous (fun x => classicalGradient (ψ n) x i) :=
      ((hψC1 n).continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hcompact : HasCompactSupport
        (fun x => classicalGradient (ψ n) x i) := by
      simpa only [classicalGradient_apply] using
        (ha.approx_hasCompactSupport n).fderiv_apply
          (𝕜 := ℝ) (basisVec i)
    exact hcont.memLp_of_hasCompactSupport hcompact
  have hGradNormTendsto :
      Tendsto
        (fun n => eLpNorm
          (fun x => vecEuclideanNorm (classicalGradient (ψ n) x)) 2 volume)
        atTop
        (𝓝 (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 volume)) :=
    tendsto_eLpNorm_vecEuclideanNorm_of_sub (by norm_num)
      hGradSeqCoordMem
      (fun i => by
        simpa only [GradMemL2On, MemLpOn, volumeOn,
          Measure.restrict_univ] using u.gradMemL2 i)
      hGradDiffTendsto
  have hInMeasure : TendstoInMeasure volume ψ atTop u.toFun :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := (2 : ℝ≥0∞))
      (by norm_num) hValueTendsto
  obtain ⟨σ, hσmono, hσae⟩ := hInMeasure.exists_seq_tendsto_ae
  let high : ℕ → ℝ≥0∞ := fun n => eLpNorm (ψ (σ n)) 6 volume
  let rhs : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal 4 * (eLpNorm (ψ (σ n)) 2 volume) ^ ((4 : ℕ) : ℝ) *
      (eLpNorm (fun x => vecEuclideanNorm (classicalGradient (ψ (σ n)) x))
        2 volume) ^ ((2 : ℕ) : ℝ)
  let rhsLim : ℝ≥0∞ :=
    ENNReal.ofReal 4 * (eLpNorm u.toFun 2 volume) ^ ((4 : ℕ) : ℝ) *
      (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 volume) ^ ((2 : ℕ) : ℝ)
  have hValuePowTendsto :
      Tendsto (fun n => eLpNorm (ψ n) 2 volume ^ ((4 : ℕ) : ℝ)) atTop
        (𝓝 (eLpNorm u.toFun 2 volume ^ ((4 : ℕ) : ℝ))) :=
    (ENNReal.continuous_rpow_const (y := ((4 : ℕ) : ℝ))).tendsto _ |>.comp
      hValueNormTendsto
  have hGradPowTendsto :
      Tendsto
        (fun n => eLpNorm (fun x => vecEuclideanNorm (classicalGradient (ψ n) x))
          2 volume ^ ((2 : ℕ) : ℝ)) atTop
        (𝓝 (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 volume ^ ((2 : ℕ) : ℝ))) :=
    (ENNReal.continuous_rpow_const (y := ((2 : ℕ) : ℝ))).tendsto _ |>.comp
      hGradNormTendsto
  have hValuePowTop : eLpNorm u.toFun 2 volume ^ ((4 : ℕ) : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) huMem.eLpNorm_ne_top
  have hGradPowTop :
      eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 volume ^ ((2 : ℕ) : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hGradNormMem.eLpNorm_ne_top
  have hProductTendsto :
      Tendsto
        (fun n => eLpNorm (ψ (σ n)) 2 volume ^ ((4 : ℕ) : ℝ) *
          eLpNorm (fun x => vecEuclideanNorm (classicalGradient (ψ (σ n)) x))
            2 volume ^ ((2 : ℕ) : ℝ)) atTop
        (𝓝 (eLpNorm u.toFun 2 volume ^ ((4 : ℕ) : ℝ) *
          eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 volume ^ ((2 : ℕ) : ℝ))) :=
    ENNReal.Tendsto.mul
      (hValuePowTendsto.comp hσmono.tendsto_atTop) (Or.inr hGradPowTop)
      (hGradPowTendsto.comp hσmono.tendsto_atTop) (Or.inr hValuePowTop)
  have hRhsTendsto : Tendsto rhs atTop (𝓝 rhsLim) := by
    have hconst := ENNReal.Tendsto.const_mul
      (a := ENNReal.ofReal 4) hProductTendsto (Or.inr ENNReal.ofReal_ne_top)
    simpa only [rhs, rhsLim, Function.comp_apply, mul_assoc] using hconst
  have hRootTendsto :
      Tendsto (fun n => rhs n ^ (1 / 6 : ℝ)) atTop
        (𝓝 (rhsLim ^ (1 / 6 : ℝ))) :=
    (ENNReal.continuous_rpow_const (y := (1 / 6 : ℝ))).tendsto _ |>.comp
      hRhsTendsto
  have hrootBound (n : ℕ) : high n ≤ rhs n ^ (1 / 6 : ℝ) := by
    have hsmooth := smooth_one_dimensional_gagliardo_nirenberg_lp_energy
      (hψSmooth (σ n)) (ha.approx_hasCompactSupport (σ n))
    have hsmoothRpow :
        (eLpNorm (ψ (σ n)) 6 volume) ^ ((6 : ℕ) : ℝ) ≤
          ENNReal.ofReal 4 * (eLpNorm (ψ (σ n)) 2 volume) ^ ((4 : ℕ) : ℝ) *
            (eLpNorm (fun x => vecEuclideanNorm
              (classicalGradient (ψ (σ n)) x)) 2 volume) ^ ((2 : ℕ) : ℝ) := by
      rw [ENNReal.rpow_natCast, ENNReal.rpow_natCast,
        ENNReal.rpow_natCast]
      exact hsmooth
    have hroot := ENNReal.rpow_le_rpow hsmoothRpow
      (by norm_num : 0 ≤ (1 / 6 : ℝ))
    rw [← ENNReal.rpow_mul] at hroot
    have hexp : ((6 : ℕ) : ℝ) * (1 / 6 : ℝ) = 1 := by norm_num
    simpa only [high, rhs, hexp, ENNReal.rpow_one,
      mul_assoc] using hroot
  have hliminfBound :
      Filter.liminf (fun n => high n) atTop ≤ rhsLim ^ (1 / 6 : ℝ) := by
    calc
      Filter.liminf (fun n => high n) atTop ≤
          Filter.liminf (fun n => rhs n ^ (1 / 6 : ℝ)) atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hrootBound)
      _ = rhsLim ^ (1 / 6 : ℝ) := hRootTendsto.liminf_eq
  have hFatou : eLpNorm u.toFun 6 volume ≤ Filter.liminf high atTop :=
    Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun n => (hψCont (σ n)).aestronglyMeasurable)
      u.toFun huMem.aestronglyMeasurable hσae
  have hnormRoot : eLpNorm u.toFun 6 volume ≤ rhsLim ^ (1 / 6 : ℝ) :=
    hFatou.trans hliminfBound
  have hpowered := ENNReal.rpow_le_rpow hnormRoot
    (by norm_num : 0 ≤ (6 : ℝ))
  rw [← ENNReal.rpow_mul] at hpowered
  have hexp : (1 / 6 : ℝ) * 6 = 1 := by norm_num
  simpa only [ENNReal.rpow_natCast, hexp, ENNReal.rpow_one,
    rhsLim, mul_assoc] using hpowered

/-- In dimension two, the whole-space `H¹` Gagliardo--Nirenberg inequality
in integral-energy form. -/
theorem h1_two_dimensional_gagliardo_nirenberg_energy
    (u : H1Function (Set.univ : Set (Vec 2))) :
    (eLpNorm u.toFun 4 volume) ^ (4 : ℝ) ≤
      (ENNReal.ofReal (4 * (sobolevOneConstant 2 : ℝ))) ^ (2 : ℝ) *
        (eLpNorm u.toFun 2 volume) ^ (2 : ℝ) *
          (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 volume) ^ (2 : ℝ) := by
  have h := h1_two_dimensional_gagliardo_nirenberg u
  have hpow := ENNReal.rpow_le_rpow h (by norm_num : 0 ≤ (2 : ℝ))
  rw [← ENNReal.rpow_mul] at hpow
  have hmul := ENNReal.mul_rpow_of_nonneg
    (ENNReal.ofReal (4 * (sobolevOneConstant 2 : ℝ)) *
      eLpNorm u.toFun 2 volume)
    (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 volume)
    (by norm_num : 0 ≤ (2 : ℝ))
  rw [ENNReal.mul_rpow_of_nonneg
    (ENNReal.ofReal (4 * (sobolevOneConstant 2 : ℝ)))
    (eLpNorm u.toFun 2 volume) (by norm_num : 0 ≤ (2 : ℝ))] at hmul
  have hexp : (2 : ℝ) * 2 = 4 := by norm_num
  rw [hexp, hmul] at hpow
  exact hpow

end PDE.Parabolic
