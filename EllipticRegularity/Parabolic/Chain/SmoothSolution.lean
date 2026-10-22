/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.Chain.Integral
public import EllipticRegularity.Parabolic.WeakSlice.Product
public import Mathlib.Topology.Algebra.Support

/-! # Nonlinear testing identity for classical weak solutions -/

@[expose] public section

namespace PDE.Parabolic.Chain

open MeasureTheory Set PDE

/-- The renormalized weak-form integrand for a scalar function `F(u)`. -/
noncomputable def renormalizedIntegrand {d : ℕ} {U : Set (Vec d)} {I : Set ℝ}
    (a : ParCoeffField d) (u : ParH1Function U I) (F : ℝ → ℝ)
    (φ : Vec d × ℝ → ℝ) (z : Vec d × ℝ) : ℝ :=
  -(F (u.toFun z) * parTimeDeriv φ z) +
    deriv F (u.toFun z) *
      vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad φ z) +
    deriv (deriv F) (u.toFun z) *
      vecDot (matVecMul (a z) (u.grad z)) (u.grad z) * φ z

/-- Dot product distributes over addition in its second argument. -/
theorem vecDot_add_right {d : ℕ} (x y z : Vec d) :
    vecDot x (y + z) = vecDot x y + vecDot x z := by
  simp only [vecDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- Dot product pulls a scalar out of its second argument. -/
theorem vecDot_smul_right {d : ℕ} (x y : Vec d) (c : ℝ) :
    vecDot x (c • y) = c * vecDot x y := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Pointwise algebra behind the nonlinear test identity. -/
theorem weakIntegrand_chain_decomposition {d : ℕ} {U : Set (Vec d)} {I : Set ℝ}
    (a : ParCoeffField d) (u : ParH1Function U I) (F : ℝ → ℝ)
    (hF : ContDiff ℝ 2 F) (hw : ContDiff ℝ 2 u.toFun)
    (hgrad : ∀ z ∈ U ×ˢ I, parSpaceGrad u.toFun z = u.grad z)
    (φ : Vec d × ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (z : Vec d × ℝ)
    (hz : z ∈ U ×ˢ I) :
    parWeakIntegrand a u (fun y => deriv F (u.toFun y) * φ y) z =
      renormalizedIntegrand a u F φ z +
        parTimeDeriv (fun y => renormalizationRemainder F (u.toFun y) * φ y) z := by
  have hw1 : ContDiff ℝ 1 u.toFun := hw.of_le (by norm_num)
  have hF1 : ContDiff ℝ 1 (deriv F) := contDiff_deriv_of_two hF
  have hR : ContDiff ℝ 1 (renormalizationRemainder F) := by
    change ContDiff ℝ 1 (F - fun s => s * deriv F s)
    exact (hF.of_le (by norm_num)).sub (contDiff_id.mul hF1)
  have hψt : parTimeDeriv (fun y => deriv F (u.toFun y) * φ y) z =
      deriv (deriv F) (u.toFun z) * parTimeDeriv u.toFun z * φ z +
        deriv F (u.toFun z) * parTimeDeriv φ z := by
    have hm := parTimeDeriv_mul (hF1.comp hw1) hφ z
    rw [parTimeDeriv_comp hF1 hw1] at hm
    simpa only [Function.comp_apply] using hm
  have hψx : parSpaceGrad (fun y => deriv F (u.toFun y) * φ y) z =
      φ z • (deriv (deriv F) (u.toFun z) • parSpaceGrad u.toFun z) +
        deriv F (u.toFun z) • parSpaceGrad φ z := by
    have hm := parSpaceGrad_mul (hF1.comp hw1) hφ z
    rw [parSpaceGrad_comp hF1 hw1] at hm
    simpa only [Function.comp_apply] using hm
  rw [hgrad z hz] at hψx
  have hRt : parTimeDeriv
      (fun y => renormalizationRemainder F (u.toFun y) * φ y) z =
      (-u.toFun z * deriv (deriv F) (u.toFun z)) * parTimeDeriv u.toFun z * φ z +
        renormalizationRemainder F (u.toFun z) * parTimeDeriv φ z := by
    have hm := parTimeDeriv_mul (hR.comp hw1) hφ z
    rw [parTimeDeriv_comp hR hw1, deriv_renormalizationRemainder hF] at hm
    simpa only [Function.comp_apply] using hm
  unfold parWeakIntegrand renormalizedIntegrand
  rw [hψt, hψx, hRt, smul_smul, vecDot_add_right, vecDot_smul_right, vecDot_smul_right]
  simp only [renormalizationRemainder]
  ring

/-- For a classical `C²` solution, nonlinear testing gives the exact
renormalized weak identity. The solution and its stored spatial gradient must
agree classically on the cylinder. -/
theorem smooth_solution_renormalization {d : ℕ} {U : Set (Vec d)} {I : Set ℝ}
    (hU : IsOpen U) (hI : I.OrdConnected) (a : ParCoeffField d) (u : ParH1Function U I)
    (hu : IsParabolicWeakSolution a U I u)
    (hw : ContDiff ℝ 2 u.toFun)
    (hgrad : ∀ z ∈ U ×ˢ I, parSpaceGrad u.toFun z = u.grad z)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (φ : ParTestFunction U (interior I)) :
    IntegrableOn (renormalizedIntegrand a u F φ.toFun) (U ×ˢ I) ∧
      ∫ z in U ×ˢ I, renormalizedIntegrand a u F φ.toFun z = 0 := by
  have hw1 : ContDiff ℝ 1 u.toFun := hw.of_le (by norm_num)
  have hF1 : ContDiff ℝ 1 (deriv F) := contDiff_deriv_of_two hF
  have hR : ContDiff ℝ 1 (renormalizationRemainder F) := by
    change ContDiff ℝ 1 (F - fun s => s * deriv F s)
    exact (hF.of_le (by norm_num)).sub (contDiff_id.mul hF1)
  let ψ : ParTestFunction U (interior I) :=
    { toFun := fun z => deriv F (u.toFun z) * φ.toFun z
      contDiff := (hF1.comp hw1).mul φ.contDiff
      hasCompactSupport := φ.hasCompactSupport.mul_left
      tsupport_subset := (tsupport_mul_subset_right).trans φ.tsupport_subset }
  let c : Vec d × ℝ → ℝ :=
    fun z => renormalizationRemainder F (u.toFun z) * φ.toFun z
  have hcC : ContDiff ℝ 1 c := (hR.comp hw1).mul φ.contDiff
  have hcK : HasCompactSupport c := φ.hasCompactSupport.mul_left
  have hcSupport : tsupport c ⊆ U ×ˢ interior I :=
    (tsupport_mul_subset_right).trans φ.tsupport_subset
  obtain ⟨hW, hWzero⟩ := hu ψ
  have hcGlobal : Integrable (parTimeDeriv c) volume := integrable_parTimeDeriv c hcC hcK
  have hcZero : ∫ z in U ×ˢ I, parTimeDeriv c z = 0 := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact integral_parTimeDeriv_eq_zero c hcC hcK
    · intro z hz
      have hzC : z ∉ tsupport c := by
        intro hcz
        have hmem := hcSupport hcz
        exact hz ⟨hmem.1, (interior_subset hmem.2)⟩
      have hzfd : z ∉ tsupport (fderiv ℝ c) := fun h =>
        hzC (tsupport_fderiv_subset ℝ h)
      have hfd : fderiv ℝ c z = 0 := image_eq_zero_of_notMem_tsupport hzfd
      simp [parTimeDeriv, hfd]
  have hcInt : IntegrableOn (parTimeDeriv c) (U ×ˢ I) := hcGlobal.integrableOn
  have hmeas : MeasurableSet (U ×ˢ I) := hU.measurableSet.prod hI.measurableSet
  have hT : IntegrableOn (renormalizedIntegrand a u F φ.toFun) (U ×ˢ I) := by
    refine (hW.sub hcInt).congr ?_
    filter_upwards [ae_restrict_mem hmeas] with z hz
    have hdec := weakIntegrand_chain_decomposition a u F hF hw hgrad φ.toFun
      φ.contDiff z hz
    simpa [ψ, c] using congrArg (fun q => q - parTimeDeriv c z) hdec
  have hEq :
      ∫ z in U ×ˢ I, renormalizedIntegrand a u F φ.toFun z =
        (∫ z in U ×ˢ I, parWeakIntegrand a u ψ.toFun z) -
          ∫ z in U ×ˢ I, parTimeDeriv c z := by
    rw [← integral_sub hW hcInt]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem hmeas] with z hz
    have hdec := weakIntegrand_chain_decomposition a u F hF hw hgrad φ.toFun
      φ.contDiff z hz
    change renormalizedIntegrand a u F φ.toFun z =
      parWeakIntegrand a u (fun y => deriv F (u.toFun y) * φ.toFun y) z -
        parTimeDeriv (fun y => renormalizationRemainder F (u.toFun y) * φ.toFun y) z
    rw [hdec]
    ring
  rw [hWzero, hcZero] at hEq
  exact ⟨hT, by simpa using hEq⟩


/-- For a classical weak supersolution, a nonnegative test multiplied by a
nonnegative `F'` gives the renormalized supersolution inequality. The sign is
`0 ≤ ∫` because `IsParabolicWeakSupersolution` uses that convention. -/
theorem smooth_supersolution_renormalization {d : ℕ} {U : Set (Vec d)} {I : Set ℝ}
    (hU : IsOpen U) (hI : I.OrdConnected) (a : ParCoeffField d) (u : ParH1Function U I)
    (hu : IsParabolicWeakSupersolution a U I u)
    (hw : ContDiff ℝ 2 u.toFun)
    (hgrad : ∀ z ∈ U ×ˢ I, parSpaceGrad u.toFun z = u.grad z)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hFmono : ∀ s, 0 ≤ deriv F s)
    (φ : ParTestFunction U (interior I))
    (hφnonneg : ∀ z, 0 ≤ φ.toFun z) :
    IntegrableOn (renormalizedIntegrand a u F φ.toFun) (U ×ˢ I) ∧
      0 ≤ ∫ z in U ×ˢ I, renormalizedIntegrand a u F φ.toFun z := by
  have hw1 : ContDiff ℝ 1 u.toFun := hw.of_le (by norm_num)
  have hF1 : ContDiff ℝ 1 (deriv F) := contDiff_deriv_of_two hF
  have hR : ContDiff ℝ 1 (renormalizationRemainder F) := by
    change ContDiff ℝ 1 (F - fun s => s * deriv F s)
    exact (hF.of_le (by norm_num)).sub (contDiff_id.mul hF1)
  let ψ : ParTestFunction U (interior I) :=
    { toFun := fun z => deriv F (u.toFun z) * φ.toFun z
      contDiff := (hF1.comp hw1).mul φ.contDiff
      hasCompactSupport := φ.hasCompactSupport.mul_left
      tsupport_subset := (tsupport_mul_subset_right).trans φ.tsupport_subset }
  have hψnonneg : ∀ z, 0 ≤ ψ.toFun z := by
    intro z
    simp only [ψ]
    exact mul_nonneg (hFmono (u.toFun z)) (hφnonneg z)
  let c : Vec d × ℝ → ℝ :=
    fun z => renormalizationRemainder F (u.toFun z) * φ.toFun z
  have hcC : ContDiff ℝ 1 c := (hR.comp hw1).mul φ.contDiff
  have hcK : HasCompactSupport c := φ.hasCompactSupport.mul_left
  have hcSupport : tsupport c ⊆ U ×ˢ interior I :=
    (tsupport_mul_subset_right).trans φ.tsupport_subset
  obtain ⟨hW, hWnonneg⟩ := hu ψ hψnonneg
  have hcGlobal : Integrable (parTimeDeriv c) volume := integrable_parTimeDeriv c hcC hcK
  have hcZero : ∫ z in U ×ˢ I, parTimeDeriv c z = 0 := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact integral_parTimeDeriv_eq_zero c hcC hcK
    · intro z hz
      have hzC : z ∉ tsupport c := by
        intro hcz
        have hmem := hcSupport hcz
        exact hz ⟨hmem.1, (interior_subset hmem.2)⟩
      have hzfd : z ∉ tsupport (fderiv ℝ c) := fun h =>
        hzC (tsupport_fderiv_subset ℝ h)
      have hfd : fderiv ℝ c z = 0 := image_eq_zero_of_notMem_tsupport hzfd
      simp [parTimeDeriv, hfd]
  have hcInt : IntegrableOn (parTimeDeriv c) (U ×ˢ I) := hcGlobal.integrableOn
  have hmeas : MeasurableSet (U ×ˢ I) := hU.measurableSet.prod hI.measurableSet
  have hT : IntegrableOn (renormalizedIntegrand a u F φ.toFun) (U ×ˢ I) := by
    refine (hW.sub hcInt).congr ?_
    filter_upwards [ae_restrict_mem hmeas] with z hz
    have hdec := weakIntegrand_chain_decomposition a u F hF hw hgrad φ.toFun
      φ.contDiff z hz
    change parWeakIntegrand a u (fun y => deriv F (u.toFun y) * φ.toFun y) z -
      parTimeDeriv (fun y => renormalizationRemainder F (u.toFun y) * φ.toFun y) z =
        renormalizedIntegrand a u F φ.toFun z
    rw [hdec]
    ring
  have hEq :
      ∫ z in U ×ˢ I, renormalizedIntegrand a u F φ.toFun z =
        (∫ z in U ×ˢ I, parWeakIntegrand a u ψ.toFun z) -
          ∫ z in U ×ˢ I, parTimeDeriv c z := by
    rw [← integral_sub hW hcInt]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem hmeas] with z hz
    have hdec := weakIntegrand_chain_decomposition a u F hF hw hgrad φ.toFun
      φ.contDiff z hz
    change renormalizedIntegrand a u F φ.toFun z =
      parWeakIntegrand a u (fun y => deriv F (u.toFun y) * φ.toFun y) z -
        parTimeDeriv (fun y => renormalizationRemainder F (u.toFun y) * φ.toFun y) z
    rw [hdec]
    ring
  rw [hcZero] at hEq
  refine ⟨hT, ?_⟩
  rw [hEq]
  simpa using hWnonneg


/-- Antitone nonlinearities reverse the renormalized supersolution sign. This
covers decreasing powers when their scalar function is extended smoothly to a
nonincreasing `C²` function on `ℝ`. -/
theorem smooth_supersolution_renormalization_antitone
    {d : ℕ} {U : Set (Vec d)} {I : Set ℝ}
    (hU : IsOpen U) (hI : I.OrdConnected) (a : ParCoeffField d) (u : ParH1Function U I)
    (hu : IsParabolicWeakSupersolution a U I u)
    (hw : ContDiff ℝ 2 u.toFun)
    (hgrad : ∀ z ∈ U ×ˢ I, parSpaceGrad u.toFun z = u.grad z)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hFantitone : ∀ s, deriv F s ≤ 0)
    (φ : ParTestFunction U (interior I))
    (hφnonneg : ∀ z, 0 ≤ φ.toFun z) :
    IntegrableOn (renormalizedIntegrand a u F φ.toFun) (U ×ˢ I) ∧
      ∫ z in U ×ˢ I, renormalizedIntegrand a u F φ.toFun z ≤ 0 := by
  have hnegDeriv (G : ℝ → ℝ) (s : ℝ) : deriv (-G) s = -deriv G s := by
    calc
      deriv (-G) s = (fderiv ℝ (-G) s) 1 := fderiv_apply_one_eq_deriv.symm
      _ = -(fderiv ℝ G s 1) := by rw [fderiv_neg]; simp
      _ = -deriv G s := by rw [fderiv_apply_one_eq_deriv]
  have hfirst : deriv (-F) = fun s => -deriv F s := by
    funext s
    exact hnegDeriv F s
  have hsecond : deriv (deriv (-F)) = fun s => -deriv (deriv F) s := by
    calc
      deriv (deriv (-F)) = deriv (-deriv F) := congrArg deriv hfirst
      _ = fun s => -deriv (deriv F) s := by
        funext s
        exact hnegDeriv (deriv F) s
  have hnegmono : ∀ s, 0 ≤ deriv (-F) s := by
    intro s
    rw [hnegDeriv]
    exact neg_nonneg.mpr (hFantitone s)
  have hneg := smooth_supersolution_renormalization hU hI a u hu hw hgrad (-F)
    hF.neg hnegmono φ hφnonneg
  have hform : renormalizedIntegrand a u (-F) φ.toFun =
      fun z => -renormalizedIntegrand a u F φ.toFun z := by
    funext z
    simp only [renormalizedIntegrand]
    rw [hsecond, hfirst]
    simp only [Pi.neg_apply]
    ring
  have hmeas : MeasurableSet (U ×ˢ I) := hU.measurableSet.prod hI.measurableSet
  have hminus : IntegrableOn (fun z => -renormalizedIntegrand a u F φ.toFun z) (U ×ˢ I) := by
    refine hneg.1.congr ?_
    filter_upwards [ae_restrict_mem hmeas] with z hz
    exact congrFun hform z
  have hT : IntegrableOn (renormalizedIntegrand a u F φ.toFun) (U ×ˢ I) := by
    refine hminus.neg.congr ?_
    filter_upwards [ae_restrict_mem hmeas] with z hz
    simp
  have hsign : 0 ≤ ∫ z in U ×ˢ I, -renormalizedIntegrand a u F φ.toFun z := by
    simpa only [hform] using hneg.2
  rw [integral_neg] at hsign
  exact ⟨hT, by linarith⟩

end PDE.Parabolic.Chain
