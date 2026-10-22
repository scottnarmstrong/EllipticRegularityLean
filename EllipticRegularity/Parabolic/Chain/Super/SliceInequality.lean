/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.Chain.Super.DuBoisReymondLe
public import EllipticRegularity.Parabolic.WeakSlice.Result

/-! # The weak supersolution inequality at every time

The supersolution analogue of `PDE.Parabolic.weak_slice`, for nonnegative spatial test
functions. -/

@[expose] public section

namespace PDE.Parabolic.Chain.Super

open MeasureTheory Set Filter Topology PDE PDE.Parabolic.WeakSlice PDE.Parabolic

/-- The weak supersolution inequality tested against `θ(τ) ζ(x)` with `θ, ζ ≥ 0`,
after Fubini. -/
theorem weak_test_inequality {d : ℕ} {lam Lam : ℝ} {U : Set (Vec d)} (hU : IsOpen U)
    {I : Set ℝ} (hI : I.OrdConnected) {a : ParCoeffField d}
    (ha : IsParabolicCoeff lam Lam a U I) (u : ParH1Function U I)
    (hu : IsParabolicWeakSupersolution a U I u) {ζ : Vec d → ℝ}
    (hζnn : ∀ x, 0 ≤ ζ x) (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ) (hζU : tsupport ζ ⊆ U) {p q : ℝ}
    (hp : p ∈ I) (hq : q ∈ I) {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hθs : tsupport θ ⊆ Ioo p q) (hθnn : ∀ τ, 0 ≤ θ τ) :
    ∫ τ in Ioo p q, slicePairing u ζ τ * deriv θ τ ≤
      ∫ τ in Ioo p q, sliceFlux a u ζ τ * θ τ := by
  set F : Vec d × ℝ → ℝ :=
    fun z => vecDot (matVecMul (a z) (u.grad z)) (spaceGradC1 ζ z.1) with hF
  have hIoo : Ioo p q ⊆ I := fun τ hτ => hI.out hp hq ⟨hτ.1.le, hτ.2.le⟩
  have hIoo' : Ioo p q ⊆ interior I := interior_maximal hIoo isOpen_Ioo
  have hFint := integrableOn_flux_Icc hU hI ha u hζ hζc hζU hp hq
  -- the test function
  let φ : ParTestFunction U (interior I) :=
    { toFun := fun w : Vec d × ℝ => θ w.2 * ζ w.1
      contDiff := contDiff_prod hθ hζ
      hasCompactSupport := hasCompactSupport_prod hθc hζc
      tsupport_subset := tsupport_prod_subset.trans (prod_mono hζU (hθs.trans hIoo')) }
  obtain ⟨hint, hzero⟩ := hu φ (fun z => mul_nonneg (hθnn _) (hζnn _))
  have hφ : ∀ z, parWeakIntegrand a u φ.toFun z
      = -(u.toFun z * (deriv θ z.2 * ζ z.1)) + θ z.2 * F z := by
    intro z
    unfold parWeakIntegrand
    show -(u.toFun z * parTimeDeriv (fun w : Vec d × ℝ => θ w.2 * ζ w.1) z) +
      vecDot (matVecMul (a z) (u.grad z))
        (parSpaceGrad (fun w : Vec d × ℝ => θ w.2 * ζ w.1) z) = _
    rw [parTimeDeriv_prod hθ hζ, parSpaceGrad_prod hθ hζ, vecDot_smul_right']
  have hθbdd : ∃ C, ∀ w : ℝ, ‖θ w‖ ≤ C := hθ.continuous.bounded_above_of_compact_support hθc
  have hFθ : IntegrableOn (fun z : Vec d × ℝ => θ z.2 * F z) (U ×ˢ I) := by
    have h1 : IntegrableOn (fun z : Vec d × ℝ => θ z.2 * F z) (U ×ˢ Icc p q) := by
      obtain ⟨C, hC⟩ := hθbdd
      exact hFint.bdd_mul (f := fun z : Vec d × ℝ => θ z.2) (c := C)
        (hθ.continuous.comp continuous_snd).aestronglyMeasurable
        (Eventually.of_forall fun z => hC z.2)
    refine h1.of_forall_sdiff_eq_zero (hU.measurableSet.prod hI.measurableSet) ?_
    rintro ⟨x, τ⟩ ⟨hz, hn⟩
    have : τ ∉ tsupport θ := fun h' =>
      hn ⟨hz.1, (hθs h').1.le, (hθs h').2.le⟩
    simp [image_eq_zero_of_notMem_tsupport this]
  have hA : IntegrableOn (fun z : Vec d × ℝ => u.toFun z * (deriv θ z.2 * ζ z.1)) (U ×ˢ I) := by
    have : (fun z : Vec d × ℝ => u.toFun z * (deriv θ z.2 * ζ z.1))
        = fun z => θ z.2 * F z - parWeakIntegrand a u φ.toFun z := by
      funext z; rw [hφ z]; ring
    rw [this]; exact hFθ.sub hint
  have heq : ∫ z in U ×ˢ I, u.toFun z * (deriv θ z.2 * ζ z.1)
      ≤ ∫ z in U ×ˢ I, θ z.2 * F z := by
    have h0 := hzero
    simp_rw [hφ] at h0
    have hAn : IntegrableOn (fun z : Vec d × ℝ => -(u.toFun z * (deriv θ z.2 * ζ z.1)))
        (U ×ˢ I) := hA.neg
    rw [integral_add hAn hFθ, integral_neg] at h0
    linarith
  -- Fubini
  obtain ⟨_, hfa⟩ := integral_prod_slices hA
  obtain ⟨_, hfb⟩ := integral_prod_slices hFθ
  rw [hfa, hfb] at heq
  have e1 : ∀ τ, ∫ x in U, u.toFun (x, τ) * (deriv θ τ * ζ x)
      = slicePairing u ζ τ * deriv θ τ := by
    intro τ
    unfold slicePairing
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only; ring
  have e2 : ∀ τ, ∫ x in U, θ τ * F (x, τ) = sliceFlux a u ζ τ * θ τ := by
    intro τ
    unfold sliceFlux
    rw [integral_const_mul, mul_comm]
  simp only [e1, e2] at heq
  have r1 : ∀ f : ℝ → ℝ, (∀ τ, τ ∉ Ioo p q → f τ = 0) →
      ∫ τ in I, f τ = ∫ τ in Ioo p q, f τ := fun f hf =>
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hI.measurableSet hIoo
      fun τ hτ => hf τ hτ.2
  have hz : ∀ τ, τ ∉ Ioo p q → deriv θ τ = 0 := fun τ hτ =>
    image_eq_zero_of_notMem_tsupport (fun h' => hτ (hθs (tsupport_deriv_subset h')))
  have hz' : ∀ τ, τ ∉ Ioo p q → θ τ = 0 := fun τ hτ =>
    image_eq_zero_of_notMem_tsupport (fun h' => hτ (hθs h'))
  rw [r1 _ (fun τ hτ => by rw [hz τ hτ, mul_zero]),
    r1 _ (fun τ hτ => by rw [hz' τ hτ, mul_zero])] at heq
  exact heq

/-- The supersolution slice inequality: for `ζ ≥ 0` in `C¹_c(U)`,
`∫ u(t) ζ - ∫ u(s) ζ ≥ -∫∫_{(s,t]} a∇u·∇ζ`. -/
theorem weak_slice_inequality (d : ℕ) (lam Lam : ℝ) (U : Set (Vec d)) (hU : IsOpen U)
    (I : Set ℝ) (hI : I.OrdConnected) (a : ParCoeffField d)
    (ha : IsParabolicCoeff lam Lam a U I)
    (u : ParH1Function U I) (hu : IsParabolicWeakSupersolution a U I u)
    (ζ : Vec d → ℝ) (hζnn : ∀ x, 0 ≤ ζ x) (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ) (hζU : tsupport ζ ⊆ U)
    (s t : ℝ) (hs : s ∈ I) (ht : t ∈ I) (hst : s < t) :
    IntegrableOn (fun z : Vec d × ℝ => vecDot (matVecMul (a z) (u.grad z)) (spaceGradC1 ζ z.1))
        (U ×ˢ Ioc s t) ∧
      -∫ z in U ×ˢ Ioc s t, vecDot (matVecMul (a z) (u.grad z)) (spaceGradC1 ζ z.1) ≤
        (∫ x in U, u.toFun (x, t) * ζ x) - (∫ x in U, u.toFun (x, s) * ζ x) := by
  have hFint := integrableOn_flux_Icc hU hI ha u hζ hζc hζU hs ht
  have hFIoc : IntegrableOn (fun z : Vec d × ℝ =>
      vecDot (matVecMul (a z) (u.grad z)) (spaceGradC1 ζ z.1)) (U ×ˢ Ioc s t) :=
    hFint.mono_set (prod_mono subset_rfl Ioc_subset_Icc_self)
  refine ⟨hFIoc, ?_⟩
  obtain ⟨hgint, hfub⟩ := integral_prod_slices hFIoc
  obtain ⟨hgIcc, _⟩ := integral_prod_slices hFint
  have hgIoo : IntegrableOn (sliceFlux a u ζ) (Ioo s t) :=
    hgIcc.mono_set Ioo_subset_Icc_self
  -- extend `m` continuously
  have hmc := slicePairing_continuousOn u hζ hζc hζU
  have hSub : Icc s t ⊆ I := hI.out hs ht
  let m' : ℝ → ℝ := fun τ => slicePairing u ζ (projIcc s t hst.le τ)
  have hm' : Continuous m' :=
    (hmc.mono hSub).comp_continuous continuous_projIcc.subtype_val
      (fun τ => (projIcc s t hst.le τ).2)
  have hdbr := dubois_reymond_le hst m' (sliceFlux a u ζ) hm' hgIoo
    (fun θ h1 h2 h3 h4 => by
      have := weak_test_inequality hU hI ha u hu hζnn hζ hζc hζU hs ht h1 h2 h3 h4
      refine le_of_eq_of_le (setIntegral_congr_fun measurableSet_Ioo fun τ hτ => ?_) this
      simp only [m', projIcc_of_mem _ (Ioo_subset_Icc_self hτ)])
  simp only [m', projIcc_left, projIcc_right] at hdbr
  rw [hfub, integral_Ioc_eq_integral_Ioo]
  change -∫ τ in Ioo s t, sliceFlux a u ζ τ ≤ _ - _
  unfold slicePairing at hdbr
  linarith [hdbr]

end PDE.Parabolic.Chain.Super
