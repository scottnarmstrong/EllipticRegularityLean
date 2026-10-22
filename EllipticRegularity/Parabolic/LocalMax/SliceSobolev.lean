module

public import EllipticRegularity.Parabolic.Sobolev.ParabolicSlices
public import PDEFoundation.Sobolev.Ch4.ChainRule
public import PDEFoundation.Sobolev.WeakDerivative.Product
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Order.CompletePartialOrder

/-!
# Parabolic Sobolev step for cutoff compositions `η G(u)`

For a parabolic energy function `u` on `U × I`, a `C¹` function `G` with bounded derivative and a
smooth space-time cutoff `η` whose spatial support lies in a fixed compact subset of `U`, almost
every slice `η(·,t) G(u(·,t))` is (after zero extension) an `H¹(ℝᵈ)` function with gradient
`G'(u) η ∇u + G(u) ∇η`.  The spatial Gagliardo--Nirenberg inequality, integrated in time, gives

`∫∫ |η G(u)|^{2(d+2)/d} ≤ C(d) S^{2/d} D`,

where `S` bounds the slice energies `∫ (η G(u))²(t)` for almost every `t` and `D` bounds the
space-time integral of the squared gradient.  This is the Sobolev half of the Moser power step.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.LocalMax

open MeasureTheory Set

variable {d : ℕ}

/-- The spatial derivative of a slice of a differentiable space-time function. -/
theorem fderiv_slice_apply {η : Vec d × ℝ → ℝ} (hη : Differentiable ℝ η) (x : Vec d) (t : ℝ)
    (v : Vec d) : fderiv ℝ (fun y => η (y, t)) x v = fderiv ℝ η (x, t) (v, 0) := by
  have h1 : HasFDerivAt (fun y : Vec d => (y, t))
      ((ContinuousLinearMap.id ℝ (Vec d)).prod 0) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
  have h2 : HasFDerivAt (fun y : Vec d => η (y, t))
      ((fderiv ℝ η (x, t)).comp ((ContinuousLinearMap.id ℝ (Vec d)).prod 0)) x :=
    (hη (x, t)).hasFDerivAt.comp x h1
  rw [h2.fderiv]
  simp

/-- A continuous function vanishing off a compact set is bounded. -/
theorem exists_abs_le_of_continuous_of_eq_zero_off {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} (hf : Continuous f) {K : Set X} (hK : IsCompact K)
    (hf0 : ∀ x, x ∉ K → f x = 0) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |f x| ≤ B := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ K
  · exact (by simpa [Real.norm_eq_abs] using hB x hx : |f x| ≤ B).trans (le_max_left _ _)
  · simp [hf0 x hx]

section SliceH1

variable {U : Set (Vec d)}

/-- `ζ G(v)` for `v ∈ H¹(U)`, `G ∈ C¹` with bounded derivative and a smooth bounded `ζ` with
bounded derivative, as an element of `H¹(U)`. -/
noncomputable def cutoffCompH1 (hU : IsOpen U) (hfin : volume U ≠ ⊤) (v : H1Function U)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) {M : ℝ} (hM : 0 ≤ M) (hGM : ∀ s, |deriv G s| ≤ M)
    {ζ : Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) {B : ℝ} (hB : 0 ≤ B)
    (hζB : ∀ x, |ζ x| ≤ B) (hdζB : ∀ x i, |fderiv ℝ ζ x (basisVec i)| ≤ B) :
    H1Function U :=
  let w := Ch4Infra.compOpen hU hfin v hG hM hGM
  have hζc : Continuous ζ := hζ.continuous
  have hdζc : ∀ i : Fin d, Continuous fun x => fderiv ℝ ζ x (basisVec i) := fun i =>
    ((hζ.continuous_fderiv (by simp)).clm_apply continuous_const)
  { toFun := fun x => ζ x * w.toFun x
    grad := fun x i => ζ x * w.grad x i + w.toFun x * fderiv ℝ ζ x (basisVec i)
    memL2 := by
      refine (w.memL2.const_mul B).mono
        (hζc.aestronglyMeasurable.mul w.memL2.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => ?_)
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hB]
      exact mul_le_mul_of_nonneg_right (hζB x) (abs_nonneg _)
    gradMemL2 := by
      intro i
      have h1 : MemLp (fun x => ζ x * w.grad x i) 2 (volumeOn U) := by
        refine ((w.gradMemL2 i).const_mul B).mono
          (hζc.aestronglyMeasurable.mul (w.gradMemL2 i).aestronglyMeasurable)
          (Filter.Eventually.of_forall fun x => ?_)
        simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hB]
        exact mul_le_mul_of_nonneg_right (hζB x) (abs_nonneg _)
      have h2 : MemLp (fun x => w.toFun x * fderiv ℝ ζ x (basisVec i)) 2 (volumeOn U) := by
        refine (w.memL2.mul_const B).mono
          (w.memL2.aestronglyMeasurable.mul (hdζc i).aestronglyMeasurable)
          (Filter.Eventually.of_forall fun x => ?_)
        simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hB]
        exact mul_le_mul_of_nonneg_left (hdζB x i) (abs_nonneg _)
      exact h1.add h2
    hasWeakGradient := by
      have hwLoc : LocallyIntegrable w.toFun (volumeOn U) :=
        w.memL2.locallyIntegrable (by norm_num)
      have hgLoc : ∀ i : Fin d, LocallyIntegrable (fun x => w.grad x i) (volumeOn U) :=
        fun i => (w.gradMemL2 i).locallyIntegrable (by norm_num)
      exact HasWeakGradientOn.mul_contDiff w.hasWeakGradient hζ hwLoc hgLoc }

/-- Zero extension to the whole space of an `H¹(U)` function vanishing off a compact `K ⊆ U`. -/
noncomputable def zeroExtendH1 (hU : IsOpen U) (f : H1Function U) {K : Set (Vec d)}
    (hK : IsCompact K) (hKU : K ⊆ U) (hf0 : ∀ x ∈ U, x ∉ K → f.toFun x = 0) :
    H1Function (Set.univ : Set (Vec d)) where
  toFun := U.indicator f.toFun
  grad := U.indicator f.grad
  memL2 := by
    simpa only [MemL2On, MemLpOn, volumeOn, Measure.restrict_univ] using
      (memLp_indicator_iff_restrict (μ := volume) hU.measurableSet).2 f.memL2
  gradMemL2 := by
    intro i
    rw [show (fun x => U.indicator f.grad x i) = U.indicator (fun x => f.grad x i) by
      funext x
      by_cases hx : x ∈ U <;> simp [hx]]
    simpa only [GradMemL2On, GradMemLpOn, MemLpOn, volumeOn, Measure.restrict_univ] using
      (memLp_indicator_iff_restrict (μ := volume) hU.measurableSet).2 (f.gradMemL2 i)
  hasWeakGradient := by
    intro i
    have hzero := Ch4Infra.hasWeakPartialDerivOn_univ_zeroExtend hU f hKU hK hf0 i
    convert hzero using 1
    funext x
    by_cases hx : x ∈ U <;> simp [hx]

end SliceH1

section Conversions

theorem enorm_sq_eq_ofReal (r : ℝ) : ‖r‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (r ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg r), sq_abs]

theorem enorm_vecEuclideanNorm_sq (g : Vec d) :
    ‖vecEuclideanNorm g‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (vecNormSq g) := by
  rw [enorm_sq_eq_ofReal, vecEuclideanNorm_sq]

/-- The integrand of the gradient energy of `η G(u)`. -/
noncomputable def cutoffCompGrad {U : Set (Vec d)} {I : Set ℝ} (u : ParH1Function U I)
    (G : ℝ → ℝ) (η : Vec d × ℝ → ℝ) (z : Vec d × ℝ) : Vec d :=
  (deriv G (u.toFun z) * η z) • u.grad z + G (u.toFun z) • parSpaceGrad η z

end Conversions

/-- **Parabolic Sobolev step for `η G(u)`.**  The constant depends only on the dimension. -/
theorem slice_cutoff_comp_gagliardo_nirenberg (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ {U : Set (Vec d)} {I J : Set ℝ}, IsOpen U → volume U ≠ ⊤ →
      MeasurableSet J → J ⊆ I → ∀ (u : ParH1Function U I) (G : ℝ → ℝ), ContDiff ℝ 1 G →
      ∀ M : ℝ, 0 ≤ M → (∀ s, |deriv G s| ≤ M) →
      ∀ η : Vec d × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → ∀ Kx : Set (Vec d), IsCompact Kx →
      Kx ⊆ U → (∀ x t, x ∉ Kx → η (x, t) = 0) → ∀ S D : ℝ≥0∞,
      (∀ᵐ t ∂(volume.restrict J),
        ∫⁻ x in U, ENNReal.ofReal ((η (x, t) * G (u.toFun (x, t))) ^ 2) ≤ S) →
      ∫⁻ z in U ×ˢ J, ENNReal.ofReal (vecNormSq (cutoffCompGrad u G η z)) ≤ D →
      ∫⁻ z in U ×ˢ J, ENNReal.ofReal |η z * G (u.toFun z)| ^ (2 * ((d : ℝ) + 2) / d) ≤
        C * S ^ (2 / (d : ℝ)) * D := by
  have hd1 : 1 ≤ d := hd
  obtain ⟨C, hC, hGN⟩ := exists_spatial_gagliardo_nirenberg_energy_constant d hd1
  refine ⟨C, hC, ?_⟩
  intro U I J hU hfin hJ hJI u G hG M hM hGM η hη Kx hKx hKxU hηx S D hS hD
  set q : ℝ := 2 * ((d : ℝ) + 2) / d with hq_def
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hq : 0 < q := by positivity
  have hμ : volume.restrict (U ×ˢ J) ≤ volume.restrict (U ×ˢ I) :=
    Measure.restrict_mono (prod_mono subset_rfl hJI) le_rfl
  have huM : AEStronglyMeasurable u.toFun (volume.restrict (U ×ˢ J)) :=
    u.memL2.aestronglyMeasurable.mono_measure hμ
  have hgM : ∀ i : Fin d, AEStronglyMeasurable (fun z => u.grad z i) (volume.restrict (U ×ˢ J)) :=
    fun i => (u.gradMemL2 i).aestronglyMeasurable.mono_measure hμ
  have hηc : Continuous η := hη.continuous
  have hηd : Differentiable ℝ η := hη.differentiable (by simp)
  have hdη : ∀ i : Fin d, Continuous fun z => parSpaceGrad η z i := fun i =>
    (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hG'c : Continuous (deriv G) := hG.continuous_deriv le_rfl
  have hGu : AEStronglyMeasurable (fun z => G (u.toFun z)) (volume.restrict (U ×ˢ J)) :=
    hG.continuous.comp_aestronglyMeasurable huM
  have hfM : AEStronglyMeasurable (fun z => η z * G (u.toFun z)) (volume.restrict (U ×ˢ J)) :=
    hηc.aestronglyMeasurable.mul hGu
  have hgradM : AEMeasurable (cutoffCompGrad u G η) (volume.restrict (U ×ˢ J)) := by
    refine aemeasurable_pi_iff.2 fun i => ?_
    have h1 : AEStronglyMeasurable (fun z => deriv G (u.toFun z) * η z * u.grad z i +
        G (u.toFun z) * parSpaceGrad η z i) (volume.restrict (U ×ˢ J)) :=
      (((hG'c.comp_aestronglyMeasurable huM).mul hηc.aestronglyMeasurable).mul (hgM i)).add
        (hGu.mul (hdη i).aestronglyMeasurable)
    refine h1.aemeasurable.congr (Filter.Eventually.of_forall fun z => ?_)
    simp [cutoffCompGrad, smul_eq_mul]
  -- slice functions
  let A : ℝ → ℝ≥0∞ := fun t =>
    ∫⁻ x in U, ENNReal.ofReal |η (x, t) * G (u.toFun (x, t))| ^ q
  let B : ℝ → ℝ≥0∞ := fun t =>
    ∫⁻ x in U, ENNReal.ofReal ((η (x, t) * G (u.toFun (x, t))) ^ 2)
  let Dt : ℝ → ℝ≥0∞ := fun t =>
    ∫⁻ x in U, ENNReal.ofReal (vecNormSq (cutoffCompGrad u G η (x, t)))
  have hAM : AEMeasurable (fun z => ENNReal.ofReal |η z * G (u.toFun z)| ^ q)
      ((volume.restrict U).prod (volume.restrict J)) := by
    rw [← Energy.volume_restrict_prod]
    exact (ENNReal.measurable_ofReal.comp_aemeasurable hfM.aemeasurable.abs).pow_const q
  have hDM : AEMeasurable (fun z => ENNReal.ofReal (vecNormSq (cutoffCompGrad u G η z)))
      ((volume.restrict U).prod (volume.restrict J)) := by
    rw [← Energy.volume_restrict_prod]
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (continuous_vecNormSq.measurable.comp_aemeasurable hgradM)
  have hLHS : ∫⁻ z in U ×ˢ J, ENNReal.ofReal |η z * G (u.toFun z)| ^ q =
      ∫⁻ t in J, A t := by
    rw [Energy.volume_restrict_prod, lintegral_prod_symm _ hAM]
  have hDeq : ∫⁻ z in U ×ˢ J, ENNReal.ofReal (vecNormSq (cutoffCompGrad u G η z)) =
      ∫⁻ t in J, Dt t := by
    rw [Energy.volume_restrict_prod, lintegral_prod_symm _ hDM]
  have hDtM : AEMeasurable Dt (volume.restrict J) := hDM.lintegral_prod_left'
  -- the slice estimate
  have hslices : ∀ᵐ t ∂(volume.restrict J), A t ≤ C * B t ^ (2 / (d : ℝ)) * Dt t := by
    have hae : ∀ᵐ t ∂(volume.restrict J), ∃ v : H1Function U,
        v.toFun = parSlice u.toFun t ∧ v.grad = parSlice u.grad t :=
      ae_mono (Measure.restrict_mono hJI le_rfl) (ae_parH1_slice_h1 hU u)
    filter_upwards [hae] with t ht
    obtain ⟨v, hv, hvg⟩ := ht
    set ζ : Vec d → ℝ := fun x => η (x, t) with hζ_def
    have hζ : ContDiff ℝ (⊤ : ℕ∞) ζ := hη.comp (contDiff_id.prodMk contDiff_const)
    have hζ0 : ∀ x, x ∉ Kx → ζ x = 0 := fun x hx => hηx x t hx
    have hdζ0 : ∀ i : Fin d, ∀ x, x ∉ Kx → fderiv ℝ ζ x (basisVec i) = 0 := by
      intro i x hx
      have hloc : ζ =ᶠ[nhds x] fun _ => (0 : ℝ) :=
        Filter.eventually_of_mem (hKx.isClosed.isOpen_compl.mem_nhds hx) fun y hy => hζ0 y hy
      rw [hloc.fderiv_eq]
      simp
    obtain ⟨B0, hB0, hB0b⟩ :=
      exists_abs_le_of_continuous_of_eq_zero_off hζ.continuous hKx hζ0
    have hbi : ∀ i : Fin d, ∃ Bi : ℝ, 0 ≤ Bi ∧ ∀ x, |fderiv ℝ ζ x (basisVec i)| ≤ Bi := fun i =>
      exists_abs_le_of_continuous_of_eq_zero_off
        ((hζ.continuous_fderiv (by simp)).clm_apply continuous_const) hKx (hdζ0 i)
    choose Bi hBi0 hBib using hbi
    set Bt : ℝ := B0 + ∑ i, Bi i with hBt
    have hsum0 : 0 ≤ ∑ i, Bi i := Finset.sum_nonneg fun i _ => hBi0 i
    have hBt0 : 0 ≤ Bt := add_nonneg hB0 hsum0
    have hζB : ∀ x, |ζ x| ≤ Bt := fun x => (hB0b x).trans (le_add_of_nonneg_right hsum0)
    have hdζB : ∀ x i, |fderiv ℝ ζ x (basisVec i)| ≤ Bt := fun x i =>
      (hBib i x).trans ((Finset.single_le_sum (fun j _ => hBi0 j) (Finset.mem_univ i)).trans
        (le_add_of_nonneg_left hB0))
    let w := cutoffCompH1 hU hfin v hG hM hGM hζ hBt0 hζB hdζB
    have hw : ∀ x, w.toFun x = η (x, t) * G (u.toFun (x, t)) := by
      intro x
      simp [w, cutoffCompH1, Ch4Infra.compOpen, hv, ζ, parSlice]
    have hwg : ∀ x, w.grad x = cutoffCompGrad u G η (x, t) := by
      intro x
      funext i
      simp only [w, cutoffCompH1, Ch4Infra.compOpen, hv, hvg, cutoffCompGrad, parSlice,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, parSpaceGrad, ζ]
      rw [fderiv_slice_apply hηd]
      ring
    have hw0 : ∀ x ∈ U, x ∉ Kx → w.toFun x = 0 := by
      intro x _ hx
      rw [hw x, hηx x t hx, zero_mul]
    let W := zeroExtendH1 hU w hKx hKxU hw0
    have hGNt := hGN W
    have hWf : W.toFun = U.indicator w.toFun := rfl
    have hWg : (fun x => vecEuclideanNorm (W.grad x)) =
        U.indicator (fun x => vecEuclideanNorm (w.grad x)) := by
      funext x
      by_cases hx : x ∈ U <;>
        simp [W, zeroExtendH1, hx, PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot]
    rw [hWf, hWg] at hGNt
    simp only [eLpNorm_indicator_eq_eLpNorm_restrict hU.measurableSet] at hGNt
    have hwM : AEStronglyMeasurable w.toFun (volume.restrict U) := w.memL2.aestronglyMeasurable
    have hwgM : AEStronglyMeasurable (fun x => vecEuclideanNorm (w.grad x)) (volume.restrict U) :=
      (GradMemLpOn.memLp_vecEuclideanNorm w.gradMemL2).aestronglyMeasurable
    have h1 : (eLpNorm w.toFun (ENNReal.ofReal q) (volume.restrict U)) ^ q = A t := by
      rw [eLpNorm_rpow_eq_lintegral_enorm_rpow q hq hwM]
      refine lintegral_congr fun x => ?_
      rw [hw x, Real.enorm_eq_ofReal_abs]
    have h2 : (eLpNorm w.toFun 2 (volume.restrict U)) ^ (4 / (d : ℝ)) = B t ^ (2 / (d : ℝ)) := by
      have hB : (eLpNorm w.toFun 2 (volume.restrict U)) ^ (2 : ℝ) = B t := by
        rw [← Energy.lintegral_enorm_sq_eq hwM]
        refine lintegral_congr fun x => ?_
        rw [hw x, enorm_sq_eq_ofReal]
      rw [← hB, ← ENNReal.rpow_mul]
      congr 1
      field_simp
      norm_num
    have h3 : (eLpNorm (fun x => vecEuclideanNorm (w.grad x)) 2 (volume.restrict U)) ^ (2 : ℝ) =
        Dt t := by
      rw [← Energy.lintegral_enorm_sq_eq hwgM]
      refine lintegral_congr fun x => ?_
      rw [enorm_vecEuclideanNorm_sq, hwg x]
    rw [h1, h2, h3] at hGNt
    exact hGNt
  have hmain := lintegral_le_of_ae_gagliardo_nirenberg_aemeasurable
    (volume.restrict J) d hd1 C S hDtM hS hslices
  calc ∫⁻ z in U ×ˢ J, ENNReal.ofReal |η z * G (u.toFun z)| ^ q
      = ∫⁻ t in J, A t := hLHS
    _ ≤ C * S ^ (2 / (d : ℝ)) * ∫⁻ t in J, Dt t := hmain
    _ ≤ C * S ^ (2 / (d : ℝ)) * D := by
      rw [← hDeq]
      gcongr

end PDE.Parabolic.LocalMax
