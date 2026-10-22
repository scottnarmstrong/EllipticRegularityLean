module

public import EllipticRegularity.Parabolic.Cauchy.Lions.MollifiedConvolution
public import EllipticRegularity.Parabolic.Energy.TestFunction

/-! # Pairing identity for spatial mollification -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped Pointwise

namespace PDE.Parabolic.Lions

/-- The derivative of the first centered kernel, as a compactly supported function of its
integration variable. -/
noncomputable def cauchyKernelDerivativeTest {d : ℕ} (a : ℝ) (x : Vec d)
    (i : Fin d) : Vec d → ℝ :=
  fun y => fderiv ℝ (PDE.Parabolic.Energy.kern a) (x - y) (basisVec i)

theorem cauchyKernelDerivativeTest_continuous {d : ℕ} (a : ℝ) (x : Vec d) (i : Fin d) :
    Continuous (cauchyKernelDerivativeTest a x i) := by
  exact (PDE.Parabolic.Energy.kern_fderiv_continuous a (basisVec i)).comp
    (continuous_const.sub continuous_id)

theorem cauchyKernelDerivativeTest_hasCompactSupport {d : ℕ} {a : ℝ}
    (ha : 0 < a) (x : Vec d) (i : Fin d) :
    HasCompactSupport (cauchyKernelDerivativeTest a x i) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x a)
  intro y hy
  by_contra hxy
  apply hy
  have hnorm' : a < ‖y - x‖ := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hxy
  have hnorm : a < ‖x - y‖ := by simpa [norm_sub_rev] using hnorm'
  simp only [cauchyKernelDerivativeTest]
  have hz := PDE.Parabolic.Energy.fderiv_kern_eq_zero_of_lt_norm ha hnorm
  exact congrArg (fun L : Vec d →L[ℝ] ℝ => L (basisVec i)) hz

/-- Spatial mollification is self-adjoint when paired against a compactly supported smooth test.
The proof is a Fubini swap on the compact support collar of the test and the mollifier. -/
theorem wholeSpaceMollify_pairing {d : ℕ} {a : ℝ} (ha : 0 < a)
    {F g : Vec d → ℝ} (hF : LocallyIntegrable F (volume : Measure (Vec d)))
    (hg : Continuous g) (hgK : HasCompactSupport g) :
    ∫ x, PDE.wholeSpaceMollify a F x * g x =
      ∫ x, F x * PDE.wholeSpaceMollify a g x := by
  let K : Set (Vec d) := tsupport g
  let L : Set (Vec d) := K + Metric.closedBall (0 : Vec d) a
  have hK : IsCompact K := hgK
  have hball : IsCompact (Metric.closedBall (0 : Vec d) a) := isCompact_closedBall 0 a
  have hL : IsCompact L := hK.add hball
  have hLmeas : MeasurableSet L := hL.measurableSet
  have hKLmeasure : (volume.restrict K).prod (volume.restrict L) =
      (volume : Measure (Vec d × Vec d)).restrict (K ×ˢ L) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  let H : Vec d × Vec d → ℝ := fun z =>
    F z.2 * PDE.Parabolic.Energy.kern a (z.1 - z.2) * g z.1
  have hFK : IntegrableOn F L (volume : Measure (Vec d)) :=
    hF.integrableOn_isCompact hL
  have hFprod : Integrable (fun z : Vec d × Vec d => F z.2)
      ((volume.restrict K).prod (volume.restrict L)) := by
    simpa using (integrableOn_const (C := (1 : ℝ)) hK.measure_lt_top.ne).mul_prod hFK
  have hmult : Continuous (fun z : Vec d × Vec d =>
      PDE.Parabolic.Energy.kern a (z.1 - z.2) * g z.1) := by
    exact (PDE.Parabolic.Energy.kern_continuous a).comp
      (continuous_fst.sub continuous_snd) |>.mul (hg.comp continuous_fst)
  obtain ⟨C, hC⟩ := (hK.prod hL).exists_bound_of_continuousOn hmult.continuousOn
  have hmultBound : ∀ᵐ z ∂((volume.restrict K).prod (volume.restrict L)),
      ‖PDE.Parabolic.Energy.kern a (z.1 - z.2) * g z.1‖ ≤ C := by
    rw [hKLmeasure, ae_restrict_iff' (hK.measurableSet.prod hL.measurableSet)]
    exact Filter.Eventually.of_forall fun z hz => hC z hz
  have hHprod : Integrable H ((volume.restrict K).prod (volume.restrict L)) := by
    have h := hFprod.bdd_mul hmult.aestronglyMeasurable (c := C) hmultBound
    exact h.congr (Filter.Eventually.of_forall fun z => by simp [H, mul_assoc]; ring)
  have hzero : ∀ z ∉ K ×ˢ L, H z = 0 := by
    rintro ⟨x, q⟩ hn
    by_cases hx : x ∈ K
    · have hq : q ∉ L := by
        intro hq
        exact hn ⟨hx, hq⟩
      have hk : PDE.Parabolic.Energy.kern a (x - q) = 0 := by
        have hdist : ¬ ‖q - x‖ ≤ a := by
          intro hdist
          apply hq
          exact ⟨x, hx, q - x, by
            rw [Metric.mem_closedBall, dist_eq_norm]
            simpa using hdist, by simp⟩
        have hnorm : a < ‖x - q‖ := by
          rw [norm_sub_rev]
          exact lt_of_not_ge hdist
        apply PDE.Parabolic.Energy.kern_eq_zero_of_lt_norm ha
        exact hnorm
      simp [H, hk]
    · have hg0 : g x = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        simpa [K] using hx
      simp [H, hg0]
  have hH : Integrable H (volume : Measure (Vec d × Vec d)) := by
    have hOn : IntegrableOn H (K ×ˢ L) (volume : Measure (Vec d × Vec d)) := by
      change Integrable H ((volume : Measure (Vec d × Vec d)).restrict (K ×ˢ L))
      rw [← hKLmeasure]
      exact hHprod
    exact hOn.integrable_of_forall_notMem_eq_zero hzero
  have hLHS : ∫ x, PDE.wholeSpaceMollify a F x * g x =
      ∫ x, ∫ y, H (x, y) := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [PDE.Parabolic.Energy.moll_eq]
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with y
    change PDE.Parabolic.Energy.kern a (x - y) * F y * g x =
      F y * PDE.Parabolic.Energy.kern a (x - y) * g x
    ring
  calc
    ∫ x, PDE.wholeSpaceMollify a F x * g x = ∫ x, ∫ y, H (x, y) := hLHS
    _ = ∫ y, ∫ x, H (x, y) := by
      have hH' : Integrable H ((volume : Measure (Vec d)).prod volume) := by
        rw [← Measure.volume_eq_prod]
        exact hH
      calc
        ∫ x, ∫ y, H (x, y) = ∫ z, H z ∂((volume : Measure (Vec d)).prod volume) := by
          symm
          exact integral_prod H hH'
        _ = ∫ y, ∫ x, H (x, y) := integral_prod_symm H hH'
    _ = ∫ y, F y * PDE.wholeSpaceMollify a g y := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [PDE.Parabolic.Energy.moll_eq]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [H]
      rw [← PDE.Parabolic.Lions.cauchyKernel_even a (x - y)]
      ring_nf

/-- Pairing a mollified flux against a centered kernel derivative is the negative flux pairing
against the convolved test kernel. This is the spatial algebra needed for the `Energy.Data`
time-slice increment field. -/
theorem wholeSpaceMollify_kernelDerivative_pairing {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) {F : Vec d → ℝ}
    (hF : LocallyIntegrable F (volume : Measure (Vec d))) (x : Vec d) (i : Fin d) :
    ∫ y, PDE.wholeSpaceMollify b F y *
        fderiv ℝ (PDE.Parabolic.Energy.kern a) (x - y) (basisVec i) =
      -∫ y, F y * fderiv ℝ (cauchyDoubleKernelTest a b x) y (basisVec i) := by
  let g := cauchyKernelDerivativeTest a x i
  have hpair := wholeSpaceMollify_pairing hb hF
    (cauchyKernelDerivativeTest_continuous a x i)
    (cauchyKernelDerivativeTest_hasCompactSupport ha x i)
  have hderiv (y : Vec d) :
      PDE.wholeSpaceMollify b g y =
        -fderiv ℝ (cauchyDoubleKernelTest a b x) y (basisVec i) := by
    rw [cauchyDoubleKernelTest_deriv ha hb]
    rw [PDE.Parabolic.Energy.moll_eq]
    simp only [g, cauchyKernelDerivativeTest]
    simp only [neg_neg]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [← cauchyKernel_even b (y - z)]
    simp only [neg_sub]
  calc
    ∫ y, PDE.wholeSpaceMollify b F y *
        fderiv ℝ (PDE.Parabolic.Energy.kern a) (x - y) (basisVec i) =
      ∫ y, PDE.wholeSpaceMollify b F y * g y := by
        apply integral_congr_ae
        filter_upwards [] with y
        rfl
    _ = ∫ y, F y * PDE.wholeSpaceMollify b g y := hpair
    _ = -∫ y, F y * fderiv ℝ (cauchyDoubleKernelTest a b x) y (basisVec i) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hderiv]
      ring

end PDE.Parabolic.Lions
