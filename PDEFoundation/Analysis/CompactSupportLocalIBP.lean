module

public import PDEFoundation.Sobolev.WeakDerivative

@[expose] public section

namespace PDE

open MeasureTheory Set Filter
open scoped Topology

private theorem continuous_mul_of_continuousOn_of_hasCompactSupport
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {f g : Vec d → ℝ} (hf : ContinuousOn f U) (hg : Continuous g)
    (hgsub : tsupport g ⊆ U) :
    Continuous (fun x => f x * g x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ tsupport g
  · exact (hf.continuousAt (hU.mem_nhds (hgsub hx))).mul hg.continuousAt
  · have hev : g =ᶠ[𝓝 x] 0 :=
      ((isClosed_tsupport (f := g)).isOpen_compl.eventually_mem hx).mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    have heq : (fun y => f y * g y) =ᶠ[𝓝 x] 0 := by
      filter_upwards [hev] with y hy
      simp [hy]
    exact continuousAt_const.congr_of_eventuallyEq heq

private theorem contDiff_mul_of_contDiffOn_of_hasCompactSupport
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {f g : Vec d → ℝ} (hf : ContDiffOn ℝ 1 f U) (hg : ContDiff ℝ 1 g)
    (hgsub : tsupport g ⊆ U) :
    ContDiff ℝ 1 (fun x => f x * g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport g
  · exact (hf.contDiffAt (hU.mem_nhds (hgsub hx))).mul hg.contDiffAt
  · have hev : g =ᶠ[𝓝 x] 0 :=
      ((isClosed_tsupport (f := g)).isOpen_compl.eventually_mem hx).mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    have heq : (fun y => f y * g y) =ᶠ[𝓝 x] 0 := by
      filter_upwards [hev] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- Local integration by parts against a smooth compactly supported test
function. All integrability is supplied by the test's compact support. -/
theorem integral_mul_weakTestFunction_partialDeriv_eq_neg_integral_fderiv_mul
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {f : Vec d → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (φ : WeakTestFunction U) (i : Fin d) :
    (∫ x in U, f x * φ.partialDeriv i x) =
      -∫ x in U, (fderiv ℝ f x) (basisVec i) * φ x := by
  let ei : Vec d := basisVec i
  let g : Vec d → ℝ := φ.toFun
  let dg : Vec d → ℝ := fun x => (fderiv ℝ g x) ei
  let df : Vec d → ℝ := fun x => (fderiv ℝ f x) ei
  have hg1 : ContDiff ℝ 1 g := φ.contDiff.of_le (by simp)
  have hprodDiff : ContDiff ℝ 1 (fun x => f x * g x) :=
    contDiff_mul_of_contDiffOn_of_hasCompactSupport hU hf hg1
      φ.tsupport_subset
  have hdgCont : Continuous dg := by
    dsimp only [dg, g]
    exact (φ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdgCompact : HasCompactSupport dg := by
    dsimp only [dg, g]
    exact φ.hasCompactSupport.fderiv_apply ℝ ei
  have hdgSub : tsupport dg ⊆ U := by
    intro x hx
    apply φ.tsupport_subset
    apply tsupport_fderiv_subset ℝ
    exact closure_mono (fun y hy => by
      change (fderiv ℝ φ.toFun y) ei ≠ 0 at hy
      exact fun hzero => hy (by rw [hzero]; exact zero_apply _)) hx
  have hACont : Continuous (fun x => f x * dg x) :=
    continuous_mul_of_continuousOn_of_hasCompactSupport hU
      hf.continuousOn hdgCont hdgSub
  have hACompact : HasCompactSupport (fun x => f x * dg x) :=
    hdgCompact.mul_left
  have hdfContOn : ContinuousOn df U := by
    intro x hx
    dsimp only [df]
    exact ((hf.contDiffAt (hU.mem_nhds hx)).continuousAt_fderiv (by norm_num)).clm_apply
      continuousAt_const |>.continuousWithinAt
  have hBCont : Continuous (fun x => df x * g x) :=
    continuous_mul_of_continuousOn_of_hasCompactSupport hU hdfContOn
      φ.contDiff.continuous φ.tsupport_subset
  have hBCompact : HasCompactSupport (fun x => df x * g x) :=
    φ.hasCompactSupport.mul_left
  have hAInt : Integrable (fun x => f x * dg x) volume :=
    hACont.integrable_of_hasCompactSupport hACompact
  have hBInt : Integrable (fun x => df x * g x) volume :=
    hBCont.integrable_of_hasCompactSupport hBCompact
  have hProdInt : Integrable (fun x => f x * g x) volume :=
    hprodDiff.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left
  have hzero : (∫ x, (fderiv ℝ (fun y => f y * g y) x) ei ∂volume) = 0 := by
    have hderivCont : Continuous (fun x =>
        (fderiv ℝ (fun y => f y * g y) x) ei) :=
      (hprodDiff.continuous_fderiv (by simp)).clm_apply continuous_const
    have hderivCompact : HasCompactSupport (fun x =>
        (fderiv ℝ (fun y => f y * g y) x) ei) :=
      φ.hasCompactSupport.mul_left.fderiv_apply ℝ ei
    have hderivInt : Integrable (fun x =>
        (fderiv ℝ (fun y => f y * g y) x) ei) volume :=
      hderivCont.integrable_of_hasCompactSupport hderivCompact
    have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := volume) (f := fun _ : Vec d => (1 : ℝ)) (g := fun x => f x * g x) (v := ei)
      (by simp) (by simpa using hderivInt) (by simpa using hProdInt)
      (fun _ _ => differentiableAt_const _)
      (fun x _ => hprodDiff.differentiable (by norm_num) x)
    simpa using hibp
  have hderivOn : ∀ x ∈ U,
      (fderiv ℝ (fun y => f y * g y) x) ei = f x * dg x + df x * g x := by
    intro x hx
    rw [fderiv_fun_mul
      ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
      (hg1.differentiable (by simp) x)]
    simp [dg, df, g, ei]
    ring
  have hsum : (∫ x in U, (f x * dg x + df x * g x)) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · calc
        (∫ x, (f x * dg x + df x * g x) ∂volume) =
            ∫ x, (fderiv ℝ (fun y => f y * g y) x) ei ∂volume := by
          apply integral_congr_ae
          filter_upwards [] with x
          by_cases hx : x ∈ U
          · exact (hderivOn x hx).symm
          · have hnot : x ∉ tsupport g := fun h => hx (φ.tsupport_subset h)
            have hg0 : g x = 0 := image_eq_zero_of_notMem_tsupport hnot
            have hdg0 : dg x = 0 := by
              dsimp only [dg]
              rw [fderiv_of_notMem_tsupport ℝ hnot]
              exact zero_apply _
            have hprodzero : (fun y => f y * g y) =ᶠ[𝓝 x] 0 := by
              have hev : g =ᶠ[𝓝 x] 0 :=
                ((isClosed_tsupport (f := g)).isOpen_compl.eventually_mem hnot).mono
                  (fun y hy => image_eq_zero_of_notMem_tsupport hy)
              filter_upwards [hev] with y hy
              simp [hy]
            rw [hprodzero.fderiv_eq]
            simp [hg0, hdg0]
        _ = 0 := hzero
    · intro x hx
      have hnot : x ∉ tsupport g := fun h => hx (φ.tsupport_subset h)
      have hg0 : g x = 0 := image_eq_zero_of_notMem_tsupport hnot
      have hdg0 : dg x = 0 := by
        dsimp only [dg]
        rw [fderiv_of_notMem_tsupport ℝ hnot]
        exact zero_apply _
      simp [hg0, hdg0]
  rw [integral_add hAInt.integrableOn hBInt.integrableOn] at hsum
  change (∫ x in U, f x * dg x) = -∫ x in U, df x * g x
  linarith

end PDE
