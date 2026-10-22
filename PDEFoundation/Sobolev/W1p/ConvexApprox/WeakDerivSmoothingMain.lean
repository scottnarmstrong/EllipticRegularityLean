module

public import PDEFoundation.Sobolev.W1p.ConvexApprox.WeakDerivSmoothingAux

/-!
# Weak derivatives of convex-domain smoothing

This file proves that convex approximation commutes with weak partial
derivatives up to the exact affine factor `1 - ε`, using the integrability
helpers of `WeakDerivSmoothingAux`.

## Main results

* `PDE.HasWeakPartialDerivOn.convexApproxSmoothing`: exact distributional
  derivative identity for the smoothing operator.
* `PDE.HasWeakGradientOn.convexApproxSmoothing`: coordinate-gradient form.
-/

@[expose] public section

open scoped Pointwise

namespace PDE

namespace HasWeakPartialDerivOn

/-- Convex-domain smoothing commutes with a weak partial derivative, with the
exact factor `1 - ε` contributed by the affine sampling map. -/
theorem convexApproxSmoothing
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {i : Fin d} {u gi ρ : Vec d → ℝ}
    (huLoc : MeasureTheory.LocallyIntegrableOn
      u U MeasureTheory.volume)
    (hgiLoc : MeasureTheory.LocallyIntegrableOn
      gi U MeasureTheory.volume)
    (hu : HasWeakPartialDerivOn U i u gi)
    (hρ : IsConvexApproxKernel ρ)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) :
    HasWeakPartialDerivOn U i
      (PDE.convexApproxSmoothing ρ u x0 r ε)
      (fun x =>
        (1 - ε) *
          PDE.convexApproxSmoothing ρ gi x0 r ε x) := by
  intro φ hφSmooth hφCompact hφU
  let dφ : Vec d → ℝ :=
    fun x => (fderiv ℝ φ x) (basisVec i)
  let F : Vec d → Vec d → ℝ :=
    fun x z =>
      ρ z *
        Set.indicator U u
          (convexApproxSample x0 z r ε x) *
        dφ x
  let G : Vec d → Vec d → ℝ :=
    fun x z =>
      ρ z *
        Set.indicator U gi
          (convexApproxSample x0 z r ε x) *
        φ x
  have hdφContinuous : Continuous dφ := by
    simpa only [dφ] using
      (hφSmooth.continuous_fderiv (by simp)).clm_apply
        continuous_const
  have hdφCompact : HasCompactSupport dφ := by
    simpa only [dφ] using
      hφCompact.fderiv_apply
        (𝕜 := ℝ) (basisVec i)
  have hdφSupport :
      Function.support dφ ⊆ tsupport φ := by
    intro x hx
    apply support_fderiv_subset (𝕜 := ℝ)
    change fderiv ℝ φ x ≠ 0
    intro hzero
    apply hx
    simp only [dφ, hzero,
      zero_apply]
  have hdφTSupport : tsupport dφ ⊆ tsupport φ :=
    closure_minimal hdφSupport
      (isClosed_tsupport (f := φ))
  have hdφU : tsupport dφ ⊆ U :=
    hdφTSupport.trans hφU
  have hprodLeft :
      MeasureTheory.Integrable
        (fun p : Vec d × Vec d => F p.1 p.2)
        ((MeasureTheory.volume.restrict (tsupport dφ)).prod
          (MeasureTheory.volume.restrict
            (tsupport ρ))) := by
    simpa only [F] using
      integrable_kernel_mul_indicator_comp_convexApproxSample_prod_mul
        hU huLoc hρ hdφContinuous hdφCompact
        hdφU hball hr hε0 hε1
  have hprodRight :
      MeasureTheory.Integrable
        (fun p : Vec d × Vec d => G p.1 p.2)
        ((MeasureTheory.volume.restrict (tsupport φ)).prod
          (MeasureTheory.volume.restrict
            (tsupport ρ))) := by
    simpa only [G] using
      integrable_kernel_mul_indicator_comp_convexApproxSample_prod_mul
        hU hgiLoc hρ hφSmooth.continuous hφCompact
        hφU hball hr hε0 hε1
  have hswapLeft :
      (∫ x in tsupport dφ,
          ∫ z in tsupport ρ, F x z
            ∂MeasureTheory.volume
          ∂MeasureTheory.volume) =
        ∫ z in tsupport ρ,
          ∫ x in tsupport dφ, F x z
            ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
    simpa only using
      (MeasureTheory.integral_integral_swap
        (μ := MeasureTheory.volume.restrict
          (tsupport dφ))
        (ν := MeasureTheory.volume.restrict
          (tsupport ρ))
        (f := F) hprodLeft)
  have hswapRight :
      (∫ x in tsupport φ,
          ∫ z in tsupport ρ, G x z
            ∂MeasureTheory.volume
          ∂MeasureTheory.volume) =
        ∫ z in tsupport ρ,
          ∫ x in tsupport φ, G x z
            ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
    simpa only using
      (MeasureTheory.integral_integral_swap
        (μ := MeasureTheory.volume.restrict
          (tsupport φ))
        (ν := MeasureTheory.volume.restrict
          (tsupport ρ))
        (f := G) hprodRight)
  have hrestrict :
      ∀ (v ψ : Vec d → ℝ),
        tsupport ψ ⊆ U →
        (∫ x in U,
            PDE.convexApproxSmoothing ρ v x0 r ε x * ψ x
              ∂MeasureTheory.volume) =
          ∫ x in tsupport ψ,
            PDE.convexApproxSmoothing ρ v x0 r ε x * ψ x
              ∂MeasureTheory.volume := by
    intro v ψ hψU
    exact
      MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        hU.measurableSet hψU (fun x hx => by
          simp only [
            image_eq_zero_of_notMem_tsupport hx.2,
            mul_zero])
  have hinner :
      ∀ (v ψ : Vec d → ℝ),
        tsupport ψ ⊆ U →
        (∫ x in tsupport ψ,
            PDE.convexApproxSmoothing ρ v x0 r ε x * ψ x
              ∂MeasureTheory.volume) =
          ∫ x in tsupport ψ,
            ∫ z in tsupport ρ,
              ρ z *
                Set.indicator U v
                  (convexApproxSample x0 z r ε x) *
                ψ x
              ∂MeasureTheory.volume
            ∂MeasureTheory.volume := by
    intro v ψ hψU
    refine MeasureTheory.setIntegral_congr_fun
      (isClosed_tsupport (f := ψ)).measurableSet ?_
    intro x hx
    have hxU : x ∈ U := hψU hx
    have hsample :
        ∀ z ∈ tsupport ρ,
          convexApproxSample x0 z r ε x ∈ U := by
      intro z hz
      have hzNorm : ‖z‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall,
          dist_zero_right] using
            hρ.support_subset_closedBall hz
      exact
        convexApproxSample_mem_of_isOpenBoundedConvexDomain
          hU hxU hball hr hzNorm hε0 hε1.le
    calc
      PDE.convexApproxSmoothing ρ v x0 r ε x * ψ x =
          (∫ z in tsupport ρ,
            ρ z *
              v (convexApproxSample x0 z r ε x)
              ∂MeasureTheory.volume) * ψ x := by
        rfl
      _ = ∫ z in tsupport ρ,
            (ρ z *
              v (convexApproxSample x0 z r ε x)) *
              ψ x
            ∂MeasureTheory.volume := by
        rw [← MeasureTheory.integral_mul_const]
      _ = ∫ z in tsupport ρ,
            ρ z *
              Set.indicator U v
                (convexApproxSample x0 z r ε x) *
              ψ x
            ∂MeasureTheory.volume := by
        refine MeasureTheory.setIntegral_congr_fun
          hρ.compactSupport.isCompact.measurableSet ?_
        intro z hz
        change
          ρ z * v (convexApproxSample x0 z r ε x) * ψ x =
            ρ z *
              Set.indicator U v
                (convexApproxSample x0 z r ε x) *
              ψ x
        rw [Set.indicator_of_mem (hsample z hz)]
  have hfactor :
      ∀ (v ψ : Vec d → ℝ) (z : Vec d),
        tsupport ψ ⊆ U →
        z ∈ tsupport ρ →
        (∫ x in tsupport ψ,
            ρ z *
              Set.indicator U v
                (convexApproxSample x0 z r ε x) *
              ψ x
              ∂MeasureTheory.volume) =
          ρ z *
            ∫ x in U,
              v (convexApproxSample x0 z r ε x) *
                ψ x
              ∂MeasureTheory.volume := by
    intro v ψ z hψU hz
    have hzNorm : ‖z‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall,
        dist_zero_right] using
          hρ.support_subset_closedBall hz
    have hmap :
        Set.MapsTo
          (convexApproxSample x0 z r ε) U U :=
      convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain
        hU hball hr hzNorm hε0 hε1.le
    calc
      (∫ x in tsupport ψ,
          ρ z *
            Set.indicator U v
              (convexApproxSample x0 z r ε x) *
            ψ x
            ∂MeasureTheory.volume) =
          ∫ x in U,
            ρ z *
              Set.indicator U v
                (convexApproxSample x0 z r ε x) *
              ψ x
            ∂MeasureTheory.volume := by
        symm
        exact
          MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
            hU.measurableSet hψU (fun x hx => by
              simp only [
                image_eq_zero_of_notMem_tsupport hx.2,
                mul_zero])
      _ = ∫ x in U,
            ρ z *
              (v (convexApproxSample x0 z r ε x) *
                ψ x)
            ∂MeasureTheory.volume := by
        refine MeasureTheory.setIntegral_congr_fun
          hU.measurableSet ?_
        intro x hx
        change
          ρ z *
              Set.indicator U v
                (convexApproxSample x0 z r ε x) *
              ψ x =
            ρ z *
              (v (convexApproxSample x0 z r ε x) * ψ x)
        rw [Set.indicator_of_mem (hmap hx)]
        ring
      _ = ρ z *
          ∫ x in U,
            v (convexApproxSample x0 z r ε x) *
              ψ x
            ∂MeasureTheory.volume := by
        rw [MeasureTheory.integral_const_mul]
  have hfixed :
      ∀ z ∈ tsupport ρ,
        (∫ x in tsupport dφ, F x z
            ∂MeasureTheory.volume) =
          -(1 - ε) *
            ∫ x in tsupport φ, G x z
              ∂MeasureTheory.volume := by
    intro z hz
    have hweak :
        (∫ x in U,
            u (convexApproxSample x0 z r ε x) *
              dφ x
            ∂MeasureTheory.volume) =
          -∫ x in U,
            ((1 - ε) *
                gi (convexApproxSample x0 z r ε x)) *
              φ x
            ∂MeasureTheory.volume := by
      simpa only [dφ] using
        ((hu.comp_convexApproxSample
          hU hball hr
          (by
            simpa only [Metric.mem_closedBall,
              dist_zero_right] using
                hρ.support_subset_closedBall hz)
          hε0 hε1) φ hφSmooth hφCompact hφU)
    have hscaled :
        (∫ x in U,
            ((1 - ε) *
                gi (convexApproxSample x0 z r ε x)) *
              φ x
            ∂MeasureTheory.volume) =
          (1 - ε) *
            ∫ x in U,
              gi (convexApproxSample x0 z r ε x) *
                φ x
              ∂MeasureTheory.volume := by
      calc
        (∫ x in U,
            ((1 - ε) *
                gi (convexApproxSample x0 z r ε x)) *
              φ x
            ∂MeasureTheory.volume) =
            ∫ x in U,
              (1 - ε) *
                (gi (convexApproxSample x0 z r ε x) *
                  φ x)
              ∂MeasureTheory.volume := by
          apply MeasureTheory.setIntegral_congr_fun
            hU.measurableSet
          intro x _hx
          ring
        _ = (1 - ε) *
            ∫ x in U,
              gi (convexApproxSample x0 z r ε x) *
                φ x
              ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_const_mul]
    calc
      (∫ x in tsupport dφ, F x z
          ∂MeasureTheory.volume) =
          ρ z *
            ∫ x in U,
              u (convexApproxSample x0 z r ε x) *
                dφ x
              ∂MeasureTheory.volume := by
        simpa only [F] using
          hfactor u dφ z hdφU hz
      _ = ρ z *
          (-((1 - ε) *
            ∫ x in U,
              gi (convexApproxSample x0 z r ε x) *
                φ x
              ∂MeasureTheory.volume)) := by
        rw [hweak, hscaled]
      _ = -(1 - ε) *
          (ρ z *
            ∫ x in U,
              gi (convexApproxSample x0 z r ε x) *
                φ x
              ∂MeasureTheory.volume) := by
        ring
      _ = -(1 - ε) *
          ∫ x in tsupport φ, G x z
            ∂MeasureTheory.volume := by
        rw [← hfactor gi φ z hφU hz]
  have hintegrated :
      (∫ z in tsupport ρ,
          ∫ x in tsupport dφ, F x z
            ∂MeasureTheory.volume
          ∂MeasureTheory.volume) =
        ∫ z in tsupport ρ,
          -(1 - ε) *
            ∫ x in tsupport φ, G x z
              ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      hρ.compactSupport.isCompact.measurableSet ?_
    exact hfixed
  calc
    (∫ x in U,
        PDE.convexApproxSmoothing ρ u x0 r ε x *
          (fderiv ℝ φ x) (basisVec i)
        ∂MeasureTheory.volume) =
        ∫ x in U,
          PDE.convexApproxSmoothing ρ u x0 r ε x * dφ x
          ∂MeasureTheory.volume := by
      rfl
    _ = ∫ x in tsupport dφ,
          PDE.convexApproxSmoothing ρ u x0 r ε x * dφ x
          ∂MeasureTheory.volume :=
      hrestrict u dφ hdφU
    _ = ∫ x in tsupport dφ,
          ∫ z in tsupport ρ, F x z
            ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
      simpa only [F] using hinner u dφ hdφU
    _ = ∫ z in tsupport ρ,
          ∫ x in tsupport dφ, F x z
            ∂MeasureTheory.volume
          ∂MeasureTheory.volume :=
      hswapLeft
    _ = ∫ z in tsupport ρ,
          -(1 - ε) *
            ∫ x in tsupport φ, G x z
              ∂MeasureTheory.volume
          ∂MeasureTheory.volume :=
      hintegrated
    _ = -(1 - ε) *
        ∫ z in tsupport ρ,
          ∫ x in tsupport φ, G x z
            ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
      rw [MeasureTheory.integral_const_mul]
    _ = -(1 - ε) *
        ∫ x in tsupport φ,
          ∫ z in tsupport ρ, G x z
            ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
      rw [← hswapRight]
    _ = -(1 - ε) *
        ∫ x in tsupport φ,
          PDE.convexApproxSmoothing ρ gi x0 r ε x * φ x
          ∂MeasureTheory.volume := by
      rw [← hinner gi φ hφU]
    _ = -(1 - ε) *
        ∫ x in U,
          PDE.convexApproxSmoothing ρ gi x0 r ε x * φ x
          ∂MeasureTheory.volume := by
      rw [← hrestrict gi φ hφU]
    _ = -∫ x in U,
        ((1 - ε) *
            PDE.convexApproxSmoothing ρ gi x0 r ε x) *
          φ x
        ∂MeasureTheory.volume := by
      have hscale :
          (∫ x in U,
            ((1 - ε) *
                PDE.convexApproxSmoothing ρ gi x0 r ε x) *
              φ x
            ∂MeasureTheory.volume) =
            (1 - ε) *
              ∫ x in U,
                PDE.convexApproxSmoothing ρ gi x0 r ε x * φ x
                ∂MeasureTheory.volume := by
        calc
          (∫ x in U,
              ((1 - ε) *
                  PDE.convexApproxSmoothing ρ gi x0 r ε x) *
                φ x
              ∂MeasureTheory.volume) =
              ∫ x in U,
                (1 - ε) *
                  (PDE.convexApproxSmoothing ρ gi x0 r ε x * φ x)
                ∂MeasureTheory.volume := by
            refine MeasureTheory.setIntegral_congr_fun
              hU.measurableSet ?_
            intro x _hx
            ring
          _ = (1 - ε) *
              ∫ x in U,
                PDE.convexApproxSmoothing ρ gi x0 r ε x * φ x
                ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_const_mul]
      rw [hscale]
      ring

/-- The globally smooth representative has the same weak partial derivative
as convex-approximation smoothing on the domain. -/
theorem convexApproxSmoothRepresentative
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {i : Fin d} {u gi ρ : Vec d → ℝ}
    (huLoc : MeasureTheory.LocallyIntegrableOn
      u U MeasureTheory.volume)
    (hgiLoc : MeasureTheory.LocallyIntegrableOn
      gi U MeasureTheory.volume)
    (hu : HasWeakPartialDerivOn U i u gi)
    (hρ : IsConvexApproxKernel ρ)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    HasWeakPartialDerivOn U i
      (PDE.convexApproxSmoothRepresentative U ρ u x0 r ε)
      (fun x =>
        (1 - ε) *
          PDE.convexApproxSmoothRepresentative
            U ρ gi x0 r ε x) := by
  intro φ hφSmooth hφCompact hφU
  have hweak :
      HasWeakPartialDerivOn U i
        (PDE.convexApproxSmoothing ρ u x0 r ε)
        (fun x =>
          (1 - ε) *
            PDE.convexApproxSmoothing ρ gi x0 r ε x) :=
    hu.convexApproxSmoothing
      hU huLoc hgiLoc hρ hball hr.le hε0.le hε1
  have hleft :
      (∫ x in U,
          PDE.convexApproxSmoothRepresentative
              U ρ u x0 r ε x *
            (fderiv ℝ φ x) (basisVec i)
          ∂MeasureTheory.volume) =
        ∫ x in U,
          PDE.convexApproxSmoothing ρ u x0 r ε x *
            (fderiv ℝ φ x) (basisVec i)
          ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      hU.measurableSet ?_
    intro x hx
    change
      PDE.convexApproxSmoothRepresentative
            U ρ u x0 r ε x *
          (fderiv ℝ φ x) (basisVec i) =
        PDE.convexApproxSmoothing ρ u x0 r ε x *
          (fderiv ℝ φ x) (basisVec i)
    rw [
      convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
        hU hρ hx hball hr hε0 hε1]
  have hright :
      (∫ x in U,
          ((1 - ε) *
              PDE.convexApproxSmoothing ρ gi x0 r ε x) *
            φ x
          ∂MeasureTheory.volume) =
        ∫ x in U,
          ((1 - ε) *
              PDE.convexApproxSmoothRepresentative
                U ρ gi x0 r ε x) *
            φ x
          ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      hU.measurableSet ?_
    intro x hx
    change
      ((1 - ε) *
          PDE.convexApproxSmoothing ρ gi x0 r ε x) *
          φ x =
        ((1 - ε) *
            PDE.convexApproxSmoothRepresentative
              U ρ gi x0 r ε x) *
          φ x
    rw [
      convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
        hU hρ hx hball hr hε0 hε1]
  calc
    (∫ x in U,
        PDE.convexApproxSmoothRepresentative U ρ u x0 r ε x *
          (fderiv ℝ φ x) (basisVec i)
        ∂MeasureTheory.volume) =
        ∫ x in U,
          PDE.convexApproxSmoothing ρ u x0 r ε x *
            (fderiv ℝ φ x) (basisVec i)
          ∂MeasureTheory.volume :=
      hleft
    _ = -∫ x in U,
          ((1 - ε) *
              PDE.convexApproxSmoothing ρ gi x0 r ε x) *
            φ x
          ∂MeasureTheory.volume :=
      hweak φ hφSmooth hφCompact hφU
    _ = -∫ x in U,
          ((1 - ε) *
              PDE.convexApproxSmoothRepresentative
                U ρ gi x0 r ε x) *
            φ x
          ∂MeasureTheory.volume := by
      rw [hright]

end HasWeakPartialDerivOn

namespace HasWeakGradientOn

/-- Coordinate-gradient form of the exact weak-derivative identity for convex
approximation smoothing. -/
theorem convexApproxSmoothing
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    {ρ : Vec d → ℝ}
    (huLoc : MeasureTheory.LocallyIntegrableOn
      u U MeasureTheory.volume)
    (hDuLoc : ∀ i : Fin d,
      MeasureTheory.LocallyIntegrableOn
        (fun x => Du x i) U MeasureTheory.volume)
    (hu : HasWeakGradientOn U u Du)
    (hρ : IsConvexApproxKernel ρ)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) :
    HasWeakGradientOn U
      (PDE.convexApproxSmoothing ρ u x0 r ε)
      (fun x i =>
        (1 - ε) *
          PDE.convexApproxSmoothing ρ
            (fun y => Du y i) x0 r ε x) := by
  intro i
  exact
    (hu i).convexApproxSmoothing
      hU huLoc (hDuLoc i) hρ hball hr hε0 hε1

/-- Coordinate-gradient form of
`HasWeakPartialDerivOn.convexApproxSmoothRepresentative`. -/
theorem convexApproxSmoothRepresentative
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    {ρ : Vec d → ℝ}
    (huLoc : MeasureTheory.LocallyIntegrableOn
      u U MeasureTheory.volume)
    (hDuLoc : ∀ i : Fin d,
      MeasureTheory.LocallyIntegrableOn
        (fun x => Du x i) U MeasureTheory.volume)
    (hu : HasWeakGradientOn U u Du)
    (hρ : IsConvexApproxKernel ρ)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    HasWeakGradientOn U
      (PDE.convexApproxSmoothRepresentative U ρ u x0 r ε)
      (fun x i =>
        (1 - ε) *
          PDE.convexApproxSmoothRepresentative U ρ
            (fun y => Du y i) x0 r ε x) := by
  intro i
  exact
    (hu i).convexApproxSmoothRepresentative
      hU huLoc (hDuLoc i) hρ hball hr hε0 hε1

end HasWeakGradientOn

end PDE
