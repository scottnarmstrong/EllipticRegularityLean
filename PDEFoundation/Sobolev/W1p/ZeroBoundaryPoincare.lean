module

public import PDEFoundation.Sobolev.Inequalities.SmoothZeroBoundaryPoincare
public import PDEFoundation.Sobolev.W1p.ZeroBoundary

/-! # Zero-boundary Poincaré inequality on the closed W1p graph -/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

noncomputable section

private theorem norm_fst_le_mul_norm_snd_smooth
    {d : ℕ} (hd : 0 < d) {U : Set (Vec d)} {D q : ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hdiam : HasEuclideanDiameterLE U D) (hD : 0 ≤ D)
    (hq : 1 < q) (φ : WeakTestFunction U) :
    letI : Fact (1 ≤ ENNReal.ofReal q) :=
      ⟨ENNReal.one_le_ofReal.mpr hq.le⟩
    ‖(smoothCompactlySupportedW1pGraph (p := ENNReal.ofReal q) hU.isOpen φ).1.1‖ ≤
      (((2 : ℝ) ^ d + 1) * D) *
        ‖(smoothCompactlySupportedW1pGraph (p := ENNReal.ofReal q) hU.isOpen φ).1.2‖ := by
  let : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr hq.le⟩
  let p : ENNReal := ENNReal.ofReal q
  let w := W1pFunction.ofContDiff hU.isOpen
    (φ.contDiff.of_le (by simp)) φ.hasCompactSupport p
  have hest := eLpNormOn_testFunction_le_two_pow_add_one_mul_diameter_grad
    hd hU hdiam hD hq φ
  have hGradMeas : AEStronglyMeasurable
      (fun x i => (fderiv ℝ φ.toFun x) (basisVec i)) (volumeOn U) :=
    (aemeasurable_pi_iff.2 fun i =>
      (w.grad_memLp i).aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hEq : ∀ r,
      eLpNorm (toHilbertVecField fun x i => (fderiv ℝ φ.toFun x) (basisVec i)) r
          (volumeOn U) =
        eLpNorm (fun x => vecEuclideanNorm (classicalGradient φ.toFun x)) r
          (volumeOn U) :=
    fun r => eLpNorm_toHilbertVecField_eq _ r _ hGradMeas
  have htop : ENNReal.ofReal (((2 : ℝ) ^ d + 1) * D) *
      euclideanFieldELpNormOn U p (classicalGradient φ.toFun) ≠ ∞ := by
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    simpa only [euclideanFieldELpNormOn, w, W1pFunction.ofContDiff,
      hEq] using!
      (gradMemLpOn_iff_memLp_toHilbertVecField.mp w.gradMemLp).eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono htop hest
  have hCnonneg : 0 ≤ ((2 : ℝ) ^ d + 1) * D :=
    mul_nonneg (add_nonneg (by positivity) zero_le_one) hD
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCnonneg] at hreal
  simpa only [smoothCompactlySupportedW1pGraph, w,
    W1pFunction.toW1pGraph, W1pFunction.ofContDiff,
    w1pGraphOfRepresentatives, weakGradientLpPairOfRepresentatives,
    MemLpOn.toScalarLp, GradMemLpOn.toHilbertVectorLp,
    Lp.norm_toLp, eLpNormOn, euclideanFieldELpNormOn,
    hEq, classicalGradient_apply, p] using! hreal

/-- The value component of a zero-boundary graph point is controlled by its
weak-gradient component. -/
theorem W10pGraph.norm_fst_le_two_pow_add_one_mul_diameter_norm_snd
    {d : ℕ} (hd : 0 < d) {U : Set (Vec d)} {D q : ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hdiam : HasEuclideanDiameterLE U D) (hD : 0 ≤ D)
    (hq : 1 < q) :
    letI : Fact (1 ≤ ENNReal.ofReal q) :=
      ⟨ENNReal.one_le_ofReal.mpr hq.le⟩
    ∀ u : W10pGraph (p := ENNReal.ofReal q) hU.isOpen,
      ‖(u : W1pGraph U (ENNReal.ofReal q)).1.1‖ ≤
        (((2 : ℝ) ^ d + 1) * D) *
          ‖(u : W1pGraph U (ENNReal.ofReal q)).1.2‖ := by
  let : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr hq.le⟩
  intro u
  let p : ENNReal := ENNReal.ofReal q
  let C : ℝ := ((2 : ℝ) ^ d + 1) * D
  have hp1 : (1 : ENNReal) ≤ p := ENNReal.one_le_ofReal.mpr hq.le
  let : Fact (1 ≤ p) := ⟨hp1⟩
  rcases W10pGraph.exists_tendsto_smooth (p := p) hU.isOpen u with ⟨φ, hφ⟩
  let v : ℕ → W1pGraph U p := fun n =>
    smoothCompactlySupportedW1pGraph (p := p) hU.isOpen (φ n)
  have hv : Tendsto v atTop (𝓝 (u : W1pGraph U p)) := hφ
  have hvval : Tendsto (fun n => (v n).1.1) atTop
      (𝓝 (u : W1pGraph U p).1.1) :=
    ((continuous_fst.comp continuous_subtype_val).tendsto _).comp hv
  have hvgrad : Tendsto (fun n => (v n).1.2) atTop
      (𝓝 (u : W1pGraph U p).1.2) :=
    ((continuous_snd.comp continuous_subtype_val).tendsto _).comp hv
  have hdiff : Tendsto
      (fun n => ‖(v n).1.1‖ - C * ‖(v n).1.2‖) atTop
      (𝓝 (‖(u : W1pGraph U p).1.1‖ - C * ‖(u : W1pGraph U p).1.2‖)) :=
    hvval.norm.sub (tendsto_const_nhds.mul hvgrad.norm)
  have hsmooth : ∀ n, ‖(v n).1.1‖ ≤ C * ‖(v n).1.2‖ := by
    intro n
    simpa only [v, C, p] using
      norm_fst_le_mul_norm_snd_smooth hd hU hdiam hD hq (φ n)
  have hnonpos : ‖(u : W1pGraph U p).1.1‖ - C * ‖(u : W1pGraph U p).1.2‖ ≤ 0 :=
    le_of_tendsto' hdiff fun n => sub_nonpos.mpr (hsmooth n)
  exact sub_nonpos.mp hnonpos

/-- The weak-gradient component of the canonical zero-boundary graph. -/
noncomputable def w10pGradientCLM
    {d : ℕ} {U : Set (Vec d)} (p : ENNReal) [Fact (1 ≤ p)]
    (hU : IsOpen U) :
    W10pGraph (p := p) hU →L[ℝ] HilbertVectorLp U p :=
  (ContinuousLinearMap.snd ℝ (ScalarLp U p) (HilbertVectorLp U p)).comp
    ((weakGradientGraph U p).subtypeL.comp
      (w10pGraphClosedSubmodule (p := p) hU).subtypeL)

@[simp]
theorem w10pGradientCLM_apply
    {d : ℕ} {U : Set (Vec d)} (p : ENNReal) [Fact (1 ≤ p)]
    (hU : IsOpen U) (u : W10pGraph (p := p) hU) :
    w10pGradientCLM p hU u = (u : W1pGraph U p).1.2 :=
  rfl

/-- On a bounded open convex domain, the weak-gradient projection is
injective on the zero-boundary graph. -/
theorem w10pGradientCLM_injective
    {d : ℕ} (hd : 0 < d) {U : Set (Vec d)} {D q : ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hdiam : HasEuclideanDiameterLE U D) (hD : 0 ≤ D)
    (hq : 1 < q) :
    letI : Fact (1 ≤ ENNReal.ofReal q) :=
      ⟨ENNReal.one_le_ofReal.mpr hq.le⟩
    Function.Injective (w10pGradientCLM (ENNReal.ofReal q) hU.isOpen) := by
  let : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr hq.le⟩
  let S := W10pGraph (p := ENNReal.ofReal q) hU.isOpen
  let : NormedAddCommGroup S := inferInstance
  intro u v huv
  have hgrad : ((u - v : W10pGraph (p := ENNReal.ofReal q) hU.isOpen) :
      W1pGraph U (ENNReal.ofReal q)).1.2 = 0 := by
    change w10pGradientCLM (ENNReal.ofReal q) hU.isOpen (u - v) = 0
    rw [map_sub, huv, sub_self]
  have hbound := W10pGraph.norm_fst_le_two_pow_add_one_mul_diameter_norm_snd
    hd hU hdiam hD hq (u - v)
  rw [hgrad, norm_zero, mul_zero] at hbound
  have hval : ((u - v : W10pGraph (p := ENNReal.ofReal q) hU.isOpen) :
      W1pGraph U (ENNReal.ofReal q)).1.1 = 0 :=
    norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))
  apply sub_eq_zero.mp
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact hval
  · exact hgrad

end

end PDE
