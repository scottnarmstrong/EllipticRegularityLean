module

public import PDEFoundation.Sobolev.Ch4.LipschitzWeak
public import PDEFoundation.Sobolev.Ch4.Compact
public import PDEFoundation.PDE.WeakDivergenceForm

/-!
# Lipschitz test functions for `H¹`

The weak-gradient identity of an `H¹(U)` function extends from smooth compactly supported test
functions to *Euclidean-Lipschitz* compactly supported test functions `ψ`, with the a.e.
classical derivative of `ψ`:
`∫_U u ∂ᵢψ = - ∫_U ∂ᵢu ψ`.
The proof mollifies `ψ` (a mollification of a Lipschitz function has derivative equal to the
mollification of its a.e. derivative, since the latter is its weak derivative).
-/

@[expose] public section

open scoped ENNReal Convolution Topology
open MeasureTheory Set Filter

namespace PDE.Ch4Infra

variable {d : ℕ} {U : Set (Vec d)}

/-- Pairing an `L²(U)` function with mollifications converges to the pairing with the limit. -/
theorem tendsto_setIntegral_mul_wholeSpaceMollify {G F : Vec d → ℝ} (hG : MemL2On U G)
    (hF : MemLp F 2 volume) {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n ≤ 1)
    (ha0 : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in U, G x * wholeSpaceMollify (a n) F x) atTop
      (𝓝 (∫ x in U, G x * F x)) := by
  have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
  refine tendsto_setIntegral_mul_of_tendsto_eLpNorm hG (fun n => ?_)
    (hF.restrict U) ?_
  · exact (contDiff_memLp_convolution_scaledConvexApproxKernel hρ (ha n) (by norm_num)
      (by norm_num) hF).2.1.restrict U
  · have h := tendsto_eLpNorm_wholeSpaceMollify_sub (p := 2) (by norm_num) (by norm_num) hF
      ha ha1 ha0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n => bot_le)
      (fun n => ?_)
    exact eLpNorm_mono_measure _ Measure.restrict_le_self

/-- **Lipschitz test functions.**  If `ψ` is Euclidean-Lipschitz with compact support in `U`
then `∫_U u ∂ᵢψ = - ∫_U (∂ᵢu) ψ` for every `u ∈ H¹(U)`. -/
theorem H1Function.integral_mul_partial_lip_eq (hU : IsOpen U) (u : H1Function U)
    {L : ℝ} {ψ : Vec d → ℝ} (hψ : EucLip L ψ) (hL : 0 ≤ L) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) (i : Fin d) :
    ∫ x in U, u.toFun x * fderiv ℝ ψ x (basisVec i) = -∫ x in U, u.grad x i * ψ x := by
  classical
  have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
  obtain ⟨δ, hδ, hδU⟩ := hψc.isCompact.exists_cthickening_subset_open hU hψU
  let δ' : ℝ := min δ 1
  have hδ' : 0 < δ' := lt_min hδ one_pos
  let a : ℕ → ℝ := fun n => δ' * unitConvexApproxScale n
  have ha : ∀ n, 0 < a n := fun n => mul_pos hδ' (unitConvexApproxScale_pos n)
  have ha1 : ∀ n, a n ≤ 1 := fun n =>
    calc a n ≤ 1 * 1 := mul_le_mul (min_le_right _ _) (unitConvexApproxScale_le_one n)
            (unitConvexApproxScale_pos n).le zero_le_one
      _ = 1 := one_mul 1
  have haδ : ∀ n, a n ≤ δ := fun n =>
    calc a n ≤ δ' * 1 := mul_le_mul_of_nonneg_left (unitConvexApproxScale_le_one n) hδ'.le
      _ ≤ δ := by rw [mul_one]; exact min_le_left _ _
  have ha0 : Tendsto a atTop (𝓝 0) := by
    simpa [a] using tendsto_unitConvexApproxScale_zero.const_mul δ'
  have hψcont : Continuous ψ := hψ.continuous hL
  have hψmem : MemLp ψ 2 volume := hψcont.memLp_of_hasCompactSupport hψc
  -- the a.e. derivative is bounded, measurable and compactly supported
  set Dψ : Vec d → ℝ := fun x => fderiv ℝ ψ x (basisVec i) with hDψ
  have hDmeas : AEStronglyMeasurable Dψ volume :=
    (measurable_fderiv_apply_const ℝ ψ (basisVec i)).aestronglyMeasurable
  have hDzero : ∀ x, x ∉ tsupport ψ → Dψ x = 0 := fun x hx => by
    simp [hDψ, fderiv_of_notMem_tsupport ℝ hx]
  have hDmem : MemLp Dψ 2 volume := by
    have hind : Dψ = (tsupport ψ).indicator Dψ := by
      funext x
      by_cases hx : x ∈ tsupport ψ
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx, hDzero x hx]
    rw [hind, memLp_indicator_iff_restrict (isClosed_tsupport ψ).measurableSet]
    have : IsFiniteMeasure (volume.restrict (tsupport ψ)) :=
      ⟨by simpa using hψc.isCompact.measure_lt_top⟩
    refine MemLp.of_bound (hDmeas.mono_measure Measure.restrict_le_self) L ?_
    have := hψ.ae_differentiableAt hL
    filter_upwards [ae_restrict_of_ae this] with x hx
    exact (Real.norm_eq_abs _ ▸ hψ.abs_partialDeriv_le hL hx i)
  have hweak := hψ.hasWeakPartialDerivOn_univ hL i
  -- mollified test functions
  let ψn : ℕ → Vec d → ℝ := fun n => wholeSpaceMollify (a n) ψ
  have hψs : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψn n) := fun n =>
    (contDiff_memLp_convolution_scaledConvexApproxKernel hρ (ha n) (by norm_num) (by norm_num)
      hψmem).1
  have hψnts : ∀ n, tsupport (ψn n) ⊆ Metric.cthickening (a n) (tsupport ψ) := fun n =>
    closure_minimal (support_wholeSpaceMollify_subset_cthickening (ha n))
      Metric.isClosed_cthickening
  have hψnc : ∀ n, HasCompactSupport (ψn n) := fun n =>
    HasCompactSupport.of_support_subset_isCompact (hψc.isCompact.cthickening (r := a n))
      (support_wholeSpaceMollify_subset_cthickening (ha n))
  have hψnU : ∀ n, tsupport (ψn n) ⊆ U := fun n =>
    (hψnts n).trans ((Metric.cthickening_mono (haδ n) _).trans hδU)
  have hderiv : ∀ n x, (fderiv ℝ (ψn n) x) (basisVec i) = wholeSpaceMollify (a n) Dψ x :=
    fun n x => congrFun (euclideanCoordDeriv_convolution_eq_of_hasWeakPartialDerivOn
      (hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport (ha n))
      (contDiff_scaledConvexApproxKernel hρ _) (hψmem.locallyIntegrable (by norm_num)) hweak) x
  have hid : ∀ n, ∫ x in U, u.toFun x * wholeSpaceMollify (a n) Dψ x =
      -∫ x in U, u.grad x i * ψn n x := fun n => by
    have := u.hasWeakPartialDerivOn i (ψn n) (hψs n) (hψnc n) (hψnU n)
    simpa only [hderiv] using this
  have h1 := tendsto_setIntegral_mul_wholeSpaceMollify u.memL2 hDmem ha ha1 ha0
  have h2 := tendsto_setIntegral_mul_wholeSpaceMollify (u.grad_memL2 i) hψmem ha ha1 ha0
  have h3 := tendsto_nhds_unique (h1.congr fun n => hid n) h2.neg
  exact h3

end PDE.Ch4Infra
