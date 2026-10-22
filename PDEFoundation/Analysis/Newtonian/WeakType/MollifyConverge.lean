module

public import PDEFoundation.Analysis.Newtonian.WeakType.MollifyVec
public import PDEFoundation.Analysis.Newtonian.NewtonPotentialSmoothProof
public import PDEFoundation.Analysis.Newtonian.Potential.Decay

/-!
# Mollification commutes with the gradient of the Newtonian potential up to uniform error

For `F` smooth with compact support, `∂_k (mollVec a F)_i = M_a (∂_k F_i)`, and consequently
`∇ u_{mollVec a F} (x) → ∇ u_F (x)` as `a → 0⁺`, for every `x`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Convolution ENNReal Topology

namespace PDE.NewtonWeakType

noncomputable section

variable {d : ℕ}

theorem bddSupp_of_continuous {g : Vec d → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    BddSupp g := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : Vec d)
  refine ⟨hg.measurable, ⟨C, hC⟩, ⟨R + 1, fun x hx => ?_⟩⟩
  by_contra hne
  have h2 : ‖x‖ ≤ R := by simpa using hR (subset_tsupport _ hne)
  linarith

theorem vbdd_of_smooth {F : Vec d → Vec d} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) : VBdd F := fun i =>
  bddSupp_of_continuous ((contDiff_pi.mp hF) i).continuous
    (hFc.comp_left (g := fun v : Vec d => v i) rfl)

theorem euclideanCoordDeriv_wholeSpaceMollify {a : ℝ} {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) (k : Fin d) :
    euclideanCoordDeriv k (wholeSpaceMollify a g) = wholeSpaceMollify a (euclideanCoordDeriv k g) := by
  funext x
  set L := ContinuousLinearMap.mul ℝ ℝ with hL
  have hK : LocallyIntegrable (mollK (d := d) a) volume :=
    (continuous_scaledConvexApproxKernel
      (isConvexApproxKernel_unitConvexApproxKernel (d := d)).continuous a).locallyIntegrable
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by exact_mod_cast le_top)
  have hdc : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by simp)
  have hcd : HasCompactSupport (fderiv ℝ g) := hgc.fderiv ℝ
  have hder := hgc.hasFDerivAt_convolution_right L hK hg1 x
  unfold euclideanCoordDeriv
  have e : wholeSpaceMollify a g = (mollK (d := d) a) ⋆[L, volume] g := by
    funext y
    rw [wholeSpaceMollify_apply]
    simp [convolution_def, hL]
  rw [e, hder.fderiv, convolution_precompR_apply L hK hcd hdc x (basisVec k)]
  rfl

theorem VBdd.hasCompactSupport {f : Vec d → Vec d} (hf : VBdd f) : HasCompactSupport f := by
  obtain ⟨R, hR⟩ := hf.exists_supp
  exact HasCompactSupport.intro (isCompact_closedBall (0 : Vec d) R) fun x hx => hR x (by
    have : R < ‖x‖ := by simpa using hx
    exact this.le)

/-- A bound for the Newtonian pairing of a bounded field supported in `{‖y‖ < S}`. -/
theorem exists_abs_integral_vecDot_newtonKernel_le (hd : 0 < d) (x : Vec d) (S : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : Vec d → Vec d, Continuous H → HasCompactSupport H → ∀ δ : ℝ, 0 ≤ δ →
      (∀ y i, |H y i| ≤ δ) → (∀ y, S ≤ ‖y‖ → H y = 0) →
      |∫ y, vecDot (newtonKernel (x - y)) (H y)| ≤ δ * C := by
  set B : Set (Vec d) := Metric.closedBall 0 (‖x‖ + S) with hB
  have hBc : IsCompact B := isCompact_closedBall _ _
  have hint : ∀ i : Fin d, IntegrableOn (fun t => |newtonKernel t i|) B := fun i =>
    ((locallyIntegrable_newtonKernel_apply hd i).integrableOn_isCompact hBc).abs
  refine ⟨∑ i : Fin d, ∫ t in B, |newtonKernel t i|, Finset.sum_nonneg fun i _ =>
    setIntegral_nonneg hBc.measurableSet fun t _ => abs_nonneg _, fun H hH hHc δ hδ hbd hS => ?_⟩
  have hsub : ∫ y, vecDot (newtonKernel (x - y)) (H y) =
      ∫ t, vecDot (newtonKernel t) (H (x - t)) := by
    rw [← integral_sub_left_eq_self (fun t => vecDot (newtonKernel t) (H (x - t)))
      (volume : Measure (Vec d)) x]
    simp only [sub_sub_cancel]
  rw [hsub]
  have hbound : ∀ t, ‖vecDot (newtonKernel t) (H (x - t))‖ ≤
      ∑ i : Fin d, δ * B.indicator (fun t => |newtonKernel t i|) t := by
    intro t
    rw [Real.norm_eq_abs]
    by_cases ht : t ∈ B
    · calc |vecDot (newtonKernel t) (H (x - t))|
          = |∑ i : Fin d, newtonKernel t i * H (x - t) i| := rfl
        _ ≤ ∑ i : Fin d, |newtonKernel t i * H (x - t) i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin d, δ * B.indicator (fun t => |newtonKernel t i|) t := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Set.indicator_of_mem ht, abs_mul, mul_comm δ]
          exact mul_le_mul_of_nonneg_left (hbd _ _) (abs_nonneg _)
    · have : H (x - t) = 0 := by
        apply hS
        by_contra hlt
        push Not at hlt
        apply ht
        have : ‖t‖ ≤ ‖x‖ + ‖x - t‖ := by
          simpa using norm_sub_le x (x - t)
        simp only [hB, Metric.mem_closedBall, dist_zero_right]
        linarith
      simp [vecDot, this]
      exact Finset.sum_nonneg fun i _ => mul_nonneg hδ (Set.indicator_nonneg (fun _ _ => abs_nonneg _) t)
  have hg : Integrable (fun t => ∑ i : Fin d, δ * B.indicator (fun t => |newtonKernel t i|) t) :=
    integrable_finsetSum _ fun i _ => ((integrable_indicator_iff hBc.measurableSet).mpr (hint i)).const_mul δ
  have hfi : Integrable (fun t => vecDot (newtonKernel t) (H (x - t))) := by
    have := (integrable_vecDot_newtonKernel_sub hd hH hHc x).comp_sub_left x
    simpa [sub_sub_cancel] using this
  calc |∫ t, vecDot (newtonKernel t) (H (x - t))|
      ≤ ∫ t, ∑ i : Fin d, δ * B.indicator (fun t => |newtonKernel t i|) t := by
        have := norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hbound)
        simpa using this
    _ = δ * ∑ i : Fin d, ∫ t in B, |newtonKernel t i| := by
        rw [integral_finsetSum _ fun i _ => ((integrable_indicator_iff hBc.measurableSet).mpr (hint i)).const_mul δ,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_const_mul, integral_indicator hBc.measurableSet]

theorem vecDot_sub_right' (u v w : Vec d) : vecDot u (v - w) = vecDot u v - vecDot u w := by
  simp [vecDot, mul_sub, Finset.sum_sub_distrib]

/-- For smooth compactly supported `F`, `∂_k u_{F_a}(x) → ∂_k u_F(x)` as `a → 0⁺`. -/
theorem eventually_abs_coordDeriv_mollVec_sub_le (hd : 0 < d) {F : Vec d → Vec d}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) (x : Vec d) (k : Fin d)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a in 𝓝[>] (0 : ℝ),
      |euclideanCoordDeriv k (newtonPotential (mollVec a F)) x -
          euclideanCoordDeriv k (newtonPotential F) x| ≤ ε := by
  have hFs : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun z => F z i) := fun i => (contDiff_pi.mp hF) i
  set G : Vec d → Vec d := fun y i => euclideanCoordDeriv k (fun z => F z i) y with hGdef
  have hGs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun y => G y i) := fun i =>
    contDiff_euclideanCoordDeriv (hFs i) k
  have hGcs : ∀ i, HasCompactSupport (fun y => G y i) := fun i =>
    hasCompactSupport_euclideanCoordDeriv (hasCompactSupport_apply hFc i) k
  have hG : VBdd G := fun i => bddSupp_of_continuous (hGs i).continuous (hGcs i)
  have hGsm : ContDiff ℝ (⊤ : ℕ∞) G := contDiff_pi.mpr hGs
  have hGc : HasCompactSupport G := hG.hasCompactSupport
  obtain ⟨R, hR⟩ := hG.exists_supp
  obtain ⟨C, hC0, hC⟩ := exists_abs_integral_vecDot_newtonKernel_le hd x (R + 1)
  set δ : ℝ := ε / (C + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hex : ∀ i : Fin d, ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a ≤ a₀ → ∀ y,
      dist (wholeSpaceMollify a (fun y => G y i) y) (G y i) ≤ δ := fun i =>
    exists_forall_dist_wholeSpaceMollify_le (hGs i).continuous (hGcs i) hδ0
  choose a₀ ha₀ hclose using hex
  have hev : ∀ᶠ a in 𝓝[>] (0 : ℝ), 0 < a ∧ a ≤ 1 ∧ ∀ i, a ≤ a₀ i := by
    have h1 : ∀ᶠ a in 𝓝[>] (0 : ℝ), a ≤ 1 := by
      filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with a ha using ha.2
    have h2 : ∀ᶠ a in 𝓝[>] (0 : ℝ), ∀ i, a ≤ a₀ i := by
      rw [eventually_all]
      intro i
      filter_upwards [Ioc_mem_nhdsGT (ha₀ i)] with a ha using ha.2
    filter_upwards [self_mem_nhdsWithin, h1, h2] with a ha h1 h2 using ⟨ha, h1, h2⟩
  filter_upwards [hev] with a ⟨ha, ha1, hai⟩
  have hmv : VBdd (mollVec a F) := (vbdd_of_smooth hF hFc).mollVec ha
  have hmsm := contDiff_mollVec ha (vbdd_of_smooth hF hFc)
  have hmc := hasCompactSupport_mollVec ha (vbdd_of_smooth hF hFc)
  have h1 := coordDeriv_newtonPotential hd hmsm hmc k x
  have h2 := coordDeriv_newtonPotential hd hF hFc k x
  have hder : ∀ y, (fun i => euclideanCoordDeriv k (fun z => mollVec a F z i) y) = mollVec a G y := by
    intro y
    funext i
    have := euclideanCoordDeriv_wholeSpaceMollify (a := a) (hFs i) (hasCompactSupport_apply hFc i) k
    exact congrFun this y
  simp_rw [hder] at h1
  have h2' : euclideanCoordDeriv k (newtonPotential F) x =
      ∫ y, vecDot (newtonKernel (x - y)) (G y) := h2
  rw [h1, h2']
  have hmGsm := contDiff_mollVec ha hG
  have hmGc := hasCompactSupport_mollVec ha hG
  rw [← integral_sub (integrable_vecDot_newtonKernel_sub hd hmGsm.continuous hmGc x)
    (integrable_vecDot_newtonKernel_sub hd hGsm.continuous hGc x)]
  simp_rw [← vecDot_sub_right']
  have hb := hC (fun y => mollVec a G y - G y) (hmGsm.continuous.sub hGsm.continuous)
    (hmGc.sub hGc) δ hδ0.le (fun y i => by
      have := hclose i a ha (hai i) y
      rw [Real.dist_eq] at this
      exact this) (fun y hy => by
      funext i
      have hz : mollVec a G y = 0 := by
        funext j
        refine wholeSpaceMollify_eq_zero ha fun t ht => ?_
        have : R ≤ ‖y - t‖ := by
          have := norm_add_le t (y - t)
          simp only [add_sub_cancel] at this
          linarith
        simpa using congrFun (hR _ this) j
      simp [hz, hR y (by linarith)])
  refine hb.trans ?_
  rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

end

end PDE.NewtonWeakType
