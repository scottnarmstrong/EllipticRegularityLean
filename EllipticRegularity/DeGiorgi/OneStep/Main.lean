module

public import EllipticRegularity.DeGiorgi.OneStep.Wrap
public import EllipticRegularity.DeGiorgi.MoserIter.Hypotheses

/-!
# The three Moser one-step estimates

Proofs of the interface hypotheses `MoserOneStepHyp`, `WeakHarnackInvOneStepHyp` and
`WeakHarnackSmallOneStepHyp` of `EllipticRegularity.DeGiorgi.MoserIter.Hypotheses`.

The test function `η² u^{2σ-1}` is supported in the open ball `B_s`, so the endpoint `s = 3/4`
(resp. `s = 1`) needs no limiting argument: the cutoff `η` has `tsupport η ⊆ B_s` and the a.e.
bounds on `B_{3/4}` (resp. `B_1`) cover it.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace PDE.DGNMOneStep

open MeasureTheory PDE

theorem ball_mono_one {d : ℕ} {R : ℝ} (hR0 : 0 ≤ R) (hR : R ≤ 1) :
    euclideanBall (0 : Vec d) R ⊆ euclideanBall (0 : Vec d) 1 :=
  euclideanBall_mono hR0 hR

/-- Proposition 4.13, Step 1 (4.62). -/
theorem moserOneStep (d : ℕ) (hd : 3 ≤ d) : PDE.DGNMMoser.MoserOneStepHyp d := by
  refine ⟨oneStepConst d, oneStepConst_pos d, ?_⟩
  intro Λ a ha hEll u hsub δ M hδ hδu hMu p hp r s hr hrs hs
  have hU : IsOpenBoundedConvexDomain (euclideanBall (0 : Vec d) 1) :=
    isOpenBoundedConvexDomain_euclideanBall 0 one_pos
  have hΛ : 0 ≤ Λ :=
    (hEll 0 (center_mem_euclideanBall (0 : Vec d) one_pos)).Lam_pos.le
  have hR0 : (0 : ℝ) ≤ 3 / 4 := by norm_num
  have hRU : euclideanBall (0 : Vec d) (3 / 4) ⊆ euclideanBall (0 : Vec d) 1 :=
    ball_mono_one hR0 (by norm_num)
  obtain ⟨G₁, hG₁, hB₁, -, hp₁⟩ := exists_powerFn_twoSided hδ (le_max_right M δ) (p / 2)
  obtain ⟨G₂, hG₂, hB₂, hn₂, hp₂⟩ := exists_powerFn_twoSided hδ (le_max_right M δ) (2 * (p / 2) - 1)
  have hS : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) (3 / 4)),
      u.toFun x ∈ Set.Icc δ (max M δ) := by
    have h1 := ae_restrict_of_ae_restrict_of_subset hRU hδu
    filter_upwards [h1, hMu] with x hx1 hx2
    exact ⟨hx1, hx2.trans (le_max_left _ _)⟩
  obtain ⟨w, v, hv0, hreg⟩ := exists_wv hU u (S := Set.Icc δ (max M δ))
    (fun t ht => hδ.trans_le ht.1) (σ := p / 2) hG₁ hB₁ hG₂ hB₂ hn₂ (fun t ht => hp₁ t ht.1 ht.2)
    (fun t ht => hp₂ t ht.1 ht.2) hS
  have hpos : 0 < (1 : ℝ) * (2 * (p / 2) - 1) := by linarith
  exact finish hd hU hΛ hEll u w v (σ := p / 2) (τ := 1) (by positivity) (by norm_num) hpos hRU
    hreg (fun hη hηc hηU => htest_sub hU ha hEll hsub v hv0 hη hηc hηU) u.toFun
    (κ := p - 1) (by linarith) (by ring) (by ring) u.memL2.aestronglyMeasurable
    (by filter_upwards [hδu] with x hx using hδ.le.trans hx)
    (by filter_upwards [hreg] with x hx using hx.2.1) (by linarith) hrs hs

/-- Proposition 4.14, Step 1, negative powers (4.71). -/
theorem weakHarnackInvOneStep (d : ℕ) (hd : 3 ≤ d) :
    PDE.DGNMMoser.WeakHarnackInvOneStepHyp d := by
  refine ⟨oneStepConst d, oneStepConst_pos d, ?_⟩
  intro Λ a ha hEll u hsuper δ hδ hδu p hp r s hr hrs hs
  have hU : IsOpenBoundedConvexDomain (euclideanBall (0 : Vec d) 1) :=
    isOpenBoundedConvexDomain_euclideanBall 0 one_pos
  have hΛ : 0 ≤ Λ :=
    (hEll 0 (center_mem_euclideanBall (0 : Vec d) one_pos)).Lam_pos.le
  have hRU : euclideanBall (0 : Vec d) 1 ⊆ euclideanBall (0 : Vec d) 1 := subset_rfl
  obtain ⟨G₁, hG₁, hB₁, -, hp₁⟩ := exists_powerFn_oneSided hδ (s := -p / 2) (by linarith)
  obtain ⟨G₂, hG₂, hB₂, hn₂, hp₂⟩ := exists_powerFn_oneSided hδ (s := 2 * (-p / 2) - 1)
    (by linarith)
  have hS : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1), u.toFun x ∈ Set.Ici δ := hδu
  obtain ⟨w, v, hv0, hreg⟩ := exists_wv hU u (S := Set.Ici δ)
    (fun t ht => hδ.trans_le ht) (σ := -p / 2) hG₁ hB₁ hG₂ hB₂ hn₂ hp₁ hp₂ hS
  have hpos : 0 < (-1 : ℝ) * (2 * (-p / 2) - 1) := by linarith
  refine finish hd hU hΛ hEll u w v (σ := -p / 2) (τ := -1) (by intro h; linarith) (by norm_num)
    hpos hRU hreg
    (fun hη hηc hηU => htest_super hU ha hEll hsuper v hv0 hη hηc hηU) (fun x => (u.toFun x)⁻¹)
    (κ := 1 + p) hp (by ring) (by ring) u.memL2.aestronglyMeasurable.aemeasurable.inv.aestronglyMeasurable
    (by filter_upwards [hδu] with x hx using inv_nonneg.mpr (hδ.le.trans hx))
    ?_ (by linarith) hrs hs
  filter_upwards [hreg] with x hx
  obtain ⟨hu, hw, -⟩ := hx
  rw [hw, Real.inv_rpow hu.le, ← Real.rpow_neg hu.le]
  congr 1; ring

/-- Proposition 4.14, Step 1, small positive powers (4.72). -/
theorem weakHarnackSmallOneStep (d : ℕ) (hd : 3 ≤ d) :
    PDE.DGNMMoser.WeakHarnackSmallOneStepHyp d := by
  refine ⟨oneStepConst d, oneStepConst_pos d, ?_⟩
  intro Λ a ha hEll u hsuper δ hδ hδu p hp hp1 r s hr hrs hs
  have hU : IsOpenBoundedConvexDomain (euclideanBall (0 : Vec d) 1) :=
    isOpenBoundedConvexDomain_euclideanBall 0 one_pos
  have hΛ : 0 ≤ Λ :=
    (hEll 0 (center_mem_euclideanBall (0 : Vec d) one_pos)).Lam_pos.le
  have hRU : euclideanBall (0 : Vec d) 1 ⊆ euclideanBall (0 : Vec d) 1 := subset_rfl
  obtain ⟨G₁, hG₁, hB₁, -, hp₁⟩ := exists_powerFn_oneSided hδ (s := p / 2) (by linarith)
  obtain ⟨G₂, hG₂, hB₂, hn₂, hp₂⟩ := exists_powerFn_oneSided hδ (s := 2 * (p / 2) - 1)
    (by linarith)
  have hS : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1), u.toFun x ∈ Set.Ici δ := hδu
  obtain ⟨w, v, hv0, hreg⟩ := exists_wv hU u (S := Set.Ici δ)
    (fun t ht => hδ.trans_le ht) (σ := p / 2) hG₁ hB₁ hG₂ hB₂ hn₂ hp₁ hp₂ hS
  have hpos : 0 < (-1 : ℝ) * (2 * (p / 2) - 1) := by linarith
  exact finish hd hU hΛ hEll u w v (σ := p / 2) (τ := -1) (by positivity) (by norm_num)
    hpos hRU hreg
    (fun hη hηc hηU => htest_super hU ha hEll hsuper v hv0 hη hηc hηU) u.toFun
    (κ := 1 - p) hp (by ring) (by ring) u.memL2.aestronglyMeasurable
    (by filter_upwards [hδu] with x hx using hδ.le.trans hx)
    (by filter_upwards [hreg] with x hx using hx.2.1) (by linarith) hrs hs

end PDE.DGNMOneStep
