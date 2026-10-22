module

public import PDEFoundation.Sobolev.Trace.Assembly.TraceUnique

/-!
# The trace inequality from the smooth bound and density (manuscript Step 5)

`trace_inequality_of_props`: for `p > 1`, the smooth trace bound `SmoothTraceBound Ω p` and the
density statement `DensityProp Ω p` give existence, `σ`-a.e. uniqueness and the Besov bound of
traces of `W^{1,p}(Ω)` functions: the conclusion of the `trace_inequality`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

variable {d : ℕ} {Ω : Set (Vec d)} {p : ℝ}

/-- **Bound for every trace.** -/
theorem isTraceOf_besovNorm_le [IsFiniteMeasure (boundarySurfaceMeasure Ω)] (hΩo : IsOpen Ω)
    (hp : 1 < p) {C : ℝ≥0}
    (hS : ∀ φ : Vec d → ℝ, ContDiffOn ℝ 1 φ (closure Ω) →
      eLpNorm φ (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) ≤
          (C : ℝ≥0∞) * w1pPairNorm Ω p φ (classicalGradient φ) ∧
        gagliardoSeminorm Ω (1 - 1 / p) p φ ≤ (C : ℝ≥0∞) * w1pPairNorm Ω p φ (classicalGradient φ))
    (u : W1pFunction Ω (ENNReal.ofReal p)) {g : Vec d → ℝ} (hg : IsTraceOf Ω p u g) :
    besovNorm Ω (1 - 1 / p) p g ≤ ((2 * C : ℝ≥0) : ℝ≥0∞) * w1pNorm Ω p u := by
  obtain ⟨hgm, ψ, hψ, hψu, hψg⟩ := hg
  have hq1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  have hpair : ∀ k, w1pPairNorm Ω p (ψ k) (classicalGradient (ψ k)) ≤
      w1pPairNorm Ω p (ψ k - u.toFun) (classicalGradient (ψ k) - u.grad) + w1pNorm Ω p u :=
    fun k => w1pPairNorm_le_sub_add hΩo hp.le u (hψ k)
  have hB : Tendsto (fun k => (C : ℝ≥0∞) *
      (w1pPairNorm Ω p (ψ k - u.toFun) (classicalGradient (ψ k) - u.grad) + w1pNorm Ω p u))
      atTop (𝓝 ((C : ℝ≥0∞) * w1pNorm Ω p u)) := by
    have h := ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞))
      (hψu.add (tendsto_const_nhds (x := w1pNorm Ω p u))) (Or.inr ENNReal.coe_ne_top)
    simpa using h
  -- the `L^p` part
  have hLp : eLpNorm g (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) ≤
      (C : ℝ≥0∞) * w1pNorm Ω p u := by
    have hbound : ∀ k, eLpNorm g (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) ≤
        eLpNorm (ψ k - g) (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) + (C : ℝ≥0∞) *
          (w1pPairNorm Ω p (ψ k - u.toFun) (classicalGradient (ψ k) - u.grad) + w1pNorm Ω p u) := by
      intro k
      have e : g = -(ψ k - g) + ψ k := by abel
      calc eLpNorm g (ENNReal.ofReal p) (boundarySurfaceMeasure Ω)
          = eLpNorm (-(ψ k - g) + ψ k) (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) := by
            rw [← e]
        _ ≤ eLpNorm (-(ψ k - g)) (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) +
            eLpNorm (ψ k) (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) := eLpNorm_add_le hq1
        _ ≤ _ := by
            rw [eLpNorm_neg]
            refine add_le_add le_rfl ((hS _ (hψ k)).1.trans ?_)
            gcongr
            exact hpair k
    have hlim := hψg.add hB
    rw [zero_add] at hlim
    exact ge_of_tendsto' hlim hbound
  -- the seminorm part
  have hgag : gagliardoSeminorm Ω (1 - 1 / p) p g ≤ (C : ℝ≥0∞) * w1pNorm Ω p u := by
    have hq0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
    have hmeas : ∀ k, AEStronglyMeasurable (ψ k) (boundarySurfaceMeasure Ω) := fun k =>
      aestronglyMeasurable_of_continuousOn_closure (hψ k).continuousOn
    have hin := tendstoInMeasure_of_tendsto_eLpNorm hq0 hψg
    obtain ⟨ns, hns, hae⟩ := hin.exists_seq_tendsto_ae
    refine gagliardoSeminorm_le_of_tendsto (by linarith) (f := fun i => ψ (ns i))
      (fun i => (hmeas (ns i)).aemeasurable) hae (hB.comp hns.tendsto_atTop) fun i => ?_
    refine (hS _ (hψ (ns i))).2.trans ?_
    show _ ≤ (C : ℝ≥0∞) * (w1pPairNorm Ω p (ψ (ns i) - u.toFun)
      (classicalGradient (ψ (ns i)) - u.grad) + w1pNorm Ω p u)
    gcongr
    exact hpair (ns i)
  unfold besovNorm
  calc eLpNorm g (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) + gagliardoSeminorm Ω (1 - 1 / p) p g
      ≤ (C : ℝ≥0∞) * w1pNorm Ω p u + (C : ℝ≥0∞) * w1pNorm Ω p u := add_le_add hLp hgag
    _ = ((2 * C : ℝ≥0) : ℝ≥0∞) * w1pNorm Ω p u := by
        push_cast
        ring

/-- **Existence of a trace.** -/
theorem exists_isTraceOf (hΩo : IsOpen Ω) (hp : 1 < p) {C : ℝ≥0}
    (hS : ∀ φ : Vec d → ℝ, ContDiffOn ℝ 1 φ (closure Ω) →
      eLpNorm φ (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) ≤
        (C : ℝ≥0∞) * w1pPairNorm Ω p φ (classicalGradient φ))
    (hD : DensityProp Ω p) (u : W1pFunction Ω (ENNReal.ofReal p)) : ∃ g, IsTraceOf Ω p u g := by
  obtain ⟨φ, hφ, hφu⟩ := hD u
  have hq1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  have hφc : ∀ k, ContDiffOn ℝ 1 (φ k) (closure Ω) := fun k => (hφ k).contDiffOn
  set b : ℕ → ℝ≥0∞ := fun k =>
    w1pPairNorm Ω p (φ k - u.toFun) (classicalGradient (φ k) - u.grad) with hb
  set δ : ℕ → ℝ≥0∞ := fun k => (2⁻¹ : ℝ≥0∞) ^ k / ((C : ℝ≥0∞) + 1) with hδ
  have hδpos : ∀ k, 0 < δ k := fun k =>
    ENNReal.div_pos (pow_ne_zero _ (by simp)) (by simp)
  have hδle : ∀ k, (C : ℝ≥0∞) * δ k ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
    intro k
    rw [hδ, ← mul_div_assoc, mul_comm, mul_div_assoc]
    calc (2⁻¹ : ℝ≥0∞) ^ k * ((C : ℝ≥0∞) / ((C : ℝ≥0∞) + 1)) ≤ (2⁻¹ : ℝ≥0∞) ^ k * 1 := by
          gcongr
          exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact le_self_add)
      _ = _ := mul_one _
  choose ns hns using fun k => (hφu.eventually (gt_mem_nhds (hδpos k))).exists
  set f : ℕ → Vec d → ℝ := fun k => φ (ns k) with hf
  have hfc : ∀ k, ContDiffOn ℝ 1 (f k) (closure Ω) := fun k => hφc (ns k)
  have hδtop : ∀ k, δ k < ⊤ := fun k =>
    ENNReal.div_lt_top (ENNReal.pow_ne_top (by simp)) (by simp)
  have hpairf : ∀ k, w1pPairNorm Ω p (f k) (classicalGradient (f k)) ≤
      b (ns k) + w1pNorm Ω p u := fun k => w1pPairNorm_le_sub_add hΩo hp.le u (hfc k)
  have hfmem : ∀ k, MemLp (f k) (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) := by
    intro k
    have h1 : eLpNorm (f k) (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) ≤
        (C : ℝ≥0∞) * (b (ns k) + w1pNorm Ω p u) := by
      refine (hS _ (hfc k)).trans ?_
      gcongr
      exact hpairf k
    exact lt_of_le_of_lt h1 (ENNReal.mul_lt_top ENNReal.coe_lt_top
      (ENNReal.add_lt_top.2 ⟨(hns k).trans (hδtop k), w1pNorm_lt_top u⟩))
  have hδanti : ∀ N n, N ≤ n → δ n ≤ δ N := by
    intro N n hNn
    simp only [hδ]
    exact ENNReal.div_le_div_right (pow_le_pow_right_of_le_one' (by norm_num) hNn) _
  set B : ℕ → ℝ≥0∞ := fun N => 4 * (2⁻¹ : ℝ≥0∞) ^ N with hB
  have hBsum : ∑' i, B i ≠ ⊤ := by
    simp only [hB, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    refine ENNReal.mul_ne_top (by norm_num) ?_
    rw [ENNReal.one_sub_inv_two, inv_inv]
    norm_num
  have hcau : ∀ N n m : ℕ, N ≤ n → N ≤ m →
      eLpNorm (f n - f m) (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) < B N := by
    intro N n m hn hm
    have h1 : eLpNorm (f n - f m) (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) ≤
        (C : ℝ≥0∞) * (b (ns n) + b (ns m)) :=
      (hS _ ((hfc n).sub (hfc m))).trans (by
        gcongr
        exact w1pPairNorm_sub_sub_le hΩo hp.le u (hfc n) (hfc m))
    have h2 : (C : ℝ≥0∞) * (b (ns n) + b (ns m)) ≤ 2 * (2⁻¹ : ℝ≥0∞) ^ N := by
      calc (C : ℝ≥0∞) * (b (ns n) + b (ns m)) ≤ (C : ℝ≥0∞) * (δ N + δ N) := by
            gcongr
            · exact (hns n).le.trans (hδanti N n hn)
            · exact (hns m).le.trans (hδanti N m hm)
        _ = 2 * ((C : ℝ≥0∞) * δ N) := by ring
        _ ≤ 2 * (2⁻¹ : ℝ≥0∞) ^ N := by gcongr; exact hδle N
    have hpos : (2⁻¹ : ℝ≥0∞) ^ N ≠ 0 := pow_ne_zero _ (by simp)
    have hfin : (2⁻¹ : ℝ≥0∞) ^ N ≠ ⊤ := ENNReal.pow_ne_top (by simp)
    refine lt_of_le_of_lt (h1.trans h2) ?_
    have h2x : (2 : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ N ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hfin
    have h2x0 : (2 : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ N ≠ 0 := mul_ne_zero (by norm_num) hpos
    have h4 : B N = 2 * (2⁻¹ : ℝ≥0∞) ^ N + 2 * (2⁻¹ : ℝ≥0∞) ^ N := by
      simp only [hB]; rw [← two_mul, ← mul_assoc]; norm_num
    rw [h4]
    exact ENNReal.lt_add_right h2x h2x0
  obtain ⟨g, hgmem, hglim⟩ := MeasureTheory.Lp.cauchy_complete_eLpNorm hq1 hfmem hBsum hcau
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.div_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (r := (2⁻¹ : ℝ≥0∞)) (by norm_num)) (Or.inr (by simp : (C : ℝ≥0∞) + 1 ≠ 0))
    simpa [hδ] using h
  refine ⟨g, hgmem, f, hfc, ?_, hglim⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hδlim (fun _ => bot_le)
    fun k => (hns k).le

/-- **Trace inequality** (manuscript Step 5), from the smooth trace bound and density. -/
theorem trace_inequality_of_props [IsFiniteMeasure (boundarySurfaceMeasure Ω)] (hΩo : IsOpen Ω)
    (hp : 1 < p) (hS : SmoothTraceBound Ω p) (hD : DensityProp Ω p) :
    ∃ C : ℝ≥0, ∀ u : W1pFunction Ω (ENNReal.ofReal p),
      (∃ g, IsTraceOf Ω p u g) ∧
      (∀ g g', IsTraceOf Ω p u g → IsTraceOf Ω p u g' →
        g =ᵐ[boundarySurfaceMeasure Ω] g') ∧
      ∀ g, IsTraceOf Ω p u g →
        besovNorm Ω (1 - 1 / p) p g ≤ (C : ℝ≥0∞) * w1pNorm Ω p u := by
  obtain ⟨C, hC⟩ := hS
  refine ⟨2 * C, fun u => ⟨exists_isTraceOf hΩo hp (fun φ hφ => (hC φ hφ).1) hD u,
    fun g g' hg hg' => isTraceOf_ae_unique hΩo hp (fun φ hφ => (hC φ hφ).1) u hg hg',
    fun g hg => isTraceOf_besovNorm_le hΩo hp hC u hg⟩⟩

end PDE.TraceLane
