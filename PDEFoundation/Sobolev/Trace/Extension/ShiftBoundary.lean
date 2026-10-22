module

public import PDEFoundation.Sobolev.Trace.Extension.ShiftSmooth
public import PDEFoundation.Sobolev.Trace.Smooth.Sigma

/-!
# Shifted extensions converge to `g` in `L^p(∂Ω)`

On `∂Ω` we have `g = ∑ⱼ ηⱼ ζⱼ g`, and on `∂Ω ∩ domⱼ` the point `x = Ψⱼ(x', 0)` has
`ζⱼ g (x) = gⱼ(x')` and `φⱼ⁻¹ x = (x', 0)`.  The `p`-th power of the error is therefore bounded
by `∑ⱼ cⱼ ∫ |Fⱼ(x', τ) - gⱼ(x')|^p dx'`, which tends to zero by `modelExt_tendsto_boundary`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

theorem ExtData.eta_mul_zeta (D : ExtData Ω) (j : Fin D.A.N) (x : Vec (n + 1)) :
    D.η j x * D.A.ζ j x = D.A.ζ j x := by
  by_cases hx : x ∈ tsupport (D.A.ζ j)
  · rw [D.η_one j x hx, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

theorem ExtData.shift_sub_eq_sum_frontier (D : ExtData Ω) {x : Vec (n + 1)}
    (hx : x ∈ frontier Ω) (τ : ℝ) (g : Vec (n + 1) → ℝ) :
    D.shift τ g x - g x = ∑ j, D.η j x *
      (modelExt n (D.flat j g) ((D.A.chart j).inv x + (0, τ)) - D.A.ζ j x * g x) := by
  have h1 : g x = ∑ j, D.η j x * (D.A.ζ j x * g x) := by
    have : ∑ j, D.η j x * (D.A.ζ j x * g x) = ∑ j, D.A.ζ j x * g x := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mul_assoc, D.eta_mul_zeta]
    rw [this, ← Finset.sum_mul, D.A.sum_eq_one x (D.A.frontier_subset hx), one_mul]
  conv_lhs => rw [h1]
  simp only [ExtData.shift, mul_sub, Finset.sum_sub_distrib]

/-- The `j`-th boundary integrand, cut off to the chart cylinder. -/
noncomputable def shiftBd (D : ExtData Ω) (j : Fin D.A.N) (p τ : ℝ) (g : Vec (n + 1) → ℝ)
    (x : Vec (n + 1)) : ℝ≥0∞ :=
  (D.A.chart j).dom.indicator (fun x => ENNReal.ofReal
    (|modelExt n (D.flat j g) ((D.A.chart j).inv x + (0, τ)) - D.A.ζ j x * g x| ^ p)) x

theorem ExtData.ofReal_abs_term_le (D : ExtData Ω) (j : Fin D.A.N) {M p : ℝ} (hp : 0 < p)
    (hM : ∀ y, |D.η j y| ≤ M) (τ : ℝ) (g : Vec (n + 1) → ℝ) (x : Vec (n + 1)) :
    ENNReal.ofReal (|D.η j x * (modelExt n (D.flat j g) ((D.A.chart j).inv x + (0, τ)) -
        D.A.ζ j x * g x)| ^ p) ≤ ENNReal.ofReal (M ^ p) * shiftBd D j p τ g x := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  by_cases hx : x ∈ (D.A.chart j).dom
  · simp only [shiftBd, indicator_of_mem hx]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hM0 _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.mul_rpow hM0 (abs_nonneg _)]
    refine Real.rpow_le_rpow (abs_nonneg _) ?_ hp.le
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
  · have : x ∉ tsupport (D.η j) := fun h => hx (D.η_tsupport j h)
    rw [image_eq_zero_of_notMem_tsupport this]
    simp [Real.zero_rpow hp.ne']

theorem ExtData.shiftBd_aemeasurable (D : ExtData Ω) (j : Fin D.A.N) {p : ℝ} (hp : 1 < p)
    {g : Vec (n + 1) → ℝ} (hg : IsBesov Ω (1 - 1 / p) p g) (τ : ℝ) :
    AEMeasurable (shiftBd D j p τ g) (boundarySurfaceMeasure Ω) := by
  unfold shiftBd
  refine AEMeasurable.indicator ?_ (D.A.chart j).isOpen_dom.measurableSet
  have hF : Measurable fun x => modelExt n (D.flat j g) ((D.A.chart j).inv x + (0, τ)) :=
    (measurable_modelExt_of_locallyIntegrable (D.locallyIntegrable_flat j hp hg)).comp
      (((D.A.chart j).contDiff_inv.continuous.add continuous_const).measurable)
  have hζ : Measurable (D.A.ζ j) := (D.A.ζ_smooth j).continuous.measurable
  exact ENNReal.measurable_ofReal.comp_aemeasurable
    ((continuous_abs.measurable.comp_aemeasurable
      (hF.aemeasurable.sub (hζ.aemeasurable.mul hg.1))).pow_const p)

theorem ExtData.shiftBd_map_le (D : ExtData Ω) (j : Fin D.A.N) (p τ : ℝ) (g : Vec (n + 1) → ℝ)
    (x' : Vec n) :
    shiftBd D j p τ g ((D.A.chart j).map (x', 0)) ≤
      ENNReal.ofReal (|modelExt n (D.flat j g) (x', τ) - D.flat j g x'| ^ p) := by
  unfold shiftBd
  refine (indicator_le_self' (fun _ _ => zero_le) _).trans ?_
  rw [(D.A.chart j).inv_map]
  refine le_of_eq ?_
  have : ((x', (0 : ℝ)) : Vec n × ℝ) + ((0 : Vec n), τ) = (x', τ) := by ext <;> simp
  rw [this]
  rfl


/-- Pointwise bound for the boundary error. -/
theorem ExtData.ofReal_abs_shift_sub_le (D : ExtData Ω) {p : ℝ} (hp : 1 < p) {M : Fin D.A.N → ℝ}
    (hM : ∀ j y, |D.η j y| ≤ M j) {x : Vec (n + 1)} (hx : x ∈ frontier Ω) (τ : ℝ)
    (g : Vec (n + 1) → ℝ) :
    ENNReal.ofReal (|D.shift τ g x - g x| ^ p) ≤ ENNReal.ofReal ((D.A.N : ℝ) ^ (p - 1)) *
      ∑ j, ENNReal.ofReal (M j ^ p) * shiftBd D j p τ g x := by
  rw [D.shift_sub_eq_sum_frontier hx]
  refine le_trans ?_ (mul_le_mul' le_rfl
    (Finset.sum_le_sum fun j _ => D.ofReal_abs_term_le j (by linarith) (hM j) τ g x))
  have h := shift_ofReal_sum_rpow_le (Finset.univ : Finset (Fin D.A.N)) hp.le
    (fun j => |D.η j x * (modelExt n (D.flat j g) ((D.A.chart j).inv x + (0, τ)) -
      D.A.ζ j x * g x)|) (fun j => abs_nonneg _)
  rw [Finset.card_univ, Fintype.card_fin] at h
  refine le_trans (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (abs_nonneg _)
    (Finset.abs_sum_le_sum_abs _ _) (by linarith))) h

theorem ExtData.exists_boundary_bound (D : ExtData Ω) {p : ℝ} (hp : 1 < p)
    {g : Vec (n + 1) → ℝ} (hg : IsBesov Ω (1 - 1 / p) p g) :
    ∃ c : Fin D.A.N → ℝ≥0∞, (∀ j, c j ≠ ⊤) ∧ ∀ τ : ℝ,
      ∫⁻ x, ENNReal.ofReal (|D.shift τ g x - g x| ^ p) ∂boundarySurfaceMeasure Ω ≤
        ∑ j, c j * ∫⁻ x', ENNReal.ofReal
          (|modelExt n (D.flat j g) (x', τ) - D.flat j g x'| ^ p) := by
  have hM : ∀ j, ∃ M : ℝ, 0 ≤ M ∧ ∀ X, |D.η j X| ≤ M := fun j =>
    exists_abs_le_of_hasCompactSupport (D.η_smooth j).continuous (D.η_compact j)
  choose M hM0 hM using hM
  refine ⟨fun j => ENNReal.ofReal ((D.A.N : ℝ) ^ (p - 1)) *
    (ENNReal.ofReal (M j ^ p) * surfConst (D.A.chart j)), fun j => ?_, fun τ => ?_⟩
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (surfConst_ne_top _))
  have hae : ∀ᵐ x ∂boundarySurfaceMeasure Ω, x ∈ frontier Ω := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (boundarySurfaceMeasure_compl_frontier (Ω := Ω))] with x hx
    simpa using hx
  calc ∫⁻ x, ENNReal.ofReal (|D.shift τ g x - g x| ^ p) ∂boundarySurfaceMeasure Ω
      ≤ ∫⁻ x, ENNReal.ofReal ((D.A.N : ℝ) ^ (p - 1)) *
          ∑ j, ENNReal.ofReal (M j ^ p) * shiftBd D j p τ g x ∂boundarySurfaceMeasure Ω :=
        lintegral_mono_ae (hae.mono fun x hx => D.ofReal_abs_shift_sub_le hp hM hx τ g)
    _ = ENNReal.ofReal ((D.A.N : ℝ) ^ (p - 1)) *
          ∑ j, ENNReal.ofReal (M j ^ p) * ∫⁻ x, shiftBd D j p τ g x ∂boundarySurfaceMeasure Ω := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum' _ fun j _ => (D.shiftBd_aemeasurable j hp hg τ).const_mul _]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal ((D.A.N : ℝ) ^ (p - 1)) *
          ∑ j, ENNReal.ofReal (M j ^ p) * (surfConst (D.A.chart j) * ∫⁻ x', ENNReal.ofReal
            (|modelExt n (D.flat j g) (x', τ) - D.flat j g x'| ^ p)) := by
        gcongr with j
        refine (lintegral_sigma_le (D.A.chart j) _ fun x hx => ?_).trans ?_
        · simp [shiftBd, indicator_of_notMem hx]
        · gcongr
          exact D.shiftBd_map_le j p τ g x'
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring


theorem tendsto_shift_inv_nhdsGT :
    Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall fun k => by simp only [mem_Ioi]; positivity⟩

/-- The shifted extensions converge to `g` in `L^p(∂Ω)`. -/
theorem ExtData.tendsto_shift_boundary (D : ExtData Ω) (_hΩo : IsOpen Ω)
    (_hΩb : Bornology.IsBounded Ω) {p : ℝ} (hp : 1 < p) {g : Vec (n + 1) → ℝ}
    (hg : IsBesov Ω (1 - 1 / p) p g) :
    Tendsto (fun k : ℕ => eLpNorm (D.shift (1 / ((k : ℝ) + 1)) g - g) (ENNReal.ofReal p)
      (boundarySurfaceMeasure Ω)) atTop (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨c, hc, hbound⟩ := D.exists_boundary_bound hp hg
  have hB : ∀ j : Fin D.A.N, Tendsto (fun k : ℕ => ∫⁻ x', ENNReal.ofReal
      (|modelExt n (D.flat j g) (x', 1 / ((k : ℝ) + 1)) - D.flat j g x'| ^ p)) atTop (𝓝 0) :=
    fun j => (modelExt_tendsto_boundary hp (D.flat_memLp j hp hg)).comp tendsto_shift_inv_nhdsGT
  have hsum : Tendsto (fun k : ℕ => ∑ j, c j * ∫⁻ x', ENNReal.ofReal
      (|modelExt n (D.flat j g) (x', 1 / ((k : ℝ) + 1)) - D.flat j g x'| ^ p)) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin D.A.N)) fun j _ =>
      ENNReal.Tendsto.const_mul (hB j) (Or.inr (hc j))
    simpa using this
  have hI : Tendsto (fun k : ℕ => ∫⁻ x, ENNReal.ofReal
      (|D.shift (1 / ((k : ℝ) + 1)) g x - g x| ^ p) ∂boundarySurfaceMeasure Ω) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
      (fun k => hbound _)
  have hpow := (ENNReal.continuous_rpow_const (y := 1 / p)).tendsto 0 |>.comp hI
  rw [ENNReal.zero_rpow_of_pos (by positivity)] at hpow
  refine hpow.congr fun k => ?_
  have hτ : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  have hmeas : AEStronglyMeasurable (D.shift (1 / ((k : ℝ) + 1)) g - g)
      (boundarySurfaceMeasure Ω) :=
    (aestronglyMeasurable_of_continuousOn_closure
      (D.shift_contDiffOn hp hg hτ).continuousOn).sub hg.1.aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_ofReal_rpow hp0 hmeas]
  rfl

end PDE.TraceLane
