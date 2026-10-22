module

public import PDEFoundation.Sobolev.Trace.Extension.Defs
public import PDEFoundation.Sobolev.Trace.Model.ExtShift
public import PDEFoundation.Sobolev.Trace.Assembly.Basic
public import PDEFoundation.Sobolev.Trace.Smooth.Scalar

/-!
# Shifted extensions: basic facts

The summands `ηⱼ · (modelExt n gⱼ)(φⱼ⁻¹ x + (0, s))` of the shifted extension, the `p`-th power
bound for finite sums, and the flat boundary data `gⱼ` of a Besov function: `gⱼ ∈ L^p` with finite
flat Gagliardo seminorm.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

theorem shift_measurableSet_upperHalf (m : ℕ) : MeasurableSet (upperHalf m) :=
  MeasurableSet.univ.prod measurableSet_Ioi

/-- `(∑ bᵢ)^p ≤ N^{p-1} ∑ bᵢ^p` in `[0,∞]`. -/
theorem shift_ofReal_sum_rpow_le {ι : Type*} (s : Finset ι) {p : ℝ} (hp : 1 ≤ p) (b : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) :
    ENNReal.ofReal ((∑ i ∈ s, b i) ^ p) ≤
      ENNReal.ofReal ((s.card : ℝ) ^ (p - 1)) * ∑ i ∈ s, ENNReal.ofReal (b i ^ p) := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow s b hp
  simp only [abs_of_nonneg (hb _)] at h
  refine (ENNReal.ofReal_le_ofReal h).trans ?_
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (hb i) _)]


/-- The model extension of a locally integrable function is measurable. -/
theorem measurable_modelExt_of_locallyIntegrable {m : ℕ} {w : Vec m → ℝ}
    (hw : LocallyIntegrable w volume) : Measurable (modelExt m w) := by
  classical
  have hE := (contDiffOn_modelExt hw).continuousOn
  have h : modelExt m w = (upperHalf m).piecewise (modelExt m w) (fun _ => 0) := by
    funext z
    by_cases hz : z ∈ upperHalf m
    · rw [piecewise_eq_of_mem _ _ _ hz]
    · rw [piecewise_eq_of_notMem _ _ _ hz]
      have : ¬ 0 < z.2 := fun h => hz (mem_upperHalf.2 h)
      simp [modelExt, this]
  rw [h]
  exact hE.measurable_piecewise continuousOn_const (shift_measurableSet_upperHalf m)

/-- The `i`-th summand of the shifted extension. -/
noncomputable def ExtData.term (D : ExtData Ω) (j : Fin D.A.N) (s : ℝ) (g : Vec (n + 1) → ℝ)
    (x : Vec (n + 1)) : ℝ :=
  D.η j x * modelExt n (D.flat j g) ((D.A.chart j).inv x + (0, s))

theorem ExtData.shift_eq_sum_term (D : ExtData Ω) (s : ℝ) (g : Vec (n + 1) → ℝ) :
    D.shift s g = fun x => ∑ j, D.term j s g x := rfl

theorem ExtData.shift_zero (D : ExtData Ω) (g : Vec (n + 1) → ℝ) : D.shift 0 g = D.ext g := by
  funext x
  simp only [ExtData.shift, ExtData.ext, show ((0 : Vec n), (0 : ℝ)) = 0 from rfl, add_zero]

/-- A Besov function has finite `L^p(σ)` integral. -/
theorem shift_lintegral_lt_top {p : ℝ} (hp : 1 < p) {g : Vec (n + 1) → ℝ}
    (hg : IsBesov Ω (1 - 1 / p) p g) :
    ∫⁻ x, ENNReal.ofReal (|g x| ^ p) ∂boundarySurfaceMeasure Ω < ⊤ := by
  have hp0 : 0 < p := by linarith
  rw [lintegral_ofReal_rpow_eq hp0 hg.1.aestronglyMeasurable]
  refine ENNReal.rpow_lt_top_of_nonneg hp0.le (lt_of_le_of_lt le_self_add hg.2).ne

/-- A Besov function has a finite Gagliardo double integral. -/
theorem shift_gag_lt_top {p : ℝ} (hp : 1 < p) {g : Vec (n + 1) → ℝ}
    (hg : IsBesov Ω (1 - 1 / p) p g) :
    gagliardoSeminorm Ω (1 - 1 / p) p g ^ p < ⊤ := by
  have hp0 : 0 < p := by linarith
  exact ENNReal.rpow_lt_top_of_nonneg hp0.le (lt_of_le_of_lt le_add_self hg.2).ne

theorem shift_flat_aestronglyMeasurable (φ : GraphChart Ω) {ζ : Vec (n + 1) → ℝ}
    (hζ : Continuous ζ) (hζU : tsupport ζ ⊆ φ.dom) {g : Vec (n + 1) → ℝ}
    (hg : AEMeasurable g (boundarySurfaceMeasure Ω)) :
    AEStronglyMeasurable (flatPullback φ ζ g) volume := by
  have h := flatPullback_ae_eq φ hζU (hg.ae_eq_mk)
  have hm : Measurable (flatPullback φ ζ (hg.mk g)) := by
    unfold flatPullback
    exact (hζ.measurable.comp φ.measurable_boundaryMap).mul
      (hg.measurable_mk.comp φ.measurable_boundaryMap)
  exact hm.aestronglyMeasurable.congr h.symm

/-- The flat data of a Besov function is in `L^p`. -/
theorem ExtData.flat_memLp (D : ExtData Ω) (j : Fin D.A.N) {p : ℝ} (hp : 1 < p)
    {g : Vec (n + 1) → ℝ} (hg : IsBesov Ω (1 - 1 / p) p g) :
    MemLp (D.flat j g) (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  have hζc : Continuous (D.A.ζ j) := (D.A.ζ_smooth j).continuous
  have hmeas := shift_flat_aestronglyMeasurable (D.A.chart j) hζc (D.A.ζ_tsupport j) hg.1
  obtain ⟨C, hC⟩ := flatPullback_Lp_le (D.A.chart j) hζc (D.A.ζ_compact j) (D.A.ζ_tsupport j) hp
  rw [memLp_iff]
  unfold ExtData.flat
  rw [eLpNorm_eq_lintegral_ofReal_rpow hp0 hmeas]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
  exact ((hC g hg.1).trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top (shift_lintegral_lt_top hp hg))).ne

/-- The flat data of a Besov function has finite flat Gagliardo seminorm. -/
theorem ExtData.flat_gag_ne_top (D : ExtData Ω) (j : Fin D.A.N) {p : ℝ} (hp : 1 < p)
    {g : Vec (n + 1) → ℝ} (hg : IsBesov Ω (1 - 1 / p) p g) :
    flatGagliardo n ((n : ℝ) + p - 1) p (D.flat j g) ≠ ⊤ := by
  obtain ⟨C, hC⟩ := flatPullback_gagliardo_le (D.A.chart j)
    ((D.A.ζ_smooth j).of_le (by exact_mod_cast le_top)) (D.A.ζ_compact j) (D.A.ζ_tsupport j) hp
  exact ((hC g hg.1).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top
    (ENNReal.add_lt_top.2 ⟨shift_lintegral_lt_top hp hg, shift_gag_lt_top hp hg⟩))).ne

end PDE.TraceLane
