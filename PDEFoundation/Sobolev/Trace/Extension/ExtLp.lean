module

public import PDEFoundation.Sobolev.Trace.Extension.ExtTransfer
public import PDEFoundation.Sobolev.Trace.Extension.Flat
public import PDEFoundation.Sobolev.Trace.Model.Ext
import PDEFoundation.Sobolev.Trace.Smooth.Scalar

/-!
# The `L^p` bound of one summand's majorant by the Besov norm

For a chart `j`, the `L^p(Ω)` norm of the majorant `K (|F| + |∇F|) ∘ φⱼ⁻¹` (with
`F = modelExt n (flat j g)`) is bounded by a constant times the Besov norm of `g`: change variables
to the half-space, apply the half-space bound for `modelExt`, and then the flat transfer bounds.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

theorem ext_ofReal_add_rpow_le {p a b : ℝ} (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal ((a + b) ^ p) ≤
      ENNReal.ofReal (2 ^ (p - 1)) * (ENNReal.ofReal (a ^ p) + ENNReal.ofReal (b ^ p)) := by
  have hp0 : 0 ≤ p := by linarith
  rw [← ENNReal.ofReal_rpow_of_nonneg (add_nonneg ha hb) hp0, ENNReal.ofReal_add ha hb]
  refine (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp).trans ?_
  rw [ENNReal.ofReal_rpow_of_nonneg ha hp0, ENNReal.ofReal_rpow_of_nonneg hb hp0,
    show (2 : ℝ≥0∞) ^ (p - 1) = ENNReal.ofReal (2 ^ (p - 1)) by
      rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by linarith)]; simp]

/-- The `p`-th power of `K (|F| + |∇F|)` is controlled by the two pieces. -/
theorem ext_ofReal_scaled_rpow_le {p K a b : ℝ} (hp : 1 ≤ p) (hK : 0 ≤ K) (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    ENNReal.ofReal ((K * (a + b)) ^ p) ≤
      ENNReal.ofReal (K ^ p) * (ENNReal.ofReal (2 ^ (p - 1)) *
        (ENNReal.ofReal (a ^ p) + ENNReal.ofReal (b ^ p))) := by
  rw [Real.mul_rpow hK (add_nonneg ha hb), ENNReal.ofReal_mul (Real.rpow_nonneg hK _)]
  exact mul_le_mul' le_rfl (ext_ofReal_add_rpow_le hp ha hb)

/-- The `p`-th power integral of the majorant is bounded by the Besov data of `g`. -/
theorem ExtData.lintegral_majorant_le (D : ExtData Ω) {p : ℝ} (hp : 1 < p) (j : Fin D.A.N)
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ C : ℝ≥0, ∀ g : Vec (n + 1) → ℝ, IsBesov Ω (1 - 1 / p) p g →
      ∫⁻ x in Ω, ENNReal.ofReal
          (D.majorant j K (modelExt n (D.flat j g)) x ^ p) ≤
        C * (∫⁻ x, ENNReal.ofReal (|g x| ^ p) ∂boundarySurfaceMeasure Ω +
          gagliardoSeminorm Ω (1 - 1 / p) p g ^ p) := by
  obtain ⟨CM, hCM⟩ := modelExt_bound n hp
  obtain ⟨C1, hC1⟩ := flatPullback_Lp_le (D.A.chart j) (D.contDiff_ζ j).continuous
    (D.A.ζ_compact j) (D.A.ζ_tsupport j) hp
  obtain ⟨C2, hC2⟩ := flatPullback_gagliardo_le (D.A.chart j) (D.contDiff_ζ j)
    (D.A.ζ_compact j) (D.A.ζ_tsupport j) hp
  have hp0 : 0 < p := by linarith
  refine ⟨CM * Real.toNNReal (K ^ p) * Real.toNNReal (2 ^ (p - 1)) * (C1 + C2), fun g hg => ?_⟩
  set F := modelExt n (D.flat j g) with hFdef
  have hmem := D.memLp_flat j hp hg
  have hF : ContDiffOn ℝ 1 F (upperHalf n) := modelExt_contDiffOn hp _ hmem
  set A := ∫⁻ x, ENNReal.ofReal (|g x| ^ p) ∂boundarySurfaceMeasure Ω with hA
  set Gp := gagliardoSeminorm Ω (1 - 1 / p) p g ^ p with hGp
  have h1 : ∫⁻ x in Ω, ENNReal.ofReal (D.majorant j K F x ^ p) ≤
      ∫⁻ z in upperHalf n, ENNReal.ofReal ((K * (|F z| + modelGradNorm F z)) ^ p) :=
    ext_lintegral_majorant_le (D.A.chart j) hp0 (fun z => K * (|F z| + modelGradNorm F z))
  have h2 : ∫⁻ z in upperHalf n, ENNReal.ofReal ((K * (|F z| + modelGradNorm F z)) ^ p) ≤
      ENNReal.ofReal (K ^ p) * (ENNReal.ofReal (2 ^ (p - 1)) *
        ∫⁻ z in upperHalf n, (ENNReal.ofReal (|F z| ^ p) +
          ENNReal.ofReal (modelGradNorm F z ^ p))) := by
    calc _ ≤ ∫⁻ z in upperHalf n, ENNReal.ofReal (K ^ p) * (ENNReal.ofReal (2 ^ (p - 1)) *
          (ENNReal.ofReal (|F z| ^ p) + ENNReal.ofReal (modelGradNorm F z ^ p))) :=
          lintegral_mono fun z => ext_ofReal_scaled_rpow_le hp.le hK (abs_nonneg _)
            (Real.sqrt_nonneg _)
      _ = _ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have h3 := hCM (D.flat j g) hmem
  have h4 := hC1 g hg.1
  have h5 := hC2 g hg.1
  have h6 : (∫⁻ x', ENNReal.ofReal (|D.flat j g x'| ^ p)) +
      flatGagliardo n ((n : ℝ) + p - 1) p (D.flat j g) ≤ ((C1 : ℝ≥0∞) + C2) * (A + Gp) := by
    calc _ ≤ C1 * A + C2 * (A + Gp) := add_le_add h4 h5
      _ ≤ C1 * (A + Gp) + C2 * (A + Gp) := by gcongr; exact le_self_add
      _ = _ := by rw [add_mul]
  calc _ ≤ _ := h1.trans h2
    _ ≤ ENNReal.ofReal (K ^ p) * (ENNReal.ofReal (2 ^ (p - 1)) *
          (CM * (((C1 : ℝ≥0∞) + C2) * (A + Gp)))) := by
        gcongr
        exact h3.trans (by gcongr)
    _ = _ := by
        push_cast
        simp only [ENNReal.ofReal]
        ring

/-- The `L^p(Ω)` norm of the majorant is bounded by the Besov norm of `g`. -/
theorem ExtData.eLpNorm_majorant_le (D : ExtData Ω) {p : ℝ} (hp : 1 < p) (j : Fin D.A.N)
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ C : ℝ≥0, ∀ g : Vec (n + 1) → ℝ, IsBesov Ω (1 - 1 / p) p g →
      eLpNorm (D.majorant j K (modelExt n (D.flat j g))) (ENNReal.ofReal p) (volumeOn Ω) ≤
        C * besovNorm Ω (1 - 1 / p) p g := by
  obtain ⟨C, hC⟩ := D.lintegral_majorant_le hp j hK
  have hp0 : 0 < p := by linarith
  refine ⟨C ^ (1 / p), fun g hg => ?_⟩
  have hmem := D.memLp_flat j hp hg
  have hF : ContDiffOn ℝ 1 (modelExt n (D.flat j g)) (upperHalf n) :=
    modelExt_contDiffOn hp _ hmem
  rw [eLpNorm_eq_lintegral_ofReal_rpow hp0 (D.aestronglyMeasurable_majorant j K hF)]
  have h1 : ∫⁻ x, ENNReal.ofReal (|D.majorant j K (modelExt n (D.flat j g)) x| ^ p) ∂volumeOn Ω =
      ∫⁻ x in Ω, ENNReal.ofReal (D.majorant j K (modelExt n (D.flat j g)) x ^ p) := by
    refine lintegral_congr fun x => ?_
    rw [abs_of_nonneg (D.majorant_nonneg j hK _ x)]
  rw [h1]
  have hA : (∫⁻ x, ENNReal.ofReal (|g x| ^ p) ∂boundarySurfaceMeasure Ω) ^ (1 / p) =
      eLpNorm g (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) :=
    (eLpNorm_eq_lintegral_ofReal_rpow hp0 hg.1.aestronglyMeasurable).symm
  have hG : (gagliardoSeminorm Ω (1 - 1 / p) p g ^ p) ^ (1 / p) =
      gagliardoSeminorm Ω (1 - 1 / p) p g := by
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]
  calc _ ≤ ((C : ℝ≥0∞) * (∫⁻ x, ENNReal.ofReal (|g x| ^ p) ∂boundarySurfaceMeasure Ω +
          gagliardoSeminorm Ω (1 - 1 / p) p g ^ p)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (hC g hg) (by positivity)
    _ = (C : ℝ≥0∞) ^ (1 / p) * (∫⁻ x, ENNReal.ofReal (|g x| ^ p) ∂boundarySurfaceMeasure Ω +
          gagliardoSeminorm Ω (1 - 1 / p) p g ^ p) ^ (1 / p) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ ≤ (C : ℝ≥0∞) ^ (1 / p) * ((∫⁻ x, ENNReal.ofReal (|g x| ^ p) ∂boundarySurfaceMeasure Ω) ^
          (1 / p) + (gagliardoSeminorm Ω (1 - 1 / p) p g ^ p) ^ (1 / p)) := by
        gcongr
        exact ENNReal.rpow_add_le_add_rpow _ _ (by positivity) (by
          rw [div_le_one hp0]; exact hp.le)
    _ = _ := by
        rw [hA, hG, ENNReal.coe_rpow_of_nonneg _ (by positivity)]
        rfl

end PDE.TraceLane
