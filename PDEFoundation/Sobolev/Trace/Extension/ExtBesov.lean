module

public import PDEFoundation.Sobolev.Trace.Defs
public import PDEFoundation.Sobolev.Trace.Smooth.GagSum

/-!
# The Besov class is a vector space

`IsBesov Ω (1 - 1/p) p` is closed under addition (triangle inequality in `L^p` and Minkowski for
the Gagliardo integrand) and scalar multiplication.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory
open scoped ENNReal NNReal

variable {d : ℕ} {Ω : Set (Vec d)}

/-- Triangle inequality for the Gagliardo integral, for `μ`-a.e. measurable functions. -/
theorem ext_gagInt_rpow_add_le (μ : Measure (Vec d)) [IsFiniteMeasure μ] {q p : ℝ} (hp : 1 ≤ p)
    {g h : Vec d → ℝ} (hg : AEMeasurable g μ) (hh : AEMeasurable h μ) :
    gagInt μ q p (g + h) ^ (1 / p) ≤ gagInt μ q p g ^ (1 / p) + gagInt μ q p h ^ (1 / p) := by
  have hae : g + h =ᵐ[μ] hg.mk g + hh.mk h := hg.ae_eq_mk.add hh.ae_eq_mk
  rw [gagInt_congr_ae hae, gagInt_congr_ae hg.ae_eq_mk, gagInt_congr_ae hh.ae_eq_mk]
  have := gagInt_rpow_sum_le μ (q := q) hp Finset.univ ![hg.mk g, hh.mk h]
    (fun i => by fin_cases i <;> simp [hg.measurable_mk, hh.measurable_mk])
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
  exact this

/-- Scaling of the Gagliardo integral. -/
theorem ext_gagInt_smul (μ : Measure (Vec d)) {q p : ℝ} (a : ℝ)
    (f : Vec d → ℝ) :
    gagInt μ q p (a • f) = ENNReal.ofReal (|a| ^ p) * gagInt μ q p f := by
  unfold gagInt
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun x => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun y => ?_
  unfold gagKernel
  have h1 : (a • f) x - (a • f) y = a * (f x - f y) := by simp [mul_sub]
  rw [h1, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), mul_div_assoc,
    ENNReal.ofReal_mul (by positivity)]

theorem ext_gagliardoSeminorm_smul (Ω : Set (Vec d)) {s p : ℝ} (hp : 0 < p) (a : ℝ)
    (f : Vec d → ℝ) :
    gagliardoSeminorm Ω s p (a • f) = ENNReal.ofReal |a| * gagliardoSeminorm Ω s p f := by
  rw [gagliardoSeminorm_eq, gagliardoSeminorm_eq, ext_gagInt_smul _ a f,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.ofReal_rpow_of_nonneg
      (by positivity) (by positivity), ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne',
    ENNReal.rpow_one]

theorem ext_gagliardoSeminorm_add_le [IsFiniteMeasure (boundarySurfaceMeasure Ω)] {s p : ℝ}
    (hp : 1 ≤ p) {g h : Vec d → ℝ} (hg : AEMeasurable g (boundarySurfaceMeasure Ω))
    (hh : AEMeasurable h (boundarySurfaceMeasure Ω)) :
    gagliardoSeminorm Ω s p (g + h) ≤ gagliardoSeminorm Ω s p g + gagliardoSeminorm Ω s p h := by
  simp only [gagliardoSeminorm_eq]
  exact ext_gagInt_rpow_add_le _ hp hg hh

theorem ext_besovNorm_add_le [IsFiniteMeasure (boundarySurfaceMeasure Ω)] {s p : ℝ}
    (hp : 1 ≤ p) {g h : Vec d → ℝ} (hg : AEMeasurable g (boundarySurfaceMeasure Ω))
    (hh : AEMeasurable h (boundarySurfaceMeasure Ω)) :
    besovNorm Ω s p (g + h) ≤ besovNorm Ω s p g + besovNorm Ω s p h := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  unfold besovNorm
  have h1 := eLpNorm_add_le (μ := boundarySurfaceMeasure Ω) (f := g) (g := h) hp1
  have h2 := ext_gagliardoSeminorm_add_le (Ω := Ω) (s := s) hp hg hh
  calc _ ≤ (eLpNorm g (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) +
        eLpNorm h (ENNReal.ofReal p) (boundarySurfaceMeasure Ω)) +
        (gagliardoSeminorm Ω s p g + gagliardoSeminorm Ω s p h) := add_le_add h1 h2
    _ = _ := by ring

theorem ext_besovNorm_smul {s p : ℝ} (hp : 0 < p) (Ω : Set (Vec d)) (a : ℝ) (f : Vec d → ℝ) :
    besovNorm Ω s p (a • f) = ENNReal.ofReal |a| * besovNorm Ω s p f := by
  unfold besovNorm
  rw [ext_gagliardoSeminorm_smul Ω hp, mul_add]
  congr 1
  have h := eLpNorm_const_smul (μ := boundarySurfaceMeasure Ω) (p := ENNReal.ofReal p) a f
  rw [h, Real.enorm_eq_ofReal_abs]

theorem IsBesov.add [IsFiniteMeasure (boundarySurfaceMeasure Ω)] {p : ℝ} (hp : 1 < p)
    {g h : Vec d → ℝ} (hg : IsBesov Ω (1 - 1 / p) p g) (hh : IsBesov Ω (1 - 1 / p) p h) :
    IsBesov Ω (1 - 1 / p) p (g + h) :=
  ⟨hg.1.add hh.1, (ext_besovNorm_add_le hp.le hg.1 hh.1).trans_lt
    (ENNReal.add_lt_top.2 ⟨hg.2, hh.2⟩)⟩

theorem IsBesov.smul {p : ℝ} (hp : 1 < p) (a : ℝ) {g : Vec d → ℝ}
    (hg : IsBesov Ω (1 - 1 / p) p g) : IsBesov Ω (1 - 1 / p) p (a • g) :=
  ⟨hg.1.const_smul a, by
    rw [ext_besovNorm_smul (by linarith) Ω a g]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.2⟩

end PDE.TraceLane
