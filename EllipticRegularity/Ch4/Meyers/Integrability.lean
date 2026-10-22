module

public import EllipticRegularity.Ch4.Meyers.Elliptic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Local integrability of `s^{-e}` near the codimension-two set `{s = 0}`
-/

@[expose] public section

namespace PDE.Ch4Meyers

open MeasureTheory Set

variable {d : ℕ} {w : Fin d → ℝ}

theorem measurable_axisSq (w : Fin d → ℝ) : Measurable (axisSq w) :=
  (contDiff_axisSq w).continuous.measurable

/-- One-dimensional model: `|t|^{-e}` is integrable on `[-R, R]` for `e < 1`. -/
theorem integrable_indicator_abs_rpow_neg {e : ℝ} (he1 : e < 1) (R : ℝ) :
    Integrable ((Icc (-R) R).indicator fun t : ℝ => |t| ^ (-e)) := by
  have h1 : Integrable ((Icc 0 R).indicator fun t : ℝ => t ^ (-e)) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := R) (r := -e)
      (by linarith)).1
    rw [IntegrableOn, Measure.restrict_congr_set Ioc_ae_eq_Icc] at this
    exact this
  have h2 : Integrable (fun t : ℝ => ((Icc 0 R).indicator fun t : ℝ => t ^ (-e)) (-t)) :=
    h1.comp_neg
  refine (h1.add h2).mono' ?_ ?_
  · exact ((continuous_abs.measurable.pow_const (-e)).indicator measurableSet_Icc).aestronglyMeasurable
  · refine ae_of_all _ fun t => ?_
    by_cases ht : t ∈ Icc (-R) R
    · rw [indicator_of_mem ht]
      rcases le_or_gt 0 t with h0 | h0
      · have : t ∈ Icc 0 R := ⟨h0, ht.2⟩
        simp only [Pi.add_apply, indicator_of_mem this, abs_of_nonneg h0, Real.norm_eq_abs]
        have hn : 0 ≤ ((Icc 0 R).indicator fun t : ℝ => t ^ (-e)) (-t) :=
          indicator_nonneg (fun s hs => Real.rpow_nonneg hs.1 _) _
        rw [abs_of_nonneg (Real.rpow_nonneg h0 _)]
        linarith
      · have : -t ∈ Icc 0 R := ⟨by linarith, by linarith [ht.1]⟩
        simp only [Pi.add_apply, indicator_of_mem this, abs_of_neg h0, Real.norm_eq_abs]
        have hn : 0 ≤ ((Icc 0 R).indicator fun t : ℝ => t ^ (-e)) t :=
          indicator_nonneg (fun s hs => Real.rpow_nonneg hs.1 _) _
        rw [abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
        linarith
    · rw [indicator_of_notMem ht]
      simp only [norm_zero]
      have hn1 : 0 ≤ ((Icc 0 R).indicator fun t : ℝ => t ^ (-e)) t :=
        indicator_nonneg (fun s hs => Real.rpow_nonneg hs.1 _) _
      have hn2 : 0 ≤ ((Icc 0 R).indicator fun t : ℝ => t ^ (-e)) (-t) :=
        indicator_nonneg (fun s hs => Real.rpow_nonneg hs.1 _) _
      simp only [Pi.add_apply]
      linarith

theorem sq_rpow_neg_half (x e : ℝ) : (x ^ 2) ^ (-e / 2) = |x| ^ (-e) := by
  rw [← sq_abs x, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
  congr 1
  push_cast
  ring

/-- Pointwise domination of `s^{-e}` by the product of two one-dimensional singularities. -/
theorem axisSq_rpow_neg_le (hw : ∀ i, w i = 0 ∨ w i = 1) {i0 i1 : Fin d}
    (h0 : w i0 = 1) (h1 : w i1 = 1) {e : ℝ} (he0 : 0 ≤ e) {x : Vec d}
    (hx0 : x i0 ≠ 0) (hx1 : x i1 ≠ 0) :
    axisSq w x ^ (-e) ≤ |x i0| ^ (-e) * |x i1| ^ (-e) := by
  have hs0 : 0 < x i0 ^ 2 := by positivity
  have hs1 : 0 < x i1 ^ 2 := by positivity
  have hs : 0 < axisSq w x := lt_of_lt_of_le hs0 (sq_le_axisSq hw x h0)
  have hneg : -e / 2 ≤ 0 := by linarith
  have a0 : axisSq w x ^ (-e / 2) ≤ |x i0| ^ (-e) := by
    rw [← sq_rpow_neg_half]
    exact Real.rpow_le_rpow_of_nonpos hs0 (sq_le_axisSq hw x h0) hneg
  have a1 : axisSq w x ^ (-e / 2) ≤ |x i1| ^ (-e) := by
    rw [← sq_rpow_neg_half]
    exact Real.rpow_le_rpow_of_nonpos hs1 (sq_le_axisSq hw x h1) hneg
  have : axisSq w x ^ (-e) = axisSq w x ^ (-e / 2) * axisSq w x ^ (-e / 2) := by
    rw [← Real.rpow_add hs]; congr 1; ring
  rw [this]
  exact mul_le_mul a0 a1 (Real.rpow_nonneg hs.le _) (Real.rpow_nonneg (abs_nonneg _) _)

/-- Local integrability of `s^{-e}` on a cube, for `e < 1` (two singular coordinates). -/
theorem integrableOn_axisSq_rpow_neg (hw : ∀ i, w i = 0 ∨ w i = 1) {i0 i1 : Fin d}
    (hi : i0 ≠ i1) (h0 : w i0 = 1) (h1 : w i1 = 1) {e : ℝ} (he0 : 0 ≤ e) (he1 : e < 1)
    (R : ℝ) :
    IntegrableOn (fun x : Vec d => axisSq w x ^ (-e)) (Set.pi univ fun _ => Icc (-R) R) := by
  let g : Fin d → ℝ → ℝ := fun j =>
    (Icc (-R) R).indicator (fun t => if j = i0 ∨ j = i1 then |t| ^ (-e) else 1)
  have hg : ∀ j, Integrable (g j) := by
    intro j
    by_cases hj : j = i0 ∨ j = i1
    · simpa only [g, hj, ite_true] using integrable_indicator_abs_rpow_neg he1 R
    · simp only [g, hj, ite_false]
      rw [integrable_indicator_iff measurableSet_Icc]
      exact integrableOn_const (by simp) |>.mono_set (subset_refl _)
  have hF : Integrable (fun x : Vec d => ∏ j, g j (x j)) :=
    Integrable.fintype_prod (μ := fun _ => (volume : Measure ℝ)) hg
  refine Integrable.mono' (hF.integrableOn (s := Set.pi univ fun _ => Icc (-R) R)) ?_ ?_
  · exact ((measurable_axisSq w).pow_const (-e)).aestronglyMeasurable
  · have hbox : MeasurableSet (Set.pi univ fun _ : Fin d => Icc (-R) R) :=
      MeasurableSet.univ_pi fun _ => measurableSet_Icc
    rw [ae_restrict_iff' hbox]
    have h0' : ∀ᵐ x : Vec d ∂volume, x i0 ≠ 0 :=
      Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) i0 0
    have h1' : ∀ᵐ x : Vec d ∂volume, x i1 ≠ 0 :=
      Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) i1 0
    filter_upwards [h0', h1'] with x hx0 hx1 hxb
    have hxj : ∀ j, x j ∈ Icc (-R) R := fun j => hxb j (mem_univ j)
    have hprod : ∏ j, g j (x j) = |x i0| ^ (-e) * |x i1| ^ (-e) := by
      have : ∏ j, g j (x j) =
          ∏ j ∈ Finset.univ.filter (fun j => j = i0 ∨ j = i1), |x j| ^ (-e) := by
        rw [Finset.prod_filter]
        refine Finset.prod_congr rfl fun j _ => ?_
        simp only [g, indicator_of_mem (hxj j)]
      rw [this]
      have hfilt : Finset.univ.filter (fun j : Fin d => j = i0 ∨ j = i1) = {i0, i1} := by
        ext j; simp
      rw [hfilt, Finset.prod_pair hi]
    rw [hprod, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (axisSq_nonneg hw x) _)]
    exact axisSq_rpow_neg_le hw h0 h1 he0 hx0 hx1

end PDE.Ch4Meyers
