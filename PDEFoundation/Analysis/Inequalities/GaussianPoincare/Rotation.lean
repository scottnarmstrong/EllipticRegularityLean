module

public import PDEFoundation.Analysis.Inequalities.GaussianPoincare.Pair
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Group.Prod

/-!
# Rotation invariance of the product heat kernel

The rotation `(x, y) ↦ (c x + s y, -s x + c y)` of `Vec d × Vec d` (with `c² + s² = 1`,
`c ≠ -1`) preserves Lebesgue measure and the product heat kernel.  Measure preservation is proved
by factoring the rotation into three shears, each a skew product over a translation-invariant
measure.
-/

@[expose] public section

open MeasureTheory Real

namespace PDE.GaussianPoincare

variable {d : ℕ}

/-- The shear `(x, y) ↦ (x, y + β x)` preserves Lebesgue measure. -/
theorem measurePreserving_shearLower (β : ℝ) :
    MeasurePreserving (fun p : Vec d × Vec d => (p.1, p.2 + β • p.1))
      (volume.prod volume) (volume.prod volume) := by
  refine MeasurePreserving.skew_product (μa := (volume : Measure (Vec d)))
    (μb := (volume : Measure (Vec d))) (μc := (volume : Measure (Vec d)))
    (μd := (volume : Measure (Vec d))) (f := id) (g := fun x y => y + β • x)
    (MeasurePreserving.id _) ?_ ?_
  · exact measurable_snd.add (measurable_fst.const_smul β)
  · exact Filter.Eventually.of_forall fun x => map_add_right_eq_self _ _

/-- The shear `(x, y) ↦ (x + α y, y)` preserves Lebesgue measure. -/
theorem measurePreserving_shearUpper (α : ℝ) :
    MeasurePreserving (fun p : Vec d × Vec d => (p.1 + α • p.2, p.2))
      (volume.prod volume) (volume.prod volume) := by
  have h := (Measure.measurePreserving_swap (μ := (volume : Measure (Vec d)))
    (ν := (volume : Measure (Vec d)))).comp
    ((measurePreserving_shearLower (d := d) α).comp
      (Measure.measurePreserving_swap (μ := (volume : Measure (Vec d)))
        (ν := (volume : Measure (Vec d)))))
  exact h

/-- The rotation of `Vec d × Vec d`. -/
def rot (c s : ℝ) (p : Vec d × Vec d) : Vec d × Vec d :=
  (c • p.1 + s • p.2, -s • p.1 + c • p.2)

theorem rot_eq_shears {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hc : -1 < c) :
    (rot c s : Vec d × Vec d → Vec d × Vec d) =
      (fun p => (p.1 + (s / (1 + c)) • p.2, p.2)) ∘ (fun p => (p.1, p.2 + (-s) • p.1)) ∘
        (fun p => (p.1 + (s / (1 + c)) • p.2, p.2)) := by
  have h1 : (1 + c) ≠ 0 := by linarith
  funext p
  ext i
  · simp only [rot, Function.comp, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination (p.1 i * (c + 1) + p.2 i * s) * hcs
  · simp only [rot, Function.comp, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination (p.2 i) * hcs

theorem measurePreserving_rot {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hc : -1 < c) :
    MeasurePreserving (rot c s : Vec d × Vec d → Vec d × Vec d)
      (volume.prod volume) (volume.prod volume) := by
  rw [rot_eq_shears hcs hc]
  exact (measurePreserving_shearUpper _).comp
    ((measurePreserving_shearLower _).comp (measurePreserving_shearUpper _))

theorem pairNormSq_rot {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (p : Vec d × Vec d) :
    pairNormSq (rot c s p) = pairNormSq p := by
  simp only [pairNormSq, rot, vecNormSq_eq_sum_sq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  linear_combination ((p.1 i) ^ 2 + (p.2 i) ^ 2) * hcs

theorem rot_rot {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (p : Vec d × Vec d) :
    rot c (-s) (rot c s p) = p := by
  ext i
  · simp only [rot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (p.1 i) * hcs
  · simp only [rot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (p.2 i) * hcs

/-- The rotation as a measurable equivalence. -/
def rotEquiv {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) : Vec d × Vec d ≃ᵐ Vec d × Vec d where
  toFun := rot c s
  invFun := rot c (-s)
  left_inv p := rot_rot hcs p
  right_inv p := by
    have h := rot_rot (c := c) (s := -s) (by linear_combination hcs) p
    simpa using h
  measurable_toFun := by
    unfold rot
    exact ((measurable_fst.const_smul c).add (measurable_snd.const_smul s)).prodMk
      ((measurable_fst.const_smul (-s)).add (measurable_snd.const_smul c))
  measurable_invFun := by
    unfold rot
    exact ((measurable_fst.const_smul c).add (measurable_snd.const_smul (-s))).prodMk
      ((measurable_fst.const_smul (- -s)).add (measurable_snd.const_smul c))

/-- Rotation invariance of the product heat kernel: rotating the first argument of a test function
does not change its Gaussian average. -/
theorem integral_comp_rot_pairHeat {t : ℝ} (ht : 0 < t) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1)
    (hc : -1 < c) (g : Vec d → ℝ) :
    ∫ p : Vec d × Vec d, g (c • p.1 + s • p.2) * pairHeat d t p =
      ∫ x : Vec d, g x * heat d t x := by
  have hmp : MeasurePreserving (rotEquiv (d := d) hcs) (volume.prod volume)
      (volume.prod volume) := measurePreserving_rot (d := d) hcs hc
  have h1 := hmp.integral_comp'
    (fun q : Vec d × Vec d => g q.1 * pairHeat d t q)
  have h2 : ∀ p : Vec d × Vec d, pairHeat d t (rot c s p) = pairHeat d t p := by
    intro p
    rw [pairHeat_eq, pairHeat_eq, pairNormSq_rot hcs]
  have h3 : (fun p : Vec d × Vec d => g (rotEquiv hcs p).1 * pairHeat d t (rotEquiv hcs p)) =
      fun p => g (c • p.1 + s • p.2) * pairHeat d t p := by
    funext p
    change g (rot c s p).1 * pairHeat d t (rot c s p) = _
    rw [h2]
    rfl
  rw [← h3]
  refine h1.trans ?_
  have := integral_prod_mul (μ := (volume : Measure (Vec d))) (ν := (volume : Measure (Vec d)))
    (fun x => g x * heat d t x) (heat d t)
  simp only [pairHeat]
  rw [show (fun q : Vec d × Vec d => g q.1 * (heat d t q.1 * heat d t q.2)) =
    fun q => (g q.1 * heat d t q.1) * heat d t q.2 from by funext q; ring, this, integral_heat ht,
    mul_one]

end PDE.GaussianPoincare
