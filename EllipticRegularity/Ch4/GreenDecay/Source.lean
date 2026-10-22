module

public import EllipticRegularity.Ch4.GreenDecay.Annulus

/-!
# The mean-zero annulus source `g = (u - (u)_{A_r}) 1_{A_r}` of Lemma 4.35
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4GreenDecay

open MeasureTheory PDE

noncomputable section

variable {d : ℕ}

/-- The source `g = (u - (u)_{A_r}) 1_{A_r}`. -/
def annulusSource (d : ℕ) (r : ℝ) (u : Vec d → ℝ) : Vec d → ℝ :=
  (annulus d r).indicator (fun x => u x - integralAverage (annulus d r) u)

theorem annulusSource_eq_zero_of_notMem {r : ℝ} (u : Vec d → ℝ) {x : Vec d}
    (hx : x ∉ euclideanBall (0 : Vec d) r) : annulusSource d r u x = 0 :=
  Set.indicator_of_notMem (fun h => hx (annulus_subset r h)) _

theorem annulusSource_eq_zero_of_mem_half {r : ℝ} (u : Vec d → ℝ) {x : Vec d}
    (hx : x ∈ euclideanBall (0 : Vec d) (r / 2)) : annulusSource d r u x = 0 :=
  Set.indicator_of_notMem (fun h => h.2 hx) _

theorem annulusSource_memL2 {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (u : H1Function (euclideanBall (0 : Vec d) R)) :
    MemL2On (euclideanBall (0 : Vec d) R) (annulusSource d r u.toFun) := by
  have hR : 0 < R := lt_of_lt_of_le hr hrR
  have : IsFiniteMeasure (volumeOn (euclideanBall (0 : Vec d) R)) :=
    isFiniteMeasure_volumeOn_euclideanBall 0 hR.le
  have h : MemL2On (euclideanBall (0 : Vec d) R)
      (fun x => u.toFun x - integralAverage (annulus d r) u.toFun) :=
    u.memL2.sub (memLp_const _)
  exact MemLp.indicator (measurableSet_annulus r) h

theorem integrableOn_annulus {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (u : H1Function (euclideanBall (0 : Vec d) R)) :
    IntegrableOn u.toFun (annulus d r) := by
  have hR : 0 < R := lt_of_lt_of_le hr hrR
  have : IsFiniteMeasure (volumeOn (euclideanBall (0 : Vec d) R)) :=
    isFiniteMeasure_volumeOn_euclideanBall 0 hR.le
  exact (u.integrableOn).mono_set ((annulus_subset r).trans (euclideanBall_mono hr.le hrR))

theorem annulus_sub_average_memL2 {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (u : H1Function (euclideanBall (0 : Vec d) R)) :
    MemL2On (annulus d r) (fun x => u.toFun x - integralAverage (annulus d r) u.toFun) := by
  have hR : 0 < R := lt_of_lt_of_le hr hrR
  have : IsFiniteMeasure (volumeOn (euclideanBall (0 : Vec d) R)) :=
    isFiniteMeasure_volumeOn_euclideanBall 0 hR.le
  have h : MemL2On (euclideanBall (0 : Vec d) R)
      (fun x => u.toFun x - integralAverage (annulus d r) u.toFun) :=
    u.memL2.sub (memLp_const _)
  exact h.mono_measure (Measure.restrict_mono
    ((annulus_subset r).trans (euclideanBall_mono hr.le hrR)) le_rfl)

theorem integral_annulus_sub_average (hd : 0 < d) {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (u : H1Function (euclideanBall (0 : Vec d) R)) :
    (∫ x in annulus d r, (u.toFun x - integralAverage (annulus d r) u.toFun)) = 0 := by
  have hint := integrableOn_annulus hr hrR u
  have : IsFiniteMeasure (volume.restrict (annulus d r)) :=
    isFiniteMeasure_restrict.mpr (volume_annulus_ne_top hr)
  rw [integral_sub hint (integrable_const _), setIntegral_const, smul_eq_mul]
  have hV := (volume_annulus_toReal_pos hd hr).ne'
  unfold integralAverage
  show (∫ x in annulus d r, u.toFun x) - (volume (annulus d r)).toReal *
    ((volume (annulus d r)).toReal⁻¹ * ∫ x in annulus d r, u.toFun x) = 0
  rw [← mul_assoc, mul_inv_cancel₀ hV, one_mul, sub_self]

/-- The source has mean zero. -/
theorem integral_annulusSource (hd : 0 < d) {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (u : H1Function (euclideanBall (0 : Vec d) R)) :
    (∫ x in euclideanBall (0 : Vec d) R, annulusSource d r u.toFun x) = 0 := by
  unfold annulusSource
  rw [setIntegral_indicator_eq (measurableSet_annulus r)
    ((annulus_subset r).trans (euclideanBall_mono hr.le hrR))]
  exact integral_annulus_sub_average hd hr hrR u

theorem annulusSource_mul_eq (r : ℝ) (u : Vec d → ℝ) (x : Vec d) :
    annulusSource d r u x * u x = annulusSource d r u x ^ 2 +
      integralAverage (annulus d r) u * annulusSource d r u x := by
  unfold annulusSource
  by_cases hx : x ∈ annulus d r
  · simp only [Set.indicator_of_mem hx]
    ring
  · simp only [Set.indicator_of_notMem hx]
    ring

theorem annulusSource_sq_eq (r : ℝ) (u : Vec d → ℝ) (x : Vec d) :
    annulusSource d r u x ^ 2 =
      (annulus d r).indicator
        (fun x => (u x - integralAverage (annulus d r) u) ^ 2) x := by
  unfold annulusSource
  by_cases hx : x ∈ annulus d r
  · simp only [Set.indicator_of_mem hx]
  · simp only [Set.indicator_of_notMem hx]; ring

/-- The `L²` energy of the source is the annulus oscillation. -/
theorem integral_annulusSource_sq {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R) (u : Vec d → ℝ) :
    (∫ x in euclideanBall (0 : Vec d) R, annulusSource d r u x ^ 2) =
      ∫ x in annulus d r, (u x - integralAverage (annulus d r) u) ^ 2 := by
  simp_rw [annulusSource_sq_eq]
  exact setIntegral_indicator_eq (measurableSet_annulus r)
    ((annulus_subset r).trans (euclideanBall_mono hr.le hrR)) _

/-- `∫ g u = ∫ g²`, because `g` has mean zero. -/
theorem integral_annulusSource_mul (hd : 0 < d) {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (u : H1Function (euclideanBall (0 : Vec d) R)) :
    (∫ x in euclideanBall (0 : Vec d) R, annulusSource d r u.toFun x * u.toFun x) =
      ∫ x in euclideanBall (0 : Vec d) R, annulusSource d r u.toFun x ^ 2 := by
  have hg := annulusSource_memL2 hr hrR u
  have hint : IntegrableOn (fun x => annulusSource d r u.toFun x ^ 2)
      (euclideanBall (0 : Vec d) R) := hg.integrable_sq
  have hint1 : IntegrableOn (annulusSource d r u.toFun) (euclideanBall (0 : Vec d) R) := by
    have hR : 0 < R := lt_of_lt_of_le hr hrR
    have : IsFiniteMeasure (volumeOn (euclideanBall (0 : Vec d) R)) :=
      isFiniteMeasure_volumeOn_euclideanBall 0 hR.le
    exact hg.integrable (by norm_num)
  simp_rw [annulusSource_mul_eq]
  rw [integral_add hint (hint1.const_mul _), integral_const_mul,
    integral_annulusSource hd hr hrR u, mul_zero, add_zero]

end

end PDE.Ch4GreenDecay
