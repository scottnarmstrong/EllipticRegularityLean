module

public import PDEFoundation.Sobolev.Mean
public import PDEFoundation.Measure.NormalizedLp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.MeanInequalities

/-!
# The Hölder step of the reverse Hölder lemma

The Hölder, Young and Jensen algebra of Step 2 of the reverse Hölder lemma
for the Meyers estimate, factored as lemmas about a set `P` of positive finite
volume. All averages are `V⁻¹ ∫_P`, with `V = (volume P).toReal`.
-/

@[expose] public section

open MeasureTheory

namespace PDE

namespace MeyersRH

variable {d : ℕ} {P : Set (Vec d)}

/-- Integrability of the product of conjugate-power functions, by Young's inequality. -/
theorem integrable_mul_of_memLp_conj {p p' : ℝ} (hpp : p.HolderConjugate p')
    {v G : Vec d → ℝ} (hv0 : ∀ x, 0 ≤ v x) (hG0 : ∀ x, 0 ≤ G x)
    (hv : MemLp v (ENNReal.ofReal p') (volume.restrict P))
    (hG : MemLp G (ENNReal.ofReal p) (volume.restrict P)) :
    Integrable (fun x => v x * G x) (volume.restrict P) := by
  have hp0 : 0 < p := hpp.pos
  have hp'0 : 0 < p' := hpp.symm.pos
  have h1 : Integrable (fun x => ‖v x‖ ^ p') (volume.restrict P) := by
    simpa [ENNReal.toReal_ofReal hp'0.le] using
      hv.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp'0).ne' ENNReal.ofReal_ne_top
  have h2 : Integrable (fun x => ‖G x‖ ^ p) (volume.restrict P) := by
    simpa [ENNReal.toReal_ofReal hp0.le] using
      hG.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top
  refine Integrable.mono' ((h1.div_const p').add (h2.div_const p))
    (hv.aestronglyMeasurable.mul hG.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
  have := Real.young_inequality_of_nonneg (hv0 x) (hG0 x) hpp.symm
  rw [Real.norm_of_nonneg (mul_nonneg (hv0 x) (hG0 x))]
  simpa [abs_of_nonneg (hv0 x), abs_of_nonneg (hG0 x)] using this

/-- Normalized Hölder: `∫_P v G ≤ V · (avg v^{p'})^{1/p'} · (avg G^p)^{1/p}`. -/
theorem integral_mul_le_avg {p p' : ℝ} (hpp : p.HolderConjugate p')
    (hP0 : 0 < (volume P).toReal)
    {v G : Vec d → ℝ} (hv0 : ∀ x, 0 ≤ v x) (hG0 : ∀ x, 0 ≤ G x)
    (hv : MemLp v (ENNReal.ofReal p') (volume.restrict P))
    (hG : MemLp G (ENNReal.ofReal p) (volume.restrict P)) :
    ∫ x in P, v x * G x ≤
      (volume P).toReal * ((volume P).toReal⁻¹ * ∫ x in P, v x ^ p') ^ (1 / p') *
        ((volume P).toReal⁻¹ * ∫ x in P, G x ^ p) ^ (1 / p) := by
  set V := (volume P).toReal with hV
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hpp.symm
    (Filter.Eventually.of_forall hv0) (Filter.Eventually.of_forall hG0) hv hG
  have hp0 : 0 < p := hpp.pos
  have hp'0 : 0 < p' := hpp.symm.pos
  have hIv : 0 ≤ ∫ x in P, v x ^ p' :=
    integral_nonneg fun x => Real.rpow_nonneg (hv0 x) _
  have hIG : 0 ≤ ∫ x in P, G x ^ p :=
    integral_nonneg fun x => Real.rpow_nonneg (hG0 x) _
  have hsum : 1 / p' + 1 / p = 1 := by
    have := hpp.inv_add_inv_eq_one
    rw [one_div, one_div]; linarith
  have hVV : V ^ (1 / p') * V ^ (1 / p) = V := by
    rw [← Real.rpow_add hP0, hsum, Real.rpow_one]
  have e1 : (V⁻¹ * ∫ x in P, v x ^ p') ^ (1 / p') =
      (V ^ (1 / p'))⁻¹ * (∫ x in P, v x ^ p') ^ (1 / p') := by
    rw [Real.mul_rpow (inv_nonneg.mpr hP0.le) hIv, Real.inv_rpow hP0.le]
  have e2 : (V⁻¹ * ∫ x in P, G x ^ p) ^ (1 / p) =
      (V ^ (1 / p))⁻¹ * (∫ x in P, G x ^ p) ^ (1 / p) := by
    rw [Real.mul_rpow (inv_nonneg.mpr hP0.le) hIG, Real.inv_rpow hP0.le]
  rw [e1, e2]
  have hA : 0 < V ^ (1 / p') := Real.rpow_pos_of_pos hP0 _
  have hB : 0 < V ^ (1 / p) := Real.rpow_pos_of_pos hP0 _
  have hVV' : V / (V ^ (1 / p') * V ^ (1 / p)) = 1 := by
    rw [hVV]; exact div_self hP0.ne'
  have : V * ((V ^ (1 / p'))⁻¹ * (∫ x in P, v x ^ p') ^ (1 / p')) *
      ((V ^ (1 / p))⁻¹ * (∫ x in P, G x ^ p) ^ (1 / p)) =
      (∫ x in P, v x ^ p') ^ (1 / p') * (∫ x in P, G x ^ p) ^ (1 / p) := by
    calc _ = (V / (V ^ (1 / p') * V ^ (1 / p))) *
          ((∫ x in P, v x ^ p') ^ (1 / p') * (∫ x in P, G x ^ p) ^ (1 / p)) := by
          field_simp
      _ = _ := by rw [hVV', one_mul]
  rw [this]
  exact hH

/-- `∫_P G ≤ V · (avg G^p)^{1/p}`. -/
theorem integral_le_avg {p p' : ℝ} (hpp : p.HolderConjugate p')
    (hP0 : 0 < (volume P).toReal) (hPfin : volume P ≠ ⊤)
    {G : Vec d → ℝ} (hG0 : ∀ x, 0 ≤ G x)
    (hG : MemLp G (ENNReal.ofReal p) (volume.restrict P)) :
    ∫ x in P, G x ≤
      (volume P).toReal * ((volume P).toReal⁻¹ * ∫ x in P, G x ^ p) ^ (1 / p) := by
  have hp'0 : 0 < p' := hpp.symm.pos
  have : IsFiniteMeasure (volume.restrict P) := ⟨by simpa using hPfin.lt_top⟩
  have h1 : MemLp (fun _ : Vec d => (1 : ℝ)) (ENNReal.ofReal p') (volume.restrict P) :=
    memLp_const 1
  have := integral_mul_le_avg hpp hP0 (v := fun _ => (1 : ℝ)) (fun _ => zero_le_one) hG0 h1 hG
  have hint : ∫ x in P, (1 : ℝ) ^ p' = (volume P).toReal := by
    simp only [Real.one_rpow]
    rw [setIntegral_const]
    simp [Measure.real]
  simp only [one_mul, Real.one_rpow] at this
  simp only [Real.one_rpow] at hint
  rw [hint, inv_mul_cancel₀ hP0.ne', Real.one_rpow, mul_one] at this
  exact this

/-- The shifted Hölder step:
`∫_P |u - c| G ≤ V (1 + κ) N (avg G^p)^{1/p}`, where `N = (avg |u - ū|^{p'})^{1/p'}`
and `|ū - c| ≤ κ N`. -/
theorem integral_abs_sub_mul_le {p p' : ℝ} (hpp : p.HolderConjugate p')
    (hP0 : 0 < (volume P).toReal) (hPfin : volume P ≠ ⊤)
    {u G : Vec d → ℝ} {ub c κ : ℝ} (hκ : 0 ≤ κ) (hG0 : ∀ x, 0 ≤ G x)
    (hv : MemLp (fun x => u x - ub) (ENNReal.ofReal p') (volume.restrict P))
    (hG : MemLp G (ENNReal.ofReal p) (volume.restrict P))
    (hc : |ub - c| ≤ κ * ((volume P).toReal⁻¹ * ∫ x in P, |u x - ub| ^ p') ^ (1 / p')) :
    ∫ x in P, |u x - c| * G x ≤
      (volume P).toReal * (1 + κ) *
        ((volume P).toReal⁻¹ * ∫ x in P, |u x - ub| ^ p') ^ (1 / p') *
        ((volume P).toReal⁻¹ * ∫ x in P, G x ^ p) ^ (1 / p) := by
  set V := (volume P).toReal with hV
  set N := (V⁻¹ * ∫ x in P, |u x - ub| ^ p') ^ (1 / p') with hN
  set Γ := (V⁻¹ * ∫ x in P, G x ^ p) ^ (1 / p) with hΓ
  have : IsFiniteMeasure (volume.restrict P) := ⟨by simpa using hPfin.lt_top⟩
  have hp0 : 0 < p := hpp.pos
  have hp1 : 1 ≤ p := hpp.lt.le
  have hv' : MemLp (fun x => |u x - ub|) (ENNReal.ofReal p') (volume.restrict P) := by
    simpa [Real.norm_eq_abs] using hv.norm
  have hmul : Integrable (fun x => |u x - ub| * G x) (volume.restrict P) :=
    integrable_mul_of_memLp_conj hpp (fun x => abs_nonneg _) hG0 hv' hG
  have hGint : Integrable G (volume.restrict P) :=
    hG.integrable (by simpa using hp1)
  have hA := integral_mul_le_avg hpp hP0 (fun x => abs_nonneg (u x - ub)) hG0 hv' hG
  have hB := integral_le_avg hpp hP0 hPfin hG0 hG
  have hpt : ∀ x, |u x - c| * G x ≤ |u x - ub| * G x + |ub - c| * G x := by
    intro x
    have : |u x - c| ≤ |u x - ub| + |ub - c| := by
      calc |u x - c| = |(u x - ub) + (ub - c)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    nlinarith [hG0 x]
  have hint : ∫ x in P, |u x - c| * G x ≤
      (∫ x in P, |u x - ub| * G x) + |ub - c| * ∫ x in P, G x := by
    calc ∫ x in P, |u x - c| * G x
        ≤ ∫ x in P, (|u x - ub| * G x + |ub - c| * G x) :=
          integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun x => mul_nonneg (abs_nonneg _) (hG0 x))
            (hmul.add (hGint.const_mul _)) (Filter.Eventually.of_forall hpt)
      _ = _ := by rw [integral_add hmul (hGint.const_mul _), integral_const_mul]
  have hInt0 : 0 ≤ ∫ x in P, G x := integral_nonneg hG0
  have hΓ0 : 0 ≤ Γ := Real.rpow_nonneg (mul_nonneg (inv_nonneg.mpr hP0.le)
    (integral_nonneg fun x => Real.rpow_nonneg (hG0 x) _)) _
  have hN0 : 0 ≤ N := Real.rpow_nonneg (mul_nonneg (inv_nonneg.mpr hP0.le)
    (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _)) _
  calc ∫ x in P, |u x - c| * G x
      ≤ (∫ x in P, |u x - ub| * G x) + |ub - c| * ∫ x in P, G x := hint
    _ ≤ V * N * Γ + (κ * N) * (V * Γ) := by
        exact add_le_add hA (mul_le_mul hc hB hInt0 (mul_nonneg hκ hN0))
    _ = V * (1 + κ) * N * Γ := by ring

end MeyersRH

end PDE
