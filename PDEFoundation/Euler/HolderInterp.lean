module

public import PDEFoundation.Euler.GradLimitBasic

/-!
# Hölder and interpolation for the Yudovich energy estimate

For `w ∈ L^∞ ∩ L²(cube)` (here `|w|² ≤ B²` a.e.) and a matrix field `G ∈ L^p(cube)`, `p ≥ 2`,
`|∫_{cube} (w·∇)G·w| ≤ ‖G‖_p ‖w‖_∞^{2/p} ‖w‖₂^{2-2/p}`, where `(w·∇)G·w = ∑ᵢⱼ wⱼ wᵢ Gᵢⱼ` and `Gᵢⱼ = ∂ⱼvᵢ`.
This is the manuscript's Step 5: Hölder with exponents `p, p/(p-1)` and `‖w‖²_{2p/(p-1)} ≤ ‖w‖_∞^{2/p}‖w‖₂^{2-2/p}`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE

theorem sum_sq_mul_eq (w : Vec 2) : ∑ i : Fin 2, ∑ j : Fin 2, (w j * w i) ^ 2 = vecNormSq w ^ 2 := by
  simp only [vecNormSq, vecDot, Fin.sum_univ_two]
  ring

/-- Pointwise bound `|wᵀ A w| ≤ |w|² |A|_F`. -/
theorem abs_sum_mul_le (w : Vec 2) (A : Fin 2 → Fin 2 → ℝ) :
    |∑ i, ∑ j, w j * w i * A i j| ≤ vecNormSq w * matFrobNorm A := by
  have hs : 0 ≤ vecNormSq w := by
    simp only [vecNormSq, vecDot, Fin.sum_univ_two]; nlinarith [mul_self_nonneg (w 0), mul_self_nonneg (w 1)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 2 × Fin 2))
    (fun k => w k.2 * w k.1) (fun k => A k.1 k.2)
  simp only [Fintype.sum_prod_type] at hcs
  have hF : (∑ i : Fin 2, ∑ j : Fin 2, A i j ^ 2) = matFrobNorm A ^ 2 := by
    unfold matFrobNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rw [sum_sq_mul_eq, hF] at hcs
  exact abs_le_of_sq_le_sq (by rw [mul_pow]; exact hcs) (mul_nonneg hs (matFrobNorm_nonneg A))

theorem vecNormSq_nonneg' (w : Vec 2) : 0 ≤ vecNormSq w := by
  simp only [vecNormSq, vecDot, Fin.sum_univ_two]
  nlinarith [mul_self_nonneg (w 0), mul_self_nonneg (w 1)]

theorem toReal_eLpNorm_eq_integral_rpow {μ : Measure (Vec 2)} {f : Vec 2 → ℝ} {p : ℝ}
    (hp : 0 < p) (hf : MemLp f (ENNReal.ofReal p) μ) (hf0 : ∀ x, 0 ≤ f x) :
    (eLpNorm f (ENNReal.ofReal p) μ).toReal = (∫ x, f x ^ p ∂μ) ^ (1 / p) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by simpa using hp) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity)]
  simp only [ENNReal.toReal_ofReal hp.le, one_div]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Real.norm_of_nonneg (hf0 x)]

/-- **Hölder + interpolation (manuscript Step 5).**  With `G ∈ L^p(cube)`, `p ≥ 2`, and `|w|² ≤ B²` a.e.:
`|∫ ∑ᵢⱼ wⱼ wᵢ Gᵢⱼ| ≤ ‖G‖_p · B^{2/p} · (∫ |w|²)^{1-1/p}`. -/
theorem abs_integral_wGw_le {p B : ℝ} (hp : 2 ≤ p) (hB : 0 ≤ B)
    {G : Vec 2 → Fin 2 → Fin 2 → ℝ} {w : Vec 2 → Vec 2}
    (hG : MemLp (fun x => matFrobNorm (G x)) (ENNReal.ofReal p) (volume.restrict torusCube))
    (hw : ∀ i, AEStronglyMeasurable (fun x => w x i) (volume.restrict torusCube))
    (hwB : ∀ᵐ x ∂(volume.restrict torusCube), vecNormSq (w x) ≤ B ^ 2) :
    |(∫ x in torusCube, ∑ i, ∑ j, w x j * w x i * G x i j)| ≤
      (eLpNorm (fun x => matFrobNorm (G x)) (ENNReal.ofReal p) (volume.restrict torusCube)).toReal *
        B ^ (2 / p) * (∫ x in torusCube, vecNormSq (w x)) ^ (1 - 1 / p) := by
  set μ : Measure (Vec 2) := volume.restrict torusCube with hμ
  have hp1 : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  set q : ℝ := Real.conjExponent p with hq
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp1
  have hq0 : 0 < q := hpq.symm.pos
  have hqp : 1 / p + 1 / q = 1 := by simpa using hpq.inv_add_inv_eq_one
  have hq1 : 1 ≤ q := hpq.symm.lt.le
  have hsm : AEStronglyMeasurable (fun x => vecNormSq (w x)) μ := by
    have : (fun x => vecNormSq (w x)) = fun x => w x 0 * w x 0 + w x 1 * w x 1 := by
      funext x; simp [vecNormSq, vecDot, Fin.sum_univ_two]
    rw [this]
    exact ((hw 0).mul (hw 0)).add ((hw 1).mul (hw 1))
  have hs0 : ∀ x, 0 ≤ vecNormSq (w x) := fun x => vecNormSq_nonneg' _
  have hsb : ∀ᵐ x ∂μ, ‖vecNormSq (w x)‖ ≤ B ^ 2 :=
    hwB.mono fun x hx => by rwa [Real.norm_of_nonneg (hs0 x)]
  have hsq : MemLp (fun x => vecNormSq (w x)) (ENNReal.ofReal q) μ := MemLp.of_bound hsm _ hsb
  have hsint : Integrable (fun x => vecNormSq (w x)) μ := hsq.integrable (by simpa using hq1)
  have hgint : Integrable (fun x => matFrobNorm (G x)) μ := hG.integrable (by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith))
  have hprod : Integrable (fun x => matFrobNorm (G x) * vecNormSq (w x)) μ :=
    hgint.mul_bdd hsm hsb
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (f := fun x => matFrobNorm (G x))
    (g := fun x => vecNormSq (w x)) (Filter.Eventually.of_forall fun x => matFrobNorm_nonneg _)
    (Filter.Eventually.of_forall hs0) hG hsq
  have h1 : |(∫ x in torusCube, ∑ i, ∑ j, w x j * w x i * G x i j)| ≤
      ∫ x, matFrobNorm (G x) * vecNormSq (w x) ∂μ := by
    refine (abs_integral_le_integral_abs).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _) hprod
      (Filter.Eventually.of_forall fun x => ?_)
    show |∑ i, ∑ j, w x j * w x i * G x i j| ≤ matFrobNorm (G x) * vecNormSq (w x)
    rw [mul_comm]
    exact abs_sum_mul_le (w x) (G x)
  -- the `L^q` factor
  have h2 : ∫ x, vecNormSq (w x) ^ q ∂μ ≤ (B ^ 2) ^ (q - 1) * ∫ x, vecNormSq (w x) ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hs0 x) _)
      (hsint.const_mul _) (hwB.mono fun x hx => ?_)
    have e : vecNormSq (w x) ^ q = vecNormSq (w x) ^ (q - 1) * vecNormSq (w x) := by
      rw [← Real.rpow_add_one' (hs0 x) (by linarith)]
      ring_nf
    show vecNormSq (w x) ^ q ≤ (B ^ 2) ^ (q - 1) * vecNormSq (w x)
    rw [e]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (hs0 x) hx (by linarith)) (hs0 x)
  have hY0 : 0 ≤ ∫ x, vecNormSq (w x) ∂μ := integral_nonneg hs0
  have h3 : (∫ x, vecNormSq (w x) ^ q ∂μ) ^ (1 / q) ≤
      B ^ (2 / p) * (∫ x, vecNormSq (w x) ∂μ) ^ (1 - 1 / p) := by
    calc (∫ x, vecNormSq (w x) ^ q ∂μ) ^ (1 / q)
        ≤ ((B ^ 2) ^ (q - 1) * ∫ x, vecNormSq (w x) ∂μ) ^ (1 / q) :=
          Real.rpow_le_rpow (integral_nonneg fun x => Real.rpow_nonneg (hs0 x) _) h2
            (by positivity)
      _ = ((B ^ 2) ^ (q - 1)) ^ (1 / q) * (∫ x, vecNormSq (w x) ∂μ) ^ (1 / q) :=
          Real.mul_rpow (by positivity) hY0
      _ = B ^ (2 / p) * (∫ x, vecNormSq (w x) ∂μ) ^ (1 - 1 / p) := by
          have e1 : 1 / q = 1 - 1 / p := by linarith
          have e2 : ((B ^ 2) ^ (q - 1)) ^ (1 / q) = B ^ (2 / p) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hB, ← Real.rpow_mul hB]
            congr 1
            have : (q - 1) * (1 / q) = 1 / p := by
              rw [sub_mul, one_mul, mul_one_div_cancel hq0.ne']; linarith
            push_cast
            rw [mul_assoc, this]
            ring
          rw [e2, e1]
  have hT1 := toReal_eLpNorm_eq_integral_rpow (μ := μ) hp0 hG (fun x => matFrobNorm_nonneg (G x))
  calc _ ≤ _ := h1
    _ ≤ _ := hHolder
    _ ≤ (∫ x, matFrobNorm (G x) ^ p ∂μ) ^ (1 / p) *
        (B ^ (2 / p) * (∫ x, vecNormSq (w x) ∂μ) ^ (1 - 1 / p)) :=
        mul_le_mul_of_nonneg_left h3
          (Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (matFrobNorm_nonneg _) _) _)
    _ = _ := by rw [hT1]; ring

/-- Form used in the Osgood step: if `‖G‖_p ≤ L` (e.g. `L = K p M` from the periodic CZ bound), then
`|∫ ∑ᵢⱼ wⱼ wᵢ Gᵢⱼ| ≤ L · B^{2/p} · (∫ |w|²)^{1-1/p}`. -/
theorem abs_integral_wGw_le_of_eLpNorm_le {p B L : ℝ} (hp : 2 ≤ p) (hB : 0 ≤ B) (hL : 0 ≤ L)
    {G : Vec 2 → Fin 2 → Fin 2 → ℝ} {w : Vec 2 → Vec 2}
    (hG : MemLp (fun x => matFrobNorm (G x)) (ENNReal.ofReal p) (volume.restrict torusCube))
    (hGL : eLpNorm (fun x => matFrobNorm (G x)) (ENNReal.ofReal p) (volume.restrict torusCube) ≤
      ENNReal.ofReal L)
    (hw : ∀ i, AEStronglyMeasurable (fun x => w x i) (volume.restrict torusCube))
    (hwB : ∀ᵐ x ∂(volume.restrict torusCube), vecNormSq (w x) ≤ B ^ 2) :
    |(∫ x in torusCube, ∑ i, ∑ j, w x j * w x i * G x i j)| ≤
      L * B ^ (2 / p) * (∫ x in torusCube, vecNormSq (w x)) ^ (1 - 1 / p) := by
  refine (abs_integral_wGw_le hp hB hG hw hwB).trans ?_
  have hY : 0 ≤ ∫ x in torusCube, vecNormSq (w x) := integral_nonneg fun x => vecNormSq_nonneg' _
  have h1 : (eLpNorm (fun x => matFrobNorm (G x)) (ENNReal.ofReal p)
      (volume.restrict torusCube)).toReal ≤ L := ENNReal.toReal_le_of_le_ofReal hL hGL
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hB _))
    (Real.rpow_nonneg hY _)

end PDE
