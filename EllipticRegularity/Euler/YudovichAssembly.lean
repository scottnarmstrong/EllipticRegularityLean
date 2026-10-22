module

public import EllipticRegularity.Euler.RelativeEnergy
public import PDEFoundation.Euler.OsgoodAE

/-!
# Yudovich uniqueness: assembly

Combines the relative energy inequality (`relative_energy_inequality`), the Hölder interpolation
estimate (`abs_integral_wGw_le_of_eLpNorm_le`) and the almost-everywhere Osgood lemma
(`ae_eq_zero_of_integral_bound`) to prove `PDE.yudovich_uniqueness_proof`, whose statement is exactly
that of `PDE.yudovich_uniqueness`.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace PDE

theorem vecNormSq_sub_le_two (p q : Vec 2) :
    vecNormSq (p - q) ≤ 2 * vecNormSq p + 2 * vecNormSq q := by
  rw [vecNormSq_sub_two, vecNormSq_eq_two p, vecNormSq_eq_two q]
  nlinarith [sq_nonneg (p 0 + q 0), sq_nonneg (p 1 + q 1)]

theorem eq_zero_of_vecNormSq_eq_zero {w : Vec 2} (h : vecNormSq w = 0) : w = 0 := by
  rw [vecNormSq_eq_two] at h
  have h0 : w 0 * w 0 = 0 := by nlinarith [mul_self_nonneg (w 0), mul_self_nonneg (w 1)]
  have h1 : w 1 * w 1 = 0 := by nlinarith [mul_self_nonneg (w 0), mul_self_nonneg (w 1)]
  funext i
  fin_cases i
  · exact mul_self_eq_zero.1 h0
  · exact mul_self_eq_zero.1 h1

/-- **Yudovich weak-strong uniqueness for 2d Euler** (exact statement of `PDE.yudovich_uniqueness`). -/
theorem yudovich_uniqueness_proof (T : ℝ) (hT : 0 < T) (M : ℝ) (v₀ : Vec 2 → Vec 2)
    (v₁ v₂ : Vec 2 × ℝ → Vec 2)
    (h₁ : IsEulerWeakSolutionWithDatum T v₀ v₁) (h₂ : IsEulerWeakSolutionWithDatum T v₀ v₂)
    (hb₁ : ∃ B : ℝ, ∀ᵐ z ∂(eulerMeasure T), vecNormSq (v₁ z) ≤ B)
    (hb₂ : ∃ B : ℝ, ∀ᵐ z ∂(eulerMeasure T), vecNormSq (v₂ z) ≤ B)
    (hω : HasBoundedVorticity T M v₂) (hE : HasEnergyInequality T v₀ v₁) :
    ∀ᵐ z ∂(eulerMeasure T), v₁ z = v₂ z := by
  obtain ⟨K, hK, hrel⟩ := relative_energy_inequality
  obtain ⟨G, -, hGp, hΛint, hineq⟩ := hrel T hT M v₀ v₁ v₂ h₁ h₂ hb₁ hb₂ hω hE
  obtain ⟨B1, hB1⟩ := hb₁
  obtain ⟨B2, hB2⟩ := hb₂
  have hbu : EulerBdd T (max B1 0) v₁ :=
    ⟨h₁.1.1, h₁.1.2.1, hB1.mono fun z hz => hz.trans (le_max_left _ _), le_max_right _ _⟩
  have hbv : EulerBdd T (max B2 0) v₂ :=
    ⟨h₂.1.1, h₂.1.2.1, hB2.mono fun z hz => hz.trans (le_max_left _ _), le_max_right _ _⟩
  have hBn : 0 ≤ 2 * max B1 0 + 2 * max B2 0 := by
    have := le_max_right B1 0; have := le_max_right B2 0; linarith
  set Bs : ℝ := Real.sqrt (2 * max B1 0 + 2 * max B2 0) with hBs
  have hBs0 : 0 ≤ Bs := Real.sqrt_nonneg _
  have hBs2 : Bs ^ 2 = 2 * max B1 0 + 2 * max B2 0 := Real.sq_sqrt hBn
  have hmeas1 : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ i,
      AEStronglyMeasurable (fun x => v₁ (x, t) i) (volume.restrict torusCube) :=
    ae_all_iff.2 fun i => ae_slice_aesm (hbu.coord_aesm i)
  have hmeas2 : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ i,
      AEStronglyMeasurable (fun x => v₂ (x, t) i) (volume.restrict torusCube) :=
    ae_all_iff.2 fun i => ae_slice_aesm (hbv.coord_aesm i)
  have hbd1 := ae_slice_bdd hbu.bdd
  have hbd2 := ae_slice_bdd hbv.bdd
  have hwB : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ᵐ x ∂(volume.restrict torusCube),
      vecNormSq (v₁ (x, t) - v₂ (x, t)) ≤ Bs ^ 2 := by
    filter_upwards [hbd1, hbd2] with t h1 h2
    filter_upwards [h1, h2] with x a b
    rw [hBs2]
    have := vecNormSq_sub_le_two (v₁ (x, t)) (v₂ (x, t))
    linarith
  have hyB : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
      ∫ x in torusCube, vecNormSq (v₁ (x, t) - v₂ (x, t)) ≤ Bs ^ 2 := by
    filter_upwards [hwB] with t ht
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => vecNormSq_nonneg' _)
      (integrable_const (Bs ^ 2)) ht).trans (le_of_eq ?_)
    simp [Measure.real, volume_torusCube]
  have hΛy : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ p : ℝ, 2 ≤ p →
      |∫ x in torusCube, ∑ i, ∑ j,
        (v₁ (x, s) - v₂ (x, s)) j * (v₁ (x, s) - v₂ (x, s)) i * G (x, s) i j| ≤
      (K * max M 0) * p * Bs ^ (2 / p) *
        (∫ x in torusCube, vecNormSq (v₁ (x, s) - v₂ (x, s))) ^ (1 - 1 / p) := by
    filter_upwards [hGp, hmeas1, hmeas2, hwB] with s hGs m1 m2 hb
    intro p hp
    obtain ⟨hmem, hnorm⟩ := hGs p hp
    have hp0 : 0 < p := by linarith
    have hKp : 0 ≤ K * p := mul_nonneg hK hp0.le
    have hL : 0 ≤ K * p * max M 0 := mul_nonneg hKp (le_max_right _ _)
    have hnorm' : eLpNorm (fun x => matFrobNorm (G (x, s))) (ENNReal.ofReal p)
        (volume.restrict torusCube) ≤ ENNReal.ofReal (K * p * max M 0) :=
      hnorm.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (le_max_left _ _) hKp))
    have := abs_integral_wGw_le_of_eLpNorm_le (p := p) (B := Bs) (L := K * p * max M 0)
      (G := fun x => G (x, s)) (w := fun x => v₁ (x, s) - v₂ (x, s)) hp hBs0 hL hmem hnorm'
      (fun i => (m1 i).sub (m2 i)) hb
    calc _ ≤ _ := this
      _ = _ := by ring
  have hy0ae := ae_eq_zero_of_integral_bound hT.le hBs0 (mul_nonneg hK (le_max_right M 0)) hΛint
    (y := fun t => ∫ x in torusCube, vecNormSq (v₁ (x, t) - v₂ (x, t)))
    (fun t => integral_nonneg fun x => vecNormSq_nonneg' _) hyB hineq hΛy
  -- transfer to the space-time measure
  have hcoord : ∀ i, AEStronglyMeasurable (fun z => v₁ z i - v₂ z i) (eulerMeasure T) :=
    fun i => (hbu.coord_aesm i).sub (hbv.coord_aesm i)
  have hfm : AEStronglyMeasurable (fun z => vecNormSq (v₁ z - v₂ z)) (eulerMeasure T) := by
    have : (fun z => vecNormSq (v₁ z - v₂ z)) =
        fun z => (v₁ z 0 - v₂ z 0) * (v₁ z 0 - v₂ z 0) + (v₁ z 1 - v₂ z 1) * (v₁ z 1 - v₂ z 1) := by
      funext z; rw [vecNormSq_eq_two]; rfl
    rw [this]
    exact ((hcoord 0).mul (hcoord 0)).add ((hcoord 1).mul (hcoord 1))
  have hfi : Integrable (fun z => vecNormSq (v₁ z - v₂ z)) (eulerMeasure T) := by
    refine Integrable.of_bound hfm (Bs ^ 2) ?_
    filter_upwards [hbu.bdd, hbv.bdd] with z a b
    rw [Real.norm_eq_abs, abs_of_nonneg (vecNormSq_nonneg' _), hBs2]
    have := vecNormSq_sub_le_two (v₁ z) (v₂ z)
    linarith
  have hint0 : ∫ z, vecNormSq (v₁ z - v₂ z) ∂(eulerMeasure T) = 0 := by
    have hfi' := hfi
    rw [eulerMeasure_eq_prod] at hfi' ⊢
    rw [integral_prod_symm _ hfi']
    refine (integral_congr_ae hy0ae).trans (integral_zero _ _)
  have hz := (integral_eq_zero_iff_of_nonneg (fun z => vecNormSq_nonneg' _) hfi).1 hint0
  filter_upwards [hz] with z hz
  exact sub_eq_zero.1 (eq_zero_of_vecNormSq_eq_zero hz)

end PDE
