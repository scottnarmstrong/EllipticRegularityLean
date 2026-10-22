module

public import EllipticRegularity.Euler.RelativeEnergySlice
public import PDEFoundation.Euler.HolderInterp

/-!
# The relative energy inequality (manuscript Steps 1, 3, 4)

For `v₁, v₂` as in the hypotheses of `PDE.yudovich_uniqueness` and `w = v₁ - v₂`, there
is a jointly measurable `G` (the space-time weak gradient `∇v₂`; the slices satisfy `‖G(·,t)‖_{L^p} ≤ K p M`) such
that for a.e. `t ∈ [0,T]`

`∫_cube |w(x,t)|² dx ≤ -2 ∫₀ᵗ ∫_cube ∑ᵢⱼ wⱼ wᵢ Gᵢⱼ dx ds`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE

section SliceHelpers

variable {a b : Vec 2 → Vec 2} {B1 B2 : ℝ}

theorem integrable_cube_coord_mul (ha : ∀ i, AEStronglyMeasurable (fun x => a x i) (volume.restrict torusCube))
    (hb : ∀ i, AEStronglyMeasurable (fun x => b x i) (volume.restrict torusCube))
    (hBa : ∀ᵐ x ∂(volume.restrict torusCube), vecNormSq (a x) ≤ B1)
    (hBb : ∀ᵐ x ∂(volume.restrict torusCube), vecNormSq (b x) ≤ B2) (i j : Fin 2) :
    Integrable (fun x => a x i * b x j) (volume.restrict torusCube) := by
  refine Integrable.of_bound ((ha i).mul (hb j)) (Real.sqrt B1 * Real.sqrt B2) ?_
  filter_upwards [hBa, hBb] with x h1 h2
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (abs_coord_le_sqrt h1 i) (abs_coord_le_sqrt h2 j) (abs_nonneg _)
    ((abs_nonneg _).trans (abs_coord_le_sqrt h1 i))

theorem vecNormSq_eq_two (w : Vec 2) : vecNormSq w = w 0 * w 0 + w 1 * w 1 := by
  simp [vecNormSq, vecDot, Fin.sum_univ_two]

theorem vecNormSq_sub_two (p q : Vec 2) :
    vecNormSq (p - q) = (p 0 * p 0 + p 1 * p 1) + (q 0 * q 0 + q 1 * q 1) - 2 * (p 0 * q 0 + p 1 * q 1) := by
  simp only [vecNormSq_eq_two, Pi.sub_apply]; ring

/-- Slice identity `∫|a-b|² = ∫|a|² + ∫|b|² - 2 ∑ᵢ ∫ aᵢ bᵢ`. -/
theorem integral_vecNormSq_sub
    (ha : ∀ i, AEStronglyMeasurable (fun x => a x i) (volume.restrict torusCube))
    (hb : ∀ i, AEStronglyMeasurable (fun x => b x i) (volume.restrict torusCube))
    (hBa : ∀ᵐ x ∂(volume.restrict torusCube), vecNormSq (a x) ≤ B1)
    (hBb : ∀ᵐ x ∂(volume.restrict torusCube), vecNormSq (b x) ≤ B2) :
    ∫ x in torusCube, vecNormSq (a x - b x) =
      (∫ x in torusCube, (a x 0 * a x 0 + a x 1 * a x 1)) + (∫ x in torusCube, (b x 0 * b x 0 + b x 1 * b x 1)) -
        2 * ∑ i, ∫ x in torusCube, a x i * b x i := by
  have iaa : ∀ i j, Integrable (fun x => a x i * a x j) (volume.restrict torusCube) :=
    fun i j => integrable_cube_coord_mul ha ha hBa hBa i j
  have ibb : ∀ i j, Integrable (fun x => b x i * b x j) (volume.restrict torusCube) :=
    fun i j => integrable_cube_coord_mul hb hb hBb hBb i j
  have iab : ∀ i j, Integrable (fun x => a x i * b x j) (volume.restrict torusCube) :=
    fun i j => integrable_cube_coord_mul ha hb hBa hBb i j
  simp only [vecNormSq_sub_two, Fin.sum_univ_two]
  have i1 : Integrable (fun x => a x 0 * a x 0 + a x 1 * a x 1) (volume.restrict torusCube) :=
    (iaa 0 0).add (iaa 1 1)
  have i2 : Integrable (fun x => b x 0 * b x 0 + b x 1 * b x 1) (volume.restrict torusCube) :=
    (ibb 0 0).add (ibb 1 1)
  have i3 : Integrable (fun x => a x 0 * b x 0 + a x 1 * b x 1) (volume.restrict torusCube) :=
    (iab 0 0).add (iab 1 1)
  have i12 : Integrable (fun x => (a x 0 * a x 0 + a x 1 * a x 1) + (b x 0 * b x 0 + b x 1 * b x 1))
      (volume.restrict torusCube) := i1.add i2
  rw [integral_sub i12 (i3.const_mul 2), integral_add i1 i2, integral_const_mul,
    integral_add (iab 0 0) (iab 1 1)]

end SliceHelpers

theorem energy_ineq_real {T B1 : ℝ} {v₀ : Vec 2 → Vec 2} {v₁ : Vec 2 × ℝ → Vec 2}
    (hv₀ : MemLp v₀ 2 (volume.restrict torusCube)) (hE : HasEnergyInequality T v₀ v₁)
    (hb : EulerBdd T B1 v₁) :
    ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
      (∫ x in torusCube, (v₁ (x, t) 0 * v₁ (x, t) 0 + v₁ (x, t) 1 * v₁ (x, t) 1)) ≤
        ∑ i, ∫ x in torusCube, v₀ x i * v₀ x i := by
  have hm : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ i,
      AEStronglyMeasurable (fun x => v₁ (x, t) i) (volume.restrict torusCube) :=
    ae_all_iff.2 fun i => ae_slice_aesm (hb.coord_aesm i)
  have hbd := ae_slice_bdd hb.bdd
  have hI0 : ∀ i j, Integrable (fun x => v₀ x i * v₀ x j) (volume.restrict torusCube) :=
    fun i j => (hv₀.eval i).integrable_mul (hv₀.eval j)
  have hD : ∫ x in torusCube, vecNormSq (v₀ x) = ∑ i, ∫ x in torusCube, v₀ x i * v₀ x i := by
    simp_rw [vecNormSq_eq_two, Fin.sum_univ_two]
    exact integral_add (hI0 0 0) (hI0 1 1)
  have hR : ENNReal.ofReal (∑ i, ∫ x in torusCube, v₀ x i * v₀ x i) =
      ∫⁻ x in torusCube, ENNReal.ofReal (vecNormSq (v₀ x)) := by
    rw [← hD]
    refine ofReal_integral_eq_lintegral_ofReal ?_ (Filter.Eventually.of_forall fun x => vecNormSq_nonneg' _)
    simp_rw [vecNormSq_eq_two]
    exact (hI0 0 0).add (hI0 1 1)
  filter_upwards [hE, hm, hbd] with t ht hmt hbt
  have hI1 : Integrable (fun x => v₁ (x, t) 0 * v₁ (x, t) 0 + v₁ (x, t) 1 * v₁ (x, t) 1)
      (volume.restrict torusCube) :=
    (integrable_cube_coord_mul hmt hmt hbt hbt 0 0).add (integrable_cube_coord_mul hmt hmt hbt hbt 1 1)
  have hL : ENNReal.ofReal (∫ x in torusCube, (v₁ (x, t) 0 * v₁ (x, t) 0 + v₁ (x, t) 1 * v₁ (x, t) 1)) =
      ∫⁻ x in torusCube, ENNReal.ofReal (vecNormSq (v₁ (x, t))) := by
    rw [ofReal_integral_eq_lintegral_ofReal hI1
      (Filter.Eventually.of_forall fun x => by
        simpa [vecNormSq_eq_two] using vecNormSq_nonneg' (v₁ (x, t)))]
    refine lintegral_congr fun x => ?_
    rw [vecNormSq_eq_two]
  rw [← hL, ← hR] at ht
  have hDnn : 0 ≤ ∑ i, ∫ x in torusCube, v₀ x i * v₀ x i := by
    rw [← hD]
    exact integral_nonneg fun x => vecNormSq_nonneg' _
  exact (ENNReal.ofReal_le_ofReal_iff hDnn).1 ht

/-- **Relative energy inequality.**  The constant `K` is absolute. -/
theorem relative_energy_inequality :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (T : ℝ), 0 < T → ∀ (M : ℝ) (v₀ : Vec 2 → Vec 2) (v₁ v₂ : Vec 2 × ℝ → Vec 2),
      IsEulerWeakSolutionWithDatum T v₀ v₁ → IsEulerWeakSolutionWithDatum T v₀ v₂ →
      (∃ B : ℝ, ∀ᵐ z ∂(eulerMeasure T), vecNormSq (v₁ z) ≤ B) →
      (∃ B : ℝ, ∀ᵐ z ∂(eulerMeasure T), vecNormSq (v₂ z) ≤ B) →
      HasBoundedVorticity T M v₂ → HasEnergyInequality T v₀ v₁ →
      ∃ G : Vec 2 × ℝ → Fin 2 → Fin 2 → ℝ,
        (∀ i j, AEStronglyMeasurable (fun z => G z i j) (eulerMeasure T)) ∧
        (∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ p : ℝ, 2 ≤ p →
          MemLp (fun x => matFrobNorm (G (x, t))) (ENNReal.ofReal p) (volume.restrict torusCube) ∧
          eLpNorm (fun x => matFrobNorm (G (x, t))) (ENNReal.ofReal p) (volume.restrict torusCube) ≤
            ENNReal.ofReal (K * p * M)) ∧
        IntegrableOn (fun s => ∫ x in torusCube, ∑ i, ∑ j,
          (v₁ (x, s) - v₂ (x, s)) j * (v₁ (x, s) - v₂ (x, s)) i * G (x, s) i j) (Icc (0 : ℝ) T) ∧
        ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
          ∫ x in torusCube, vecNormSq (v₁ (x, t) - v₂ (x, t)) ≤
            -2 * ∫ s in Icc (0 : ℝ) t, ∫ x in torusCube, ∑ i, ∑ j,
              (v₁ (x, s) - v₂ (x, s)) j * (v₁ (x, s) - v₂ (x, s)) i * G (x, s) i j := by
  obtain ⟨K, hK, hgrad⟩ := exists_spacetime_gradient
  refine ⟨K, hK, ?_⟩
  intro T hT M v₀ v₁ v₂ h₁ h₂ hb₁ hb₂ hω hE
  obtain ⟨B1, hB1⟩ := hb₁
  obtain ⟨B2, hB2⟩ := hb₂
  obtain ⟨ω, hωm, hωM, hωc⟩ := hω
  have hbu : EulerBdd T (max B1 0) v₁ :=
    ⟨h₁.1.1, h₁.1.2.1, hB1.mono fun z hz => hz.trans (le_max_left _ _), le_max_right _ _⟩
  have hbv : EulerBdd T (max B2 0) v₂ :=
    ⟨h₂.1.1, h₂.1.2.1, hB2.mono fun z hz => hz.trans (le_max_left _ _), le_max_right _ _⟩
  obtain ⟨G, hG, hweak⟩ := hgrad T hT v₂ ω (max B2 0) M hbv h₂.1.2.2.2.1 hωm hωM hωc
  refine ⟨G, hG.aesm, hweak.mono fun t ht p hp => ht.2 p hp, ?_⟩
  have hc1 := cross_identity_time hT h₁ h₂ hbu hbv hG
  have hc2 := cross_identity_time hT h₂ h₂ hbv hbv hG
  have hint1 := integrable_sliceR hbu hbv hG
  have hdiv1 := ae_slice_div hT (integrable_coord_of_bounded hbu.meas hbu.bdd) h₁.1.2.2.2.1
  have hdiv2 := ae_slice_div hT (integrable_coord_of_bounded hbv.meas hbv.bdd) h₂.1.2.2.2.1
  have hmeas1 : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ i,
      AEStronglyMeasurable (fun x => v₁ (x, t) i) (volume.restrict torusCube) :=
    ae_all_iff.2 fun i => ae_slice_aesm (hbu.coord_aesm i)
  have hmeas2 : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ i,
      AEStronglyMeasurable (fun x => v₂ (x, t) i) (volume.restrict torusCube) :=
    ae_all_iff.2 fun i => ae_slice_aesm (hbv.coord_aesm i)
  have hbd1 := ae_slice_bdd hbu.bdd
  have hbd2 := ae_slice_bdd hbv.bdd
  have hE' := energy_ineq_real h₁.2.1 hE hbu
  -- the slice identity `sliceR = Λ`
  have hΛ : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) T)), sliceR v₁ v₂ G s = ∫ x in torusCube, ∑ i, ∑ j,
      (v₁ (x, s) - v₂ (x, s)) j * (v₁ (x, s) - v₂ (x, s)) i * G (x, s) i j := by
    filter_upwards [hG.slice, hdiv1, hdiv2, hmeas1, hbd1] with s hs d1 d2 m1 b1
    rw [slice_sliceR_eq hs m1 b1 d1 d2, slice_relLam_eq hs m1 b1]
  refine ⟨hint1.congr hΛ, ?_⟩
  have hsR : ∀ s, sliceR v₂ v₂ G s = 0 := fun s => by simp [sliceR]
  have hmem : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), t ∈ Icc (0 : ℝ) T := ae_restrict_mem measurableSet_Icc
  filter_upwards [hc1, hc2, hE', hmeas1, hmeas2, hbd1, hbd2, hmem] with t h1 h2 h3 m1 m2 b1 b2 htm
  have hΛt : ∫ s in Icc (0 : ℝ) t, sliceR v₁ v₂ G s = ∫ s in Icc (0 : ℝ) t, ∫ x in torusCube, ∑ i, ∑ j,
      (v₁ (x, s) - v₂ (x, s)) j * (v₁ (x, s) - v₂ (x, s)) i * G (x, s) i j := by
    refine integral_congr_ae ?_
    exact ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc_right htm.2) hΛ
  simp only [hsR, integral_zero, add_zero] at h2
  rw [hΛt] at h1
  have hsub := integral_vecNormSq_sub (a := fun x => v₁ (x, t)) (b := fun x => v₂ (x, t)) m1 m2 b1 b2
  have hI22 : ∑ i, ∫ x in torusCube, v₂ (x, t) i * v₂ (x, t) i =
      ∫ x in torusCube, (v₂ (x, t) 0 * v₂ (x, t) 0 + v₂ (x, t) 1 * v₂ (x, t) 1) := by
    simp only [Fin.sum_univ_two]
    exact (integral_add (integrable_cube_coord_mul m2 m2 b2 b2 0 0)
      (integrable_cube_coord_mul m2 m2 b2 b2 1 1)).symm
  have h12 : sliceDot v₁ v₂ t = ∑ i, ∫ x in torusCube, v₁ (x, t) i * v₂ (x, t) i := rfl
  have h22 : sliceDot v₂ v₂ t = ∑ i, ∫ x in torusCube, v₂ (x, t) i * v₂ (x, t) i := rfl
  rw [hsub, ← h12, h1, ← hI22, ← h22, h2]
  linarith

end PDE
