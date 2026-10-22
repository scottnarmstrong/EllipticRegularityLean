module

public import PDEFoundation.Monotonicity.ACF.WeightedMain
public import PDEFoundation.Monotonicity.ACF.SliceRayleigh

/-!
# ACF-A: the weighted energy as the integral of its slice density

`acfWeightedEnergy G r = ofReal (∫₀ʳ dens G)` with `dens G ρ = ∫_{∂B_ρ} |G|² |x|^{2-d}`, and
`dens G ρ = ρ^{2-d} ∫_{∂B_ρ} |G|²`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

namespace ACFAssembly

noncomputable section

variable {d : ℕ}

/-- The slice density `ρ ↦ ∫_{∂B_ρ} |G|² |x|^{2-d}` of the weighted energy. -/
def dens (G : Vec d → Vec d) (ρ : ℝ) : ℝ :=
  sphereIntegral (0 : Vec d) ρ (fun x => vecNormSq (G x) / vecEuclideanNorm x ^ (d - 2))

theorem vecEuclideanNorm_of_mem_sphere {ρ : ℝ} (hρ : 0 ≤ ρ) {x : Vec d}
    (hx : x ∈ euclideanSphere (0 : Vec d) ρ) : vecEuclideanNorm x = ρ := by
  have := mem_euclideanSphere_zero_iff.1 hx
  unfold vecEuclideanNorm
  rw [this]
  exact Real.sqrt_sq hρ

theorem dens_nonneg (G : Vec d → Vec d) {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 ≤ dens G ρ :=
  sphereIntegral_zero_nonneg hρ fun _ _ =>
    div_nonneg (vecNormSq_nonneg _) (pow_nonneg (vecEuclideanNorm_nonneg _) _)

theorem dens_eq (G : Vec d → Vec d) {ρ : ℝ} (hρ : 0 < ρ) :
    dens G ρ = (ρ ^ (d - 2))⁻¹ * acfSliceGrad G ρ := by
  unfold dens acfSliceGrad
  have h1 : sphereIntegral (0 : Vec d) ρ (fun x => vecNormSq (G x) / vecEuclideanNorm x ^ (d - 2)) =
      sphereIntegral (0 : Vec d) ρ (fun x => (ρ ^ (d - 2))⁻¹ * vecNormSq (G x)) := by
    refine sphereIntegral_zero_congr fun x hx => ?_
    simp only [vecEuclideanNorm_of_mem_sphere hρ.le hx]
    rw [div_eq_inv_mul]
  rw [h1]
  unfold sphereIntegral
  rw [integral_const_mul]
  ring

/-- Finite weighted energy makes the weighted density integrable. -/
theorem integrableOn_weighted {R r : ℝ} (u : H1Function (euclideanBall (0 : Vec d) R))
    (hr : 0 < r) (hrR : r ≤ R) (hfin : acfWeightedEnergy u.grad r ≠ ⊤) :
    IntegrableOn (fun x => vecNormSq (u.grad x) / vecEuclideanNorm x ^ (d - 2))
      (euclideanBall (0 : Vec d) r) := by
  have hsub : euclideanBall (0 : Vec d) r ⊆ euclideanBall (0 : Vec d) R :=
    euclideanBall_mono hr.le hrR
  have hm : AEStronglyMeasurable (fun x => vecNormSq (u.grad x) / vecEuclideanNorm x ^ (d - 2))
      (volume.restrict (euclideanBall (0 : Vec d) r)) := by
    simp only [div_eq_mul_inv]
    exact ((aesm_vecNormSq_grad u).mono_measure (Measure.restrict_mono hsub le_rfl)).mul
      ((measurable_vecEuclideanNorm.pow_const _).inv).aestronglyMeasurable
  refine ⟨hm, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal]
  · exact lt_top_iff_ne_top.2 hfin
  · exact Filter.Eventually.of_forall fun x =>
      div_nonneg (vecNormSq_nonneg _) (pow_nonneg (vecEuclideanNorm_nonneg _) _)

/-- `acfWeightedEnergy G r = ofReal ∫₀ʳ dens G` for an integrable weighted density. -/
theorem acfWeightedEnergy_eq [NeZero d] {G : Vec d → Vec d} {r : ℝ} (hr : 0 < r)
    (hf : IntegrableOn (fun x => vecNormSq (G x) / vecEuclideanNorm x ^ (d - 2))
      (euclideanBall (0 : Vec d) r)) :
    acfWeightedEnergy G r = ENNReal.ofReal (∫ ρ in (0 : ℝ)..r, dens G ρ) ∧
      IntervalIntegrable (dens G) volume 0 r := by
  set f : Vec d → ℝ := fun x => vecNormSq (G x) / vecEuclideanNorm x ^ (d - 2) with hfdef
  have hmeas : MeasurableSet (euclideanBall (0 : Vec d) r) :=
    (isOpen_euclideanBall (0 : Vec d) r).measurableSet
  have hg : Integrable ((euclideanBall (0 : Vec d) r).indicator f) :=
    (integrable_indicator_iff hmeas).mpr hf
  obtain ⟨-, -, h3⟩ := polar_package hg
  have hdens : IntegrableOn (dens G) (Ioo 0 r) := integrableOn_slice_of_integrableOn hf
  have hnn : ∀ x, 0 ≤ f x := fun x =>
    div_nonneg (vecNormSq_nonneg _) (pow_nonneg (vecEuclideanNorm_nonneg _) _)
  have hB : ∫ ρ in Ioi (0 : ℝ), sphereIntegral (0 : Vec d) ρ
        ((euclideanBall (0 : Vec d) r).indicator f) =
      ∫ ρ in Ioo (0 : ℝ) r, sphereIntegral (0 : Vec d) ρ
        ((euclideanBall (0 : Vec d) r).indicator f) := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun ρ hρ => hρ.1) fun ρ hρ => ?_
    have hρ0 : 0 < ρ := mem_Ioi.1 hρ.1
    have hrρ : r ≤ ρ := by
      by_contra h
      exact hρ.2 ⟨hρ0, not_le.1 h⟩
    have : sphereIntegral (0 : Vec d) ρ ((euclideanBall (0 : Vec d) r).indicator f) =
        sphereIntegral (0 : Vec d) ρ (fun _ => 0) := by
      refine sphereIntegral_zero_congr fun x hx => ?_
      have hn := vecEuclideanNorm_of_mem_sphere hρ0.le hx
      have hnot : x ∉ euclideanBall (0 : Vec d) r := by
        rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hr, sub_zero, hn]
        exact not_lt.2 hrρ
      simp [hnot]
    rw [this]
    simp [sphereIntegral]
  have hC : ∫ ρ in Ioo (0 : ℝ) r, sphereIntegral (0 : Vec d) ρ
        ((euclideanBall (0 : Vec d) r).indicator f) = ∫ ρ in Ioo (0 : ℝ) r, dens G ρ :=
    setIntegral_congr_fun measurableSet_Ioo fun ρ hρ =>
      sphereIntegral_congr_ball hρ.1.le hρ.2 (fun x hx => by simp only [indicator_of_mem hx]; rfl)
  have hint : ∫ ρ in (0 : ℝ)..r, dens G ρ = ∫ x in euclideanBall (0 : Vec d) r, f x := by
    rw [intervalIntegral.integral_of_le hr.le, integral_Ioc_eq_integral_Ioo, ← hC, ← hB,
      ← h3, integral_indicator hmeas]
  refine ⟨?_, (intervalIntegrable_iff_integrableOn_Ioo_of_le hr.le).2 hdens⟩
  rw [hint, ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall hnn)]
  rfl

end

end ACFAssembly

end PDE
