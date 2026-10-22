module

public import EllipticRegularity.DeGiorgi.Assembly.Statements
public import PDEFoundation.Measure.AffineVolume
public import PDEFoundation.Geometry.EuclideanBall.Interior
public import PDEFoundation.Measure.BallVolume

/-!
# Affine change of variables for the assembly

Exact transport of restricted volume, `L^p` norms and essential extrema under the
affine map `y ↦ x₀ + r y` (`r > 0`) between round Euclidean balls.
-/

@[expose] public section

open scoped ENNReal Pointwise

namespace PDE.DGNMAssembly

open MeasureTheory Filter

variable {d : ℕ}

/-- The affine homeomorphism `y ↦ x₀ + r y`. -/
noncomputable def affEquiv (x₀ : Vec d) {r : ℝ} (hr : 0 < r) : Vec d ≃ₜ Vec d :=
  (Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft x₀)

theorem affEquiv_apply (x₀ : Vec d) {r : ℝ} (hr : 0 < r) (y : Vec d) :
    affEquiv x₀ hr y = x₀ + r • y := rfl

theorem measurableEmbedding_aff (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    MeasurableEmbedding fun y : Vec d => x₀ + r • y :=
  (affEquiv x₀ hr).measurableEmbedding

theorem aff_mem_ball_iff (x₀ y : Vec d) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) :
    x₀ + r • y ∈ euclideanBall x₀ (r * ρ) ↔ y ∈ euclideanBall (0 : Vec d) ρ := by
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (mul_pos hr hρ),
    mem_euclideanBall_iff_vecEuclideanNorm_lt hρ]
  simp only [add_sub_cancel_left, sub_zero, vecEuclideanNorm_smul, abs_of_pos hr]
  exact mul_lt_mul_iff_right₀ hr

theorem aff_image_ball (x₀ : Vec d) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) :
    (fun y : Vec d => x₀ + r • y) '' euclideanBall (0 : Vec d) ρ =
      euclideanBall x₀ (r * ρ) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (aff_mem_ball_iff x₀ y hr hρ).2 hy
  · intro hx
    refine ⟨r⁻¹ • (x - x₀), ?_, ?_⟩
    · rw [← aff_mem_ball_iff x₀ _ hr hρ]
      simpa [smul_smul, hr.ne'] using hx
    · simp [smul_smul, hr.ne']

theorem aff_preimage_ball (x₀ : Vec d) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) :
    (fun y : Vec d => x₀ + r • y) ⁻¹' euclideanBall x₀ (r * ρ) =
      euclideanBall (0 : Vec d) ρ := by
  ext y
  exact aff_mem_ball_iff x₀ y hr hρ

/-- Pushforward of restricted volume under `y ↦ x₀ + r y`. -/
theorem map_aff_volumeOn (x₀ : Vec d) {r : ℝ} (hr : 0 < r) (S : Set (Vec d)) :
    Measure.map (fun y : Vec d => x₀ + r • y) (volumeOn S) =
      ENNReal.ofReal ((r ^ d)⁻¹) •
        volumeOn ((fun y : Vec d => x₀ + r • y) '' S) := by
  have hT : (fun y : Vec d => x₀ + r • y) =
      (fun z : Vec d => x₀ + z) ∘ (fun y : Vec d => r • y) := rfl
  have hvol : Measure.map (fun y : Vec d => x₀ + r • y) (volume : Measure (Vec d)) =
      ENNReal.ofReal ((r ^ d)⁻¹) • volume := by
    rw [hT, ← Measure.map_map (measurable_const_add x₀) (measurable_const_smul r)]
    have h1 := map_smul_volumeOn_of_pos (d := d) hr Set.univ
    simp only [volumeOn, Measure.restrict_univ, Set.smul_set_univ₀ hr.ne'] at h1
    rw [h1, Measure.map_smul, map_add_left_eq_self]
    exact (measurable_const_add x₀).aemeasurable
  have hemb := (affEquiv x₀ hr).toMeasurableEquiv.restrict_map (volume : Measure (Vec d))
    ((fun y : Vec d => x₀ + r • y) '' S)
  have himg : (affEquiv x₀ hr).toMeasurableEquiv ⁻¹'
      ((fun y : Vec d => x₀ + r • y) '' S) = S := by
    exact (measurableEmbedding_aff x₀ hr).injective.preimage_image S
  rw [himg] at hemb
  have hmap : (volume : Measure (Vec d)).map (affEquiv x₀ hr).toMeasurableEquiv =
      ENNReal.ofReal ((r ^ d)⁻¹) • volume := hvol
  rw [hmap, Measure.restrict_smul] at hemb
  exact hemb.symm

theorem ofReal_inv_pow_ne_zero {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal ((r ^ d)⁻¹) ≠ 0 :=
  (ENNReal.ofReal_pos.2 (inv_pos.2 (pow_pos hr d))).ne'

theorem volumeOn_preimage_aff (x₀ : Vec d) {r : ℝ} (hr : 0 < r) (S : Set (Vec d))
    (A : Set (Vec d)) :
    volumeOn S ((fun y : Vec d => x₀ + r • y) ⁻¹' A) =
      ENNReal.ofReal ((r ^ d)⁻¹) *
        volumeOn ((fun y : Vec d => x₀ + r • y) '' S) A := by
  rw [← (measurableEmbedding_aff x₀ hr).map_apply, map_aff_volumeOn x₀ hr S]
  simp

theorem volumeOn_preimage_aff_eq_zero_iff (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (S A : Set (Vec d)) :
    volumeOn S ((fun y : Vec d => x₀ + r • y) ⁻¹' A) = 0 ↔
      volumeOn ((fun y : Vec d => x₀ + r • y) '' S) A = 0 := by
  rw [volumeOn_preimage_aff x₀ hr, mul_eq_zero]
  simp [ofReal_inv_pow_ne_zero hr]

theorem ae_comp_aff_iff (x₀ : Vec d) {r : ℝ} (hr : 0 < r) (S : Set (Vec d))
    (P : Vec d → Prop) :
    (∀ᵐ y ∂volumeOn S, P (x₀ + r • y)) ↔
      ∀ᵐ x ∂volumeOn ((fun y : Vec d => x₀ + r • y) '' S), P x := by
  simp only [ae_iff]
  exact volumeOn_preimage_aff_eq_zero_iff x₀ hr S {x | ¬ P x}

theorem ae_ball_comp_aff_iff (x₀ : Vec d) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (P : Vec d → Prop) :
    (∀ᵐ y ∂volumeOn (euclideanBall (0 : Vec d) ρ), P (x₀ + r • y)) ↔
      ∀ᵐ x ∂volumeOn (euclideanBall x₀ (r * ρ)), P x := by
  rw [ae_comp_aff_iff x₀ hr, aff_image_ball x₀ hr hρ]

theorem eLpNorm_comp_aff_ball {E : Type*} [NormedAddCommGroup E] (x₀ : Vec d) {r ρ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (p : ℝ≥0∞) (f : Vec d → E) :
    eLpNorm (fun y => f (x₀ + r • y)) p (volumeOn (euclideanBall (0 : Vec d) ρ)) =
      ENNReal.ofReal ((r ^ d)⁻¹) ^ (1 / p).toReal *
        eLpNorm f p (volumeOn (euclideanBall x₀ (r * ρ))) := by
  have h := (measurableEmbedding_aff x₀ hr).eLpNorm_map_measure (g := f) (p := p)
    (μ := volumeOn (euclideanBall (0 : Vec d) ρ))
  rw [map_aff_volumeOn x₀ hr, aff_image_ball x₀ hr hρ,
    eLpNorm_smul_measure_of_ne_zero (ofReal_inv_pow_ne_zero hr)] at h
  rw [← Function.comp_def f, ← h]
  simp

theorem essSup_comp_aff_ball (x₀ : Vec d) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (g : Vec d → ℝ≥0∞) :
    essSup (fun y => g (x₀ + r • y)) (volumeOn (euclideanBall (0 : Vec d) ρ)) =
      essSup g (volumeOn (euclideanBall x₀ (r * ρ))) := by
  rw [essSup_eq_sInf, essSup_eq_sInf]
  congr 1
  ext a
  simp only [Set.mem_ofPred_eq]
  have := volumeOn_preimage_aff_eq_zero_iff x₀ hr (euclideanBall (0 : Vec d) ρ)
    {x | a < g x}
  rw [aff_image_ball x₀ hr hρ] at this
  exact this

theorem essInf_comp_aff_ball (x₀ : Vec d) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (g : Vec d → ℝ≥0∞) :
    essInf (fun y => g (x₀ + r • y)) (volumeOn (euclideanBall (0 : Vec d) ρ)) =
      essInf g (volumeOn (euclideanBall x₀ (r * ρ))) := by
  rw [essInf_eq_sSup, essInf_eq_sSup]
  congr 1
  ext a
  simp only [Set.mem_ofPred_eq]
  have := volumeOn_preimage_aff_eq_zero_iff x₀ hr (euclideanBall (0 : Vec d) ρ)
    {x | g x < a}
  rw [aff_image_ball x₀ hr hρ] at this
  exact this

theorem lintegral_comp_aff_ball (x₀ : Vec d) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (g : Vec d → ℝ≥0∞) :
    ∫⁻ y in euclideanBall (0 : Vec d) ρ, g (x₀ + r • y) =
      ENNReal.ofReal ((r ^ d)⁻¹) * ∫⁻ x in euclideanBall x₀ (r * ρ), g x := by
  have h := (measurableEmbedding_aff x₀ hr).lintegral_map g
    (μ := volumeOn (euclideanBall (0 : Vec d) ρ))
  rw [map_aff_volumeOn x₀ hr, aff_image_ball x₀ hr hρ, lintegral_smul_measure] at h
  exact h.symm

theorem one_le_of_elliptic {Λ : ℝ} {a : CoeffField d}
    (hell : ∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) :
    1 ≤ Λ :=
  (hell 0 (center_mem_euclideanBall 0 one_pos)).2.1

theorem aemeasurable_comp_aff (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (hsub : euclideanBall x₀ r ⊆ euclideanBall (0 : Vec d) 1) {f : Vec d → ℝ}
    (hf : AEMeasurable f (volumeOn (euclideanBall (0 : Vec d) 1))) :
    AEMeasurable (fun y => f (x₀ + r • y)) (volumeOn (euclideanBall (0 : Vec d) 1)) := by
  have hmap := map_aff_volumeOn x₀ hr (euclideanBall (0 : Vec d) 1)
  rw [show (fun y : Vec d => x₀ + r • y) '' euclideanBall (0 : Vec d) 1 =
      euclideanBall x₀ r by simpa using aff_image_ball x₀ hr (one_pos : (0 : ℝ) < 1)] at hmap
  have hle : Measure.map (fun y : Vec d => x₀ + r • y) (volumeOn (euclideanBall (0 : Vec d) 1)) ≤
      ENNReal.ofReal ((r ^ d)⁻¹) • volumeOn (euclideanBall (0 : Vec d) 1) := by
    rw [hmap]
    gcongr
    exact Measure.restrict_mono hsub le_rfl
  have h1 : AEMeasurable f (Measure.map (fun y : Vec d => x₀ + r • y)
      (volumeOn (euclideanBall (0 : Vec d) 1))) :=
    (hf.smul_measure _).mono_measure hle
  exact h1.comp_measurable (measurableEmbedding_aff x₀ hr).measurable

theorem coeff_comp_aff {Λ : ℝ} {a : CoeffField d}
    (hmeas : ∀ i j : Fin d, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x))
    (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (hsub : euclideanBall x₀ r ⊆ euclideanBall (0 : Vec d) 1) :
    (∀ i j : Fin d, AEMeasurable (fun y => (fun y => a (x₀ + r • y)) y i j)
      (volumeOn (euclideanBall (0 : Vec d) 1))) ∧
    (∀ y ∈ euclideanBall (0 : Vec d) 1,
      IsEllipticMatrix 1 Λ ((fun y => a (x₀ + r • y)) y)) := by
  refine ⟨fun i j => aemeasurable_comp_aff x₀ hr hsub (f := fun x => a x i j) (hmeas i j), ?_⟩
  intro y hy
  apply hell
  have : x₀ + r • y ∈ euclideanBall x₀ (r * 1) := (aff_mem_ball_iff x₀ y hr one_pos).2 hy
  exact hsub (by simpa using this)

theorem ae_pos_comp_aff {u : Vec d → ℝ}
    (hpos : ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < u x)
    (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (hsub : euclideanBall x₀ r ⊆ euclideanBall (0 : Vec d) 1) :
    ∀ᵐ y ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < u (x₀ + r • y) := by
  have h2 := (ae_ball_comp_aff_iff x₀ hr (one_pos : (0 : ℝ) < 1) (fun x => 0 < u x)).2
    (by
      rw [mul_one]
      exact ae_mono (Measure.restrict_mono hsub le_rfl) hpos)
  exact h2

end PDE.DGNMAssembly
