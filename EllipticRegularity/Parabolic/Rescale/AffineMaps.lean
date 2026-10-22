module

public import EllipticRegularity.Parabolic.Rescale.AffineMeasure

/-!
# The parabolic rescaling maps

`Ψ y = c + r • y`, `τ s = T₀ + r ^ 2 * s` and `Φ = Prod.map Ψ τ` are measurable embeddings that
push volume to a constant multiple of volume, and map the unit cylinder
`B₁ × (-1, 0]` onto `B(c, r) × (T₀ - r², T₀]`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.Rescale

/-- The spatial affine map `y ↦ c + r • y`. -/
def spaceMap {d : ℕ} (c : Vec d) (r : ℝ) : Vec d → Vec d := fun y => c + r • y

/-- The parabolic time map `s ↦ T₀ + r ^ 2 * s`. -/
def timeMap (T₀ r : ℝ) : ℝ → ℝ := fun s => T₀ + r ^ 2 * s

/-- The parabolic rescaling `Φ(y, s) = (c + r • y, T₀ + r ^ 2 * s)`. -/
def cylMap {d : ℕ} (c : Vec d) (r T₀ : ℝ) : Vec d × ℝ → Vec d × ℝ :=
  Prod.map (spaceMap c r) (timeMap T₀ r)

variable {d : ℕ}

theorem spaceMap_apply (c : Vec d) (r : ℝ) (y : Vec d) : spaceMap c r y = c + r • y := rfl

theorem timeMap_apply (T₀ r s : ℝ) : timeMap T₀ r s = T₀ + r ^ 2 * s := rfl

theorem cylMap_apply (c : Vec d) (r T₀ : ℝ) (z : Vec d × ℝ) :
    cylMap c r T₀ z = (c + r • z.1, T₀ + r ^ 2 * z.2) := rfl

theorem continuous_spaceMap (c : Vec d) (r : ℝ) : Continuous (spaceMap c r) := by
  unfold spaceMap; fun_prop

theorem continuous_timeMap (T₀ r : ℝ) : Continuous (timeMap T₀ r) := by
  unfold timeMap; fun_prop

theorem spaceMap_measurableEmbedding (c : Vec d) {r : ℝ} (hr : 0 < r) :
    MeasurableEmbedding (spaceMap c r) :=
  ((Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft c)).measurableEmbedding

theorem timeMap_measurableEmbedding (T₀ : ℝ) {r : ℝ} (hr : 0 < r) :
    MeasurableEmbedding (timeMap T₀ r) :=
  ((Homeomorph.mulLeft₀ (r ^ 2) (pow_pos hr 2).ne').trans
    (Homeomorph.addLeft T₀)).measurableEmbedding

theorem cylMap_measurableEmbedding (c : Vec d) {r : ℝ} (hr : 0 < r) (T₀ : ℝ) :
    MeasurableEmbedding (cylMap c r T₀) :=
  (Homeomorph.prodCongr
    ((Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft c))
    ((Homeomorph.mulLeft₀ (r ^ 2) (pow_pos hr 2).ne').trans
      (Homeomorph.addLeft T₀))).measurableEmbedding

theorem map_spaceMap_volume (c : Vec d) {r : ℝ} (hr : 0 < r) :
    (volume : Measure (Vec d)).map (spaceMap c r) =
      ENNReal.ofReal ((r ^ d)⁻¹) • volume := by
  have h1 : (volume : Measure (Vec d)).map (fun x : Vec d => r • x) =
      ENNReal.ofReal ((r ^ d)⁻¹) • volume := by
    have h := PDE.map_smul_volumeOn_of_pos (d := d) hr univ
    simpa [PDE.volumeOn, Set.smul_set_univ₀ hr.ne'] using h
  have h2 : spaceMap c r = (fun x : Vec d => c + x) ∘ (fun x : Vec d => r • x) := rfl
  rw [h2, ← Measure.map_map (measurable_const_add c) (measurable_const_smul r), h1,
    Measure.map_smul _ (measurable_const_add c).aemeasurable,
    (measurePreserving_add_left (volume : Measure (Vec d)) c).map_eq]

theorem map_timeMap_volume (T₀ : ℝ) {r : ℝ} (hr : 0 < r) :
    (volume : Measure ℝ).map (timeMap T₀ r) =
      ENNReal.ofReal ((r ^ 2)⁻¹) • volume := by
  have h1 := Real.map_volume_mul_left (pow_pos hr 2).ne'
  have h2 : timeMap T₀ r = (fun x : ℝ => T₀ + x) ∘ (fun x : ℝ => r ^ 2 * x) := rfl
  rw [abs_of_pos (inv_pos.2 (pow_pos hr 2))] at h1
  rw [h2, ← Measure.map_map (measurable_const_add T₀) (measurable_const_mul (r ^ 2)), h1,
    Measure.map_smul _ (measurable_const_add T₀).aemeasurable,
    (measurePreserving_add_left (volume : Measure ℝ) T₀).map_eq]

theorem map_cylMap_volume (c : Vec d) {r : ℝ} (hr : 0 < r) (T₀ : ℝ) :
    (volume : Measure (Vec d × ℝ)).map (cylMap c r T₀) =
      ENNReal.ofReal ((r ^ (d + 2))⁻¹) • volume := by
  have hΨ : Measurable (spaceMap c r) := (spaceMap_measurableEmbedding c hr).measurable
  have hτ : Measurable (timeMap T₀ r) := (timeMap_measurableEmbedding T₀ hr).measurable
  rw [Measure.volume_eq_prod, cylMap, ← Measure.map_prod_map _ _ hΨ hτ,
    map_spaceMap_volume c hr, map_timeMap_volume T₀ hr, Measure.prod_smul_left,
    Measure.prod_smul_right, smul_smul, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [← mul_inv, ← pow_add]

theorem map_restrict_spaceMap (c : Vec d) {r : ℝ} (hr : 0 < r) (S : Set (Vec d)) :
    ((volume : Measure (Vec d)).restrict S).map (spaceMap c r) =
      ENNReal.ofReal ((r ^ d)⁻¹) • (volume : Measure (Vec d)).restrict (spaceMap c r '' S) := by
  rw [map_restrict_of_embedding (spaceMap_measurableEmbedding c hr), map_spaceMap_volume c hr,
    Measure.restrict_smul]

theorem map_restrict_timeMap (T₀ : ℝ) {r : ℝ} (hr : 0 < r) (S : Set ℝ) :
    ((volume : Measure ℝ).restrict S).map (timeMap T₀ r) =
      ENNReal.ofReal ((r ^ 2)⁻¹) • (volume : Measure ℝ).restrict (timeMap T₀ r '' S) := by
  rw [map_restrict_of_embedding (timeMap_measurableEmbedding T₀ hr), map_timeMap_volume T₀ hr,
    Measure.restrict_smul]

theorem map_restrict_cylMap (c : Vec d) {r : ℝ} (hr : 0 < r) (T₀ : ℝ) (S : Set (Vec d × ℝ)) :
    ((volume : Measure (Vec d × ℝ)).restrict S).map (cylMap c r T₀) =
      ENNReal.ofReal ((r ^ (d + 2))⁻¹) •
        (volume : Measure (Vec d × ℝ)).restrict (cylMap c r T₀ '' S) := by
  rw [map_restrict_of_embedding (cylMap_measurableEmbedding c hr T₀), map_cylMap_volume c hr T₀,
    Measure.restrict_smul]

theorem ofReal_inv_pow_ne_zero {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ENNReal.ofReal ((r ^ n)⁻¹) ≠ 0 := by
  simp [pow_pos hr n]

theorem ofReal_ne_top (x : ℝ) : ENNReal.ofReal x ≠ ∞ := ENNReal.ofReal_ne_top

theorem euclideanSqDist_spaceMap (c : Vec d) (r : ℝ) (y w : Vec d) :
    euclideanSqDist (spaceMap c r y) (spaceMap c r w) = r ^ 2 * euclideanSqDist y w := by
  have h : spaceMap c r y = r • y + c := by rw [spaceMap_apply, add_comm]
  have h' : spaceMap c r w = r • w + c := by rw [spaceMap_apply, add_comm]
  rw [h, h', euclideanSqDist_add_right, euclideanSqDist_smul_smul]

theorem spaceMap_image_euclideanBall (c w : Vec d) {r : ℝ} (hr : 0 < r) (ρ : ℝ) :
    spaceMap c r '' euclideanBall w ρ = euclideanBall (spaceMap c r w) (r * ρ) := by
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    change euclideanSqDist _ _ < _
    rw [euclideanSqDist_spaceMap, mul_pow]
    exact mul_lt_mul_of_pos_left hy hr2
  · intro hz
    have hinv : spaceMap c r (r⁻¹ • (z - c)) = z := by
      ext i
      simp [spaceMap_apply, hr.ne']
    refine ⟨r⁻¹ • (z - c), ?_, hinv⟩
    have hz' : euclideanSqDist (spaceMap c r (r⁻¹ • (z - c))) (spaceMap c r w) < (r * ρ) ^ 2 := by
      rw [hinv]; exact hz
    rw [euclideanSqDist_spaceMap, mul_pow] at hz'
    exact lt_of_mul_lt_mul_left hz' hr2.le

theorem spaceMap_image_unitBall (c : Vec d) {r : ℝ} (hr : 0 < r) :
    spaceMap c r '' euclideanBall (0 : Vec d) 1 = euclideanBall c r := by
  rw [spaceMap_image_euclideanBall c 0 hr 1]
  simp [spaceMap_apply]

theorem timeMap_image_Ioc (T₀ : ℝ) {r : ℝ} (hr : 0 < r) :
    timeMap T₀ r '' Ioc (-1 : ℝ) 0 = Ioc (T₀ - r ^ 2) T₀ := by
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  ext t
  constructor
  · rintro ⟨s, ⟨h1, h2⟩, rfl⟩
    rw [timeMap_apply]
    constructor
    · have := mul_lt_mul_of_pos_left h1 hr2
      linarith only [this]
    · have := mul_nonpos_of_nonneg_of_nonpos hr2.le h2
      linarith only [this]
  · rintro ⟨h1, h2⟩
    refine ⟨(t - T₀) / r ^ 2, ⟨?_, ?_⟩, ?_⟩
    · rw [lt_div_iff₀ hr2]; linarith only [h1]
    · exact div_nonpos_of_nonpos_of_nonneg (by linarith only [h2]) hr2.le
    · rw [timeMap_apply]; field_simp; ring

theorem cylMap_image_prod (c : Vec d) (r T₀ : ℝ) (S : Set (Vec d)) (J : Set ℝ) :
    cylMap c r T₀ '' (S ×ˢ J) = (spaceMap c r '' S) ×ˢ (timeMap T₀ r '' J) :=
  (Set.prod_image_image_eq).symm

end PDE.Parabolic.Rescale
