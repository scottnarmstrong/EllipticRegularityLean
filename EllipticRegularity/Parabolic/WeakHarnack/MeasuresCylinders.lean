module

public import EllipticRegularity.Parabolic.WeakHarnack.Geometry
public import PDEFoundation.Measure.BallVolume

/-!
# Measure-theoretic facts about the weak Harnack cylinders

Measurability, monotonicity in `σ ∈ [1/2,1]` (in the form required by `PDE.Bombieri.bombieri_giusti`
with `δ = 1/2`), containment in `B₁ × (-1,0]`, explicit volumes and the spatial/time gaps for the
three families `posCyl`, `negCyl`, `negCylInner` of `Geometry.lean`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.WeakHarnack

variable {d : ℕ}

/-! ### Parameters of the families -/

/-- Spatial radius of `posCyl d σ`. -/
noncomputable def posR (σ : ℝ) : ℝ := 1 / 2 + (σ - 1 / 2) / 2
/-- Lower time end of `posCyl d σ`. -/
noncomputable def posLo (σ : ℝ) : ℝ := -3 / 4 - (σ - 1 / 2) / 4
/-- Upper time end of `posCyl d σ`. -/
noncomputable def posHi (σ : ℝ) : ℝ := -1 / 2 + (σ - 1 / 2) / 4
/-- Spatial radius of `negCyl d σ`. -/
noncomputable def negR (σ : ℝ) : ℝ := 5 / 8 + (σ - 1 / 2) / 4
/-- Lower time end of `negCyl d σ`. -/
noncomputable def negLo (σ : ℝ) : ℝ := -5 / 16 - (σ - 1 / 2) / 16
/-- Spatial radius of `negCylInner d σ`. -/
noncomputable def innR (σ : ℝ) : ℝ := 1 / 2 + (σ - 1 / 2) / 4
/-- Lower time end of `negCylInner d σ`. -/
noncomputable def innLo (σ : ℝ) : ℝ := -1 / 4 - (σ - 1 / 2) / 8

theorem posCyl_eq (σ : ℝ) : posCyl d σ = euclideanBall (0 : Vec d) (posR σ) ×ˢ Ioo (posLo σ) (posHi σ) :=
  rfl
theorem negCyl_eq (σ : ℝ) : negCyl d σ = euclideanBall (0 : Vec d) (negR σ) ×ˢ Ioc (negLo σ) 0 := rfl
theorem negCylInner_eq (σ : ℝ) :
    negCylInner d σ = euclideanBall (0 : Vec d) (innR σ) ×ˢ Ioc (innLo σ) 0 := rfl

/-! ### Gap facts -/

theorem posR_sub {σ' σ : ℝ} : posR σ - posR σ' = (σ - σ') / 2 := by unfold posR; ring
theorem posLo_sub {σ' σ : ℝ} : posLo σ' - posLo σ = (σ - σ') / 4 := by unfold posLo; ring
theorem posHi_sub {σ' σ : ℝ} : posHi σ - posHi σ' = (σ - σ') / 4 := by unfold posHi; ring
theorem negR_sub {σ' σ : ℝ} : negR σ - negR σ' = (σ - σ') / 4 := by unfold negR; ring
theorem negLo_sub {σ' σ : ℝ} : negLo σ' - negLo σ = (σ - σ') / 16 := by unfold negLo; ring
theorem innR_sub {σ' σ : ℝ} : innR σ - innR σ' = (σ - σ') / 4 := by unfold innR; ring
theorem innLo_sub {σ' σ : ℝ} : innLo σ' - innLo σ = (σ - σ') / 8 := by unfold innLo; ring

/-! ### Measurability, monotonicity, containment -/

theorem measurableSet_posCyl (σ : ℝ) : MeasurableSet (posCyl d σ) :=
  (measurableSet_euclideanBall _ _).prod measurableSet_Ioo
theorem measurableSet_negCyl (σ : ℝ) : MeasurableSet (negCyl d σ) :=
  (measurableSet_euclideanBall _ _).prod measurableSet_Ioc
theorem measurableSet_negCylInner (σ : ℝ) : MeasurableSet (negCylInner d σ) :=
  (measurableSet_euclideanBall _ _).prod measurableSet_Ioc

theorem posCyl_mono {σ' σ : ℝ} (h1 : 1 / 2 ≤ σ') (h2 : σ' ≤ σ) : posCyl d σ' ⊆ posCyl d σ := by
  refine prod_mono (euclideanBall_mono (by linarith) (by linarith))
    (Ioo_subset_Ioo (by linarith) (by linarith))

theorem negCyl_mono {σ' σ : ℝ} (h1 : 1 / 2 ≤ σ') (h2 : σ' ≤ σ) : negCyl d σ' ⊆ negCyl d σ :=
  prod_mono (euclideanBall_mono (by linarith) (by linarith))
    (Ioc_subset_Ioc (by linarith) le_rfl)

theorem negCylInner_mono {σ' σ : ℝ} (h1 : 1 / 2 ≤ σ') (h2 : σ' ≤ σ) :
    negCylInner d σ' ⊆ negCylInner d σ :=
  prod_mono (euclideanBall_mono (by linarith) (by linarith))
    (Ioc_subset_Ioc (by linarith) le_rfl)

/-- The `hUm` form of `bombieri_giusti` with `δ = 1/2`. -/
theorem posCyl_hUm : ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → MeasurableSet (posCyl d σ) :=
  fun σ _ _ => measurableSet_posCyl σ
theorem negCyl_hUm : ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → MeasurableSet (negCyl d σ) :=
  fun σ _ _ => measurableSet_negCyl σ
theorem negCylInner_hUm : ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → MeasurableSet (negCylInner d σ) :=
  fun σ _ _ => measurableSet_negCylInner σ

/-- The `hUmono` form of `bombieri_giusti` with `δ = 1/2`. -/
theorem posCyl_hUmono : ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' ≤ σ → σ ≤ 1 → posCyl d σ' ⊆ posCyl d σ :=
  fun _ _ h1 h2 _ => posCyl_mono h1 h2
theorem negCyl_hUmono : ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' ≤ σ → σ ≤ 1 → negCyl d σ' ⊆ negCyl d σ :=
  fun _ _ h1 h2 _ => negCyl_mono h1 h2
theorem negCylInner_hUmono :
    ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' ≤ σ → σ ≤ 1 → negCylInner d σ' ⊆ negCylInner d σ :=
  fun _ _ h1 h2 _ => negCylInner_mono h1 h2

theorem posCyl_subset {σ : ℝ} (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 1) :
    posCyl d σ ⊆ euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 :=
  prod_mono (euclideanBall_mono (by linarith) (by linarith))
    ((Ioo_subset_Ioc_self).trans (Ioc_subset_Ioc (by linarith)
      (by linarith)))

theorem negCyl_subset {σ : ℝ} (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 1) :
    negCyl d σ ⊆ euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 :=
  prod_mono (euclideanBall_mono (by linarith) (by linarith))
    (Ioc_subset_Ioc (by linarith) le_rfl)

theorem negCylInner_subset {σ : ℝ} (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 1) :
    negCylInner d σ ⊆ euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 :=
  prod_mono (euclideanBall_mono (by linarith) (by linarith))
    (Ioc_subset_Ioc (by linarith) le_rfl)

/-! ### Volumes -/

theorem volume_prod_ball (R : ℝ) (s : Set ℝ) :
    volume (euclideanBall (0 : Vec d) R ×ˢ s) = volume (euclideanBall (0 : Vec d) R) * volume s := by
  rw [Measure.volume_eq_prod, Measure.prod_prod]

theorem volume_posCyl {σ : ℝ} :
    volume (posCyl d σ) =
      volume (euclideanBall (0 : Vec d) (posR σ)) * ENNReal.ofReal (posHi σ - posLo σ) := by
  rw [posCyl_eq, volume_prod_ball, Real.volume_Ioo]

theorem volume_negCyl {σ : ℝ} :
    volume (negCyl d σ) =
      volume (euclideanBall (0 : Vec d) (negR σ)) * ENNReal.ofReal (0 - negLo σ) := by
  rw [negCyl_eq, volume_prod_ball, Real.volume_Ioc]

theorem volume_negCylInner {σ : ℝ} :
    volume (negCylInner d σ) =
      volume (euclideanBall (0 : Vec d) (innR σ)) * ENNReal.ofReal (0 - innLo σ) := by
  rw [negCylInner_eq, volume_prod_ball, Real.volume_Ioc]

private theorem prod_pos_ne_top {R : ℝ} (hR : 0 < R) {s : Set ℝ} (h0 : 0 < volume s)
    (ht : volume s ≠ ⊤) :
    0 < volume (euclideanBall (0 : Vec d) R ×ˢ s) ∧ volume (euclideanBall (0 : Vec d) R ×ˢ s) ≠ ⊤ := by
  rw [volume_prod_ball]
  exact ⟨ENNReal.mul_pos (volume_euclideanBall_pos _ hR).ne' h0.ne',
    ENNReal.mul_ne_top (volume_euclideanBall_ne_top _ hR.le) ht⟩

theorem volume_posCyl_pos {σ : ℝ} (h1 : 1 / 2 ≤ σ) : 0 < volume (posCyl d σ) :=
  (prod_pos_ne_top (R := posR σ) (by (try unfold posR); linarith) (s := Ioo (posLo σ) (posHi σ))
    (by rw [Real.volume_Ioo]; simp only [ENNReal.ofReal_pos]; unfold posHi posLo; linarith)
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).1

theorem volume_posCyl_ne_top {σ : ℝ} (h1 : 1 / 2 ≤ σ) : volume (posCyl d σ) ≠ ⊤ :=
  (prod_pos_ne_top (R := posR σ) (by (try unfold posR); linarith) (s := Ioo (posLo σ) (posHi σ))
    (by rw [Real.volume_Ioo]; simp only [ENNReal.ofReal_pos]; unfold posHi posLo; linarith)
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).2

theorem volume_negCyl_pos {σ : ℝ} (h1 : 1 / 2 ≤ σ) : 0 < volume (negCyl d σ) :=
  (prod_pos_ne_top (R := negR σ) (by (try unfold negR); linarith) (s := Ioc (negLo σ) 0)
    (by rw [Real.volume_Ioc]; simp only [ENNReal.ofReal_pos]; unfold negLo; linarith)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).1

theorem volume_negCyl_ne_top {σ : ℝ} (h1 : 1 / 2 ≤ σ) : volume (negCyl d σ) ≠ ⊤ :=
  (prod_pos_ne_top (R := negR σ) (by (try unfold negR); linarith) (s := Ioc (negLo σ) 0)
    (by rw [Real.volume_Ioc]; simp only [ENNReal.ofReal_pos]; unfold negLo; linarith)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).2

theorem volume_negCylInner_pos {σ : ℝ} (h1 : 1 / 2 ≤ σ) : 0 < volume (negCylInner d σ) :=
  (prod_pos_ne_top (R := innR σ) (by (try unfold innR); linarith) (s := Ioc (innLo σ) 0)
    (by rw [Real.volume_Ioc]; simp only [ENNReal.ofReal_pos]; unfold innLo; linarith)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).1

theorem volume_negCylInner_ne_top {σ : ℝ} (h1 : 1 / 2 ≤ σ) : volume (negCylInner d σ) ≠ ⊤ :=
  (prod_pos_ne_top (R := innR σ) (by (try unfold innR); linarith) (s := Ioc (innLo σ) 0)
    (by rw [Real.volume_Ioc]; simp only [ENNReal.ofReal_pos]; unfold innLo; linarith)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).2

/-! ### Normalized measures -/

/-- The normalized restriction of Lebesgue measure to `S`. -/
noncomputable def cylMeasure {α : Type*} [MeasureSpace α] (S : Set α) :
    Measure α :=
  (volume S)⁻¹ • volume.restrict S

theorem isProbabilityMeasure_cylMeasure {α : Type*} [MeasureSpace α]
    {S : Set α} (h0 : volume S ≠ 0) (ht : volume S ≠ ⊤) :
    IsProbabilityMeasure (cylMeasure S) :=
  ⟨by simp [cylMeasure, ENNReal.inv_mul_cancel h0 ht]⟩

instance isProbabilityMeasure_cylMeasure_posCyl_one :
    IsProbabilityMeasure (cylMeasure (posCyl d 1)) :=
  isProbabilityMeasure_cylMeasure (volume_posCyl_pos (by norm_num)).ne'
    (volume_posCyl_ne_top (by norm_num))

instance isProbabilityMeasure_cylMeasure_negCyl_one :
    IsProbabilityMeasure (cylMeasure (negCyl d 1)) :=
  isProbabilityMeasure_cylMeasure (volume_negCyl_pos (by norm_num)).ne'
    (volume_negCyl_ne_top (by norm_num))

instance isProbabilityMeasure_cylMeasure_negCylInner_one :
    IsProbabilityMeasure (cylMeasure (negCylInner d 1)) :=
  isProbabilityMeasure_cylMeasure (volume_negCylInner_pos (by norm_num)).ne'
    (volume_negCylInner_ne_top (by norm_num))

/-- Restriction of the normalized measure to a measurable subset. -/
theorem cylMeasure_restrict {α : Type*} [MeasureSpace α] {S T : Set α}
    (hT : MeasurableSet T) (hTS : T ⊆ S) :
    (cylMeasure S).restrict T = (volume S)⁻¹ • volume.restrict T := by
  rw [cylMeasure, Measure.restrict_smul, Measure.restrict_restrict hT, inter_eq_left.2 hTS]

end PDE.Parabolic.WeakHarnack
