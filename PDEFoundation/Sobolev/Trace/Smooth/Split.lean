module

public import PDEFoundation.Sobolev.Trace.Smooth.GagSum

/-!
# Splitting the Gagliardo integral near a compact piece

For a measurable `f` supported in a compact `K` contained in an open `D`, the Gagliardo integral
splits into the integral over `D × D` and an error controlled by `σ(univ) ∫ |f|^p`: if `x ∈ K` and
`y ∉ D` then `|x - y| ≥ δ > 0`, and `|f x - f y|^p ≤ 2^{p-1} (|f x|^p + |f y|^p)`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped ENNReal NNReal

variable {d : ℕ}

theorem measurable_gagKernel {q p : ℝ} {f : Vec d → ℝ} (hf : Measurable f) :
    Measurable fun z : Vec d × Vec d => gagKernel q p f z.1 z.2 := by
  unfold gagKernel
  refine ENNReal.measurable_ofReal.comp ?_
  refine (Measurable.pow_const (continuous_abs.measurable.comp
    ((hf.comp measurable_fst).sub (hf.comp measurable_snd))) _).div ?_
  exact Measurable.pow_const (continuous_vecEuclideanNorm.measurable.comp
    (measurable_fst.sub measurable_snd)) _

/-- A compact subset of an open set is at positive Euclidean distance from its complement. -/
theorem exists_delta_of_isCompact {K D : Set (Vec d)} (hK : IsCompact K) (hD : IsOpen D)
    (hKD : K ⊆ D) : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∉ D, δ ≤ vecEuclideanNorm (x - y) := by
  obtain ⟨δ, hδ, hth⟩ := hK.exists_thickening_subset_open hD hKD
  refine ⟨δ, hδ, fun x hx y hy => ?_⟩
  have h1 : y ∉ Metric.thickening δ K := fun h => hy (hth h)
  rw [Metric.mem_thickening_iff] at h1
  simp only [not_exists, not_and, not_lt] at h1
  have h2 := h1 x hx
  rw [dist_eq_norm] at h2
  have h3 := norm_le_vecEuclideanNorm (y - x)
  rw [vecEuclideanNorm_sub_comm] at h3
  linarith

/-- Pointwise bound of the kernel for far-apart points. -/
theorem gagKernel_le_of_far {q p δ : ℝ} (hp : 1 ≤ p) (hq : 0 ≤ q) (hδ : 0 < δ) (f : Vec d → ℝ)
    {x y : Vec d} (h : δ ≤ vecEuclideanNorm (x - y)) :
    gagKernel q p f x y ≤ ENNReal.ofReal (2 ^ (p - 1)) * ENNReal.ofReal ((δ ^ q)⁻¹) *
      (ENNReal.ofReal (|f x| ^ p) + ENNReal.ofReal (|f y| ^ p)) := by
  unfold gagKernel
  have h1 : |f x - f y| ^ p / vecEuclideanNorm (x - y) ^ q ≤ |f x - f y| ^ p * (δ ^ q)⁻¹ := by
    rw [div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact inv_anti₀ (Real.rpow_pos_of_pos hδ _) (Real.rpow_le_rpow hδ.le h hq)
  refine (ENNReal.ofReal_le_ofReal h1).trans ?_
  rw [ENNReal.ofReal_mul (by positivity)]
  calc ENNReal.ofReal (|f x - f y| ^ p) * ENNReal.ofReal ((δ ^ q)⁻¹)
      ≤ (ENNReal.ofReal (2 ^ (p - 1)) * (ENNReal.ofReal (|f x| ^ p) + ENNReal.ofReal (|f y| ^ p))) *
        ENNReal.ofReal ((δ ^ q)⁻¹) := by
        gcongr
        exact ofReal_abs_sub_rpow_le hp _ _
    _ = _ := by ring

section Iter

variable {α : Type*} [MeasurableSpace α]

/-- Additivity of the iterated integral in the inner measure. -/
theorem lintegral_iter_add_inner (μ ν ν' : Measure α) [SFinite ν] [SFinite ν'] (G : α → α → ℝ≥0∞)
    (hG : Measurable fun z : α × α => G z.1 z.2) :
    ∫⁻ x, ∫⁻ y, G x y ∂(ν + ν') ∂μ =
      ∫⁻ x, ∫⁻ y, G x y ∂ν ∂μ + ∫⁻ x, ∫⁻ y, G x y ∂ν' ∂μ := by
  simp_rw [lintegral_add_measure]
  exact lintegral_add_left (hG.lintegral_prod_right') _

/-- Splitting of the iterated integral along a measurable set. -/
theorem lintegral_iter_split (σ : Measure α) [SFinite σ] {D : Set α} (hD : MeasurableSet D)
    (G : α → α → ℝ≥0∞) (hG : Measurable fun z : α × α => G z.1 z.2) :
    ∫⁻ x, ∫⁻ y, G x y ∂σ ∂σ =
      ∫⁻ x, ∫⁻ y, G x y ∂σ.restrict D ∂σ.restrict D +
        (∫⁻ x, ∫⁻ y, G x y ∂σ.restrict Dᶜ ∂σ.restrict D +
          (∫⁻ x, ∫⁻ y, G x y ∂σ.restrict D ∂σ.restrict Dᶜ +
            ∫⁻ x, ∫⁻ y, G x y ∂σ.restrict Dᶜ ∂σ.restrict Dᶜ)) := by
  have hσ : σ = σ.restrict D + σ.restrict Dᶜ := (Measure.restrict_add_restrict_compl hD).symm
  have e1 : ∀ μ : Measure α, ∫⁻ x, ∫⁻ y, G x y ∂σ ∂μ =
      ∫⁻ x, ∫⁻ y, G x y ∂σ.restrict D ∂μ + ∫⁻ x, ∫⁻ y, G x y ∂σ.restrict Dᶜ ∂μ := fun μ => by
    conv_lhs => rw [hσ]
    exact lintegral_iter_add_inner μ _ _ G hG
  have e2 : ∀ ν : Measure α, ∫⁻ x, ∫⁻ y, G x y ∂ν ∂σ =
      ∫⁻ x, ∫⁻ y, G x y ∂ν ∂σ.restrict D + ∫⁻ x, ∫⁻ y, G x y ∂ν ∂σ.restrict Dᶜ := fun ν => by
    conv_lhs => rw [hσ]
    rw [lintegral_add_measure]
  rw [e1 σ, e2, e2]
  ring

end Iter

section Split

variable (σ : Measure (Vec d)) [IsFiniteMeasure σ]

omit [IsFiniteMeasure σ] in
theorem lintegral_iter_const_sum (c : ℝ≥0∞) {h : Vec d → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ x, ∫⁻ y, c * (h x + h y) ∂σ ∂σ = 2 * c * σ univ * ∫⁻ x, h x ∂σ := by
  have hin : ∀ x, ∫⁻ y, c * (h x + h y) ∂σ = c * (h x * σ univ + ∫⁻ y, h y ∂σ) := fun x => by
    rw [lintegral_const_mul c (f := fun y => h x + h y) (measurable_const.add hh),
      lintegral_add_left (f := fun _ => h x) measurable_const, lintegral_const]
  simp_rw [hin]
  rw [lintegral_const_mul c (f := fun x => h x * σ univ + ∫⁻ y, h y ∂σ)
    ((hh.mul_const _).add measurable_const),
    lintegral_add_right (f := fun x => h x * σ univ) measurable_const,
    lintegral_mul_const _ hh, lintegral_const]
  ring

/-- Splitting of the Gagliardo integral of a function supported in a compact subset of `D`. -/
theorem gagInt_le_split {q p : ℝ} (hp : 1 ≤ p) (hq : 0 ≤ q)
    {K D : Set (Vec d)} (hK : IsCompact K) (hD : IsOpen D) (hKD : K ⊆ D) :
    ∃ C : ℝ≥0, ∀ f : Vec d → ℝ, Measurable f → (∀ x ∉ K, f x = 0) → gagInt σ q p f ≤
      ∫⁻ x, ∫⁻ y, gagKernel q p f x y ∂σ.restrict D ∂σ.restrict D +
        (C : ℝ≥0∞) * σ univ * ∫⁻ x, ENNReal.ofReal (|f x| ^ p) ∂σ := by
  have hp0 : 0 < p := by linarith
  obtain ⟨δ, hδ, hfar⟩ := exists_delta_of_isCompact hK hD hKD
  set c : ℝ≥0∞ := ENNReal.ofReal (2 ^ (p - 1)) * ENNReal.ofReal ((δ ^ q)⁻¹) with hc
  have hcfin : c ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  refine ⟨(4 * c).toNNReal, fun f hf hfK => ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top (by simp) hcfin)]
  set h : Vec d → ℝ≥0∞ := fun x => ENNReal.ofReal (|f x| ^ p) with hh
  have hhm : Measurable h :=
    ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp hf).pow_const _)
  have hG := measurable_gagKernel (q := q) (p := p) hf
  have hz : ∀ x y, x ∉ K → y ∉ K → gagKernel q p f x y = 0 := fun x y hx hy => by
    simp [gagKernel, hfK x hx, hfK y hy, Real.zero_rpow hp0.ne']
  have hmid : ∀ x y, (x ∈ D ∧ y ∉ D) ∨ (x ∉ D ∧ y ∈ D) →
      gagKernel q p f x y ≤ c * (h x + h y) := by
    rintro x y (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · by_cases hxK : x ∈ K
      · have := gagKernel_le_of_far hp hq hδ f (hfar x hxK y hy)
        simpa only [hc, mul_assoc] using this
      · rw [hz x y hxK (fun hyK => hy (hKD hyK))]; exact zero_le
    · by_cases hyK : y ∈ K
      · have := gagKernel_le_of_far hp hq hδ f (x := y) (y := x)
          (hfar y hyK x hx)
        have hsymm : gagKernel q p f x y = gagKernel q p f y x := by
          unfold gagKernel
          rw [abs_sub_comm, vecEuclideanNorm_sub_comm]
        rw [hsymm]
        simpa only [hc, mul_assoc, add_comm] using this
      · rw [hz x y (fun hxK => hx (hKD hxK)) hyK]; exact zero_le
  have hD' := hD.measurableSet
  rw [gagInt, lintegral_iter_split σ hD' _ hG]
  have hE : ∫⁻ x, ∫⁻ y, c * (h x + h y) ∂σ ∂σ = 2 * c * σ univ * ∫⁻ x, h x ∂σ :=
    lintegral_iter_const_sum σ c hhm
  have hle : ∀ A B : Set (Vec d), MeasurableSet A → MeasurableSet B →
      (∀ x ∈ A, ∀ y ∈ B, gagKernel q p f x y ≤ c * (h x + h y)) →
      ∫⁻ x, ∫⁻ y, gagKernel q p f x y ∂σ.restrict B ∂σ.restrict A ≤
        2 * c * σ univ * ∫⁻ x, h x ∂σ := by
    intro A B hA hB hAB
    rw [← hE]
    calc _ ≤ ∫⁻ x in A, ∫⁻ y in B, c * (h x + h y) ∂σ ∂σ :=
          setLIntegral_mono' hA fun x hx => setLIntegral_mono' hB fun y hy => hAB x hx y hy
      _ ≤ _ := lintegral_mono' Measure.restrict_le_self fun x =>
          lintegral_mono' Measure.restrict_le_self le_rfl
  have h1 := hle Dᶜ D hD'.compl hD' fun x hx y hy => hmid x y (Or.inr ⟨hx, hy⟩)
  have h2 := hle D Dᶜ hD' hD'.compl fun x hx y hy => hmid x y (Or.inl ⟨hx, hy⟩)
  have h3 : ∫⁻ x, ∫⁻ y, gagKernel q p f x y ∂σ.restrict Dᶜ ∂σ.restrict Dᶜ ≤ 0 := by
    calc _ ≤ ∫⁻ x in Dᶜ, ∫⁻ y in Dᶜ, (0 : ℝ≥0∞) ∂σ ∂σ :=
          setLIntegral_mono' hD'.compl fun x hx => setLIntegral_mono' hD'.compl fun y hy =>
            (hz x y (fun hxK => hx (hKD hxK)) (fun hyK => hy (hKD hyK))).le
      _ = 0 := by simp
  have h4 : 4 * c * σ univ * ∫⁻ x, h x ∂σ =
      2 * c * σ univ * ∫⁻ x, h x ∂σ + 2 * c * σ univ * ∫⁻ x, h x ∂σ := by
    rw [show (4 : ℝ≥0∞) = 2 + 2 by norm_num, add_mul, add_mul, add_mul]
  rw [h4]
  refine add_le_add le_rfl ?_
  exact (add_le_add h2 (add_le_add h1 h3)).trans (by rw [add_zero])

end Split

end PDE.TraceLane
