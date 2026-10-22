/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.Energy.Limit

/-! # Abstract data for the supersolution renormalization inequality -/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Chain.Super

open MeasureTheory Set Filter Topology Metric PDE PDE.Parabolic.Energy

variable {d : ℕ}

/-- Abstract data for the supersolution renormalization inequality. It is the analogue of
`PDE.Parabolic.Energy.Data`, in which the mollified weak time-slice identity is replaced by the
mollified time-slice *inequality* `hslice`, and which records the nonnegativity and time-support of
the cutoff and the time continuity of the mollified slices. -/
structure SuperData (d : ℕ) where
  K : Set (Vec d)
  hK : IsCompact K
  δ0 : ℝ
  hδ0 : 0 < δ0
  hδ1 : δ0 ≤ 1
  s : ℝ
  t : ℝ
  hst : s < t
  u : Vec d × ℝ → ℝ
  Du : Vec d × ℝ → Vec d
  G : Vec d × ℝ → Vec d
  φ : Vec d × ℝ → ℝ
  hφ : ContDiff ℝ 1 φ
  hφK : ∀ x τ, τ ∈ Icc s t → x ∈ cthickening (2 * δ0) K → x ∉ K → φ (x, τ) = 0
  hDum : ∀ i, Measurable fun z => Du z i
  hGm : ∀ i, Measurable fun z => G z i
  hu2 : MemLp u 2 (volume.restrict (cthickening δ0 K ×ˢ Ioc s t))
  hDu2 : ∀ i, MemLp (fun z => Du z i) 2 (volume.restrict (cthickening δ0 K ×ˢ Ioc s t))
  hG2 : ∀ i, MemLp (fun z => G z i) 2 (volume.restrict (cthickening δ0 K ×ˢ Ioc s t))
  hus : ∀ τ ∈ Icc s t, MemLp (fun y => u (y, τ)) 2 (volume.restrict (cthickening δ0 K))
  hwg : ∀ᵐ τ ∂(volume.restrict (Ioc s t)), ∀ a : ℝ, 0 < a → a ≤ δ0 → ∀ x ∈ K, ∀ i,
    ∫ y in cthickening δ0 K, fderiv ℝ (kern a) (x - y) (basisVec i) * u (y, τ) =
      ∫ y in cthickening δ0 K, kern a (x - y) * Du (y, τ) i
  hφnn : ∀ z, 0 ≤ φ z
  hφtime : ∀ z : Vec d × ℝ, z.2 ∉ Ioo s t → φ z = 0
  hvcont : ∀ a : ℝ, 0 < a → a ≤ δ0 → ∀ x ∈ K,
    ContinuousOn (fun τ => ∫ y in cthickening δ0 K, kern a (x - y) * u (y, τ)) (Icc s t)
  hslice : ∀ a : ℝ, 0 < a → a ≤ δ0 → ∀ x ∈ K, ∀ τ1 τ2 : ℝ, s ≤ τ1 → τ1 ≤ τ2 → τ2 ≤ t →
    (∫ z in cthickening δ0 K ×ˢ Ioc τ1 τ2,
        ∑ i, G z i * fderiv ℝ (kern a) (x - z.1) (basisVec i)) ≤
      (∫ y in cthickening δ0 K, kern a (x - y) * u (y, τ2)) -
        (∫ y in cthickening δ0 K, kern a (x - y) * u (y, τ1))

namespace SuperData

variable (D : SuperData d)

/-- The collar `K1 = cthickening δ0 K` (compact). -/
abbrev K1 : Set (Vec d) := cthickening D.δ0 D.K

theorem K1_compact : IsCompact D.K1 := D.hK.cthickening

theorem K1_measurable : MeasurableSet D.K1 := D.K1_compact.measurableSet

theorem K_subset_K1 : D.K ⊆ D.K1 := self_subset_cthickening _

theorem K_measurable : MeasurableSet D.K := D.hK.measurableSet

/-- The mollified `u`. -/
noncomputable def v (a : ℝ) : Vec d × ℝ → ℝ := mollT a D.K1 D.u

/-- The mollified time derivative `D̂_a(x,σ) = ∫_{K1} G(y,σ)·∇k_a(x-y) dy`. -/
noncomputable def Dh (a : ℝ) (x : Vec d) (σ : ℝ) : ℝ :=
  ∫ y in D.K1, ∑ i, D.G (y, σ) i * fderiv ℝ (kern a) (x - y) (basisVec i)

theorem measure_slab_lt_top (p q : ℝ) : volume (D.K1 ×ˢ Ioc p q) < ⊤ := by
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_lt_top D.K1_compact.measure_lt_top (by simp)

instance (p q : ℝ) : IsFiniteMeasure (volume.restrict (D.K1 ×ˢ Ioc p q)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact D.measure_slab_lt_top p q⟩

theorem integrableOn_G (i : Fin d) :
    IntegrableOn (fun z => D.G z i) (D.K1 ×ˢ Ioc D.s D.t) :=
  (D.hG2 i).integrable (by norm_num)


/-- The integrand of the time-slice identity. -/
noncomputable def Phi (a : ℝ) (x : Vec d) (z : Vec d × ℝ) : ℝ :=
  ∑ i, D.G z i * fderiv ℝ (kern a) (x - z.1) (basisVec i)

theorem Phi_integrableOn {a : ℝ} (ha : 0 < a) (x : Vec d) {p q : ℝ} (hp : D.s ≤ p) (hq : q ≤ D.t) :
    IntegrableOn (D.Phi a x) (D.K1 ×ˢ Ioc p q) := by
  have hsub : D.K1 ×ˢ Ioc p q ⊆ D.K1 ×ˢ Ioc D.s D.t :=
    prod_mono subset_rfl (Ioc_subset_Ioc hp hq)
  unfold Phi
  refine integrable_finsetSum _ fun i _ => ?_
  obtain ⟨C, hC⟩ := kern_fderiv_bound (d := d) ha (basisVec i)
  refine Integrable.mul_bdd ((D.integrableOn_G i).mono_set hsub) ?_ (c := C) ?_
  · exact ((kern_fderiv_continuous a (basisVec i)).comp
      (continuous_const.sub continuous_fst)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z => by simpa using hC (x - z.1)

theorem integral_Phi_eq {a : ℝ} (ha : 0 < a) (x : Vec d) {p q : ℝ} (hp : D.s ≤ p)
    (hq : q ≤ D.t) :
    ∫ z in D.K1 ×ˢ Ioc p q, D.Phi a x z = ∫ σ in Ioc p q, D.Dh a x σ := by
  have hint := D.Phi_integrableOn ha x hp hq
  unfold IntegrableOn at hint
  rw [volume_restrict_prod] at hint ⊢
  rw [integral_prod_symm _ hint]
  rfl

theorem Dh_integrableOn {a : ℝ} (ha : 0 < a) (x : Vec d) {p q : ℝ} (hp : D.s ≤ p) (hq : q ≤ D.t) :
    IntegrableOn (D.Dh a x) (Ioc p q) := by
  have hint := D.Phi_integrableOn ha x hp hq
  unfold IntegrableOn at hint ⊢
  rw [volume_restrict_prod] at hint
  exact hint.integral_prod_right

theorem v_eq (a : ℝ) (x : Vec d) (τ : ℝ) :
    D.v a (x, τ) = ∫ y in D.K1, kern a (x - y) * D.u (y, τ) := by
  unfold v
  rw [mollT_eq, ← integral_indicator D.K1_measurable]
  congr 1; funext y
  by_cases hy : y ∈ D.K1 <;> simp [hy]

theorem Dh_intervalIntegrable {a : ℝ} (ha : 0 < a) (x : Vec d) :
    IntervalIntegrable (D.Dh a x) volume D.s D.t :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le D.hst.le).2 (D.Dh_integrableOn ha x le_rfl le_rfl)

theorem contDiff_timeSlice (x : Vec d) : ContDiff ℝ 1 fun τ => D.φ (x, τ) :=
  D.hφ.comp (contDiff_const.prodMk contDiff_id)

theorem deriv_timeSlice (x : Vec d) (τ : ℝ) :
    deriv (fun τ => D.φ (x, τ)) τ = parTimeDeriv D.φ (x, τ) := by
  have h1 : HasFDerivAt D.φ (fderiv ℝ D.φ (x, τ)) (x, τ) :=
    ((D.hφ.differentiable (by simp)) (x, τ)).hasFDerivAt
  have h2 : HasDerivAt (fun τ : ℝ => ((x, τ) : Vec d × ℝ)) ((0 : Vec d), (1 : ℝ)) τ :=
    (hasDerivAt_const τ x).prodMk (hasDerivAt_id τ)
  exact (h1.comp_hasDerivAt τ h2).deriv


instance : IsFiniteMeasure (volume.restrict D.K1) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact D.K1_compact.measure_lt_top⟩

/-- The slice `σ ↦ ∫_{K1} ∑ |G_i(y,σ)| dy`. -/
noncomputable def gG (σ : ℝ) : ℝ := ∫ y in D.K1, ∑ i, |D.G (y, σ) i|

theorem integrableOn_sumAbsG :
    Integrable (fun z => ∑ i, |D.G z i|) ((volume.restrict D.K1).prod (volume.restrict (Ioc D.s D.t))) := by
  rw [← volume_restrict_prod]
  exact integrable_finsetSum _ fun i _ => (D.integrableOn_G i).abs

theorem gG_integrableOn : IntegrableOn D.gG (Ioc D.s D.t) := by
  have := D.integrableOn_sumAbsG.integral_prod_right
  exact this

theorem exists_Dh_le {a : ℝ} (ha : 0 < a) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ᵐ σ ∂(volume.restrict (Ioc D.s D.t)), ∀ x, |D.Dh a x σ| ≤ C1 * D.gG σ := by
  choose C hC using fun i : Fin d => kern_fderiv_bound (d := d) ha (basisVec i)
  refine ⟨∑ i, |C i|, Finset.sum_nonneg fun i _ => abs_nonneg _, ?_⟩
  filter_upwards [D.integrableOn_sumAbsG.prod_left_ae] with σ hσ x
  set C1 := ∑ i, |C i| with hC1
  have hle : ∀ i, |C i| ≤ C1 := fun i =>
    Finset.single_le_sum (f := fun i => |C i|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  unfold Dh gG
  have h1 : ‖∫ y in D.K1, ∑ i, D.G (y, σ) i * fderiv ℝ (kern a) (x - y) (basisVec i)‖ ≤
      ∫ y in D.K1, C1 * ∑ i, |D.G (y, σ) i| := by
    refine norm_integral_le_of_norm_le (hσ.const_mul C1) (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right ((hC i (x - y)).trans ((le_abs_self _).trans (hle i))) (abs_nonneg _)
  rw [Real.norm_eq_abs] at h1
  rw [integral_const_mul] at h1
  exact h1

theorem gG_nonneg (σ : ℝ) : 0 ≤ D.gG σ :=
  setIntegral_nonneg D.K1_measurable fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _


/-- The mollified slice inequality in interval-integral form. -/
theorem v_ge {a : ℝ} (ha : 0 < a) (haδ : a ≤ D.δ0) {x : Vec d} (hx : x ∈ D.K) {τ1 τ2 : ℝ}
    (h1 : D.s ≤ τ1) (h12 : τ1 ≤ τ2) (h2 : τ2 ≤ D.t) :
    ∫ σ in τ1..τ2, D.Dh a x σ ≤ D.v a (x, τ2) - D.v a (x, τ1) := by
  have h := D.hslice a ha haδ x hx τ1 τ2 h1 h12 h2
  rw [intervalIntegral.integral_of_le h12, ← D.integral_Phi_eq ha x h1 h2, D.v_eq, D.v_eq]
  exact h

theorem v_continuousOn {a : ℝ} (ha : 0 < a) (haδ : a ≤ D.δ0) {x : Vec d} (hx : x ∈ D.K) :
    ContinuousOn (fun τ => D.v a (x, τ)) (Icc D.s D.t) :=
  (D.hvcont a ha haδ x hx).congr fun τ _ => D.v_eq a x τ

theorem abs_integral_Dh_le {a : ℝ} {C1 : ℝ} (hC1 : 0 ≤ C1)
    (hDh : ∀ᵐ σ ∂(volume.restrict (Ioc D.s D.t)), ∀ x, |D.Dh a x σ| ≤ C1 * D.gG σ)
    (x : Vec d) {p q : ℝ} (hp : D.s ≤ p) (hpq : p ≤ q) (hq : q ≤ D.t) :
    |∫ σ in p..q, D.Dh a x σ| ≤ C1 * ∫ σ in Ioc D.s D.t, D.gG σ := by
  rw [intervalIntegral.integral_of_le hpq, ← Real.norm_eq_abs]
  have hsub : Ioc p q ⊆ Ioc D.s D.t := Ioc_subset_Ioc hp hq
  have hint : IntegrableOn D.gG (Ioc p q) := D.gG_integrableOn.mono_set hsub
  calc ‖∫ σ in Ioc p q, D.Dh a x σ‖ ≤ ∫ σ in Ioc p q, C1 * D.gG σ :=
        norm_integral_le_of_norm_le (hint.const_mul C1)
          (by
            have := ae_restrict_of_ae_restrict_of_subset hsub hDh
            filter_upwards [this] with σ hσ
            rw [Real.norm_eq_abs]; exact hσ x)
    _ = C1 * ∫ σ in Ioc p q, D.gG σ := integral_const_mul _ _
    _ ≤ C1 * ∫ σ in Ioc D.s D.t, D.gG σ := by
        refine mul_le_mul_of_nonneg_left ?_ hC1
        exact setIntegral_mono_set D.gG_integrableOn (Filter.Eventually.of_forall D.gG_nonneg)
          (Filter.Eventually.of_forall hsub)

theorem abs_v_le {a : ℝ} {Ck : ℝ} (hCk : ∀ y : Vec d, |kern a y| ≤ Ck) {x : Vec d}
    (τ : ℝ) (hτ : τ ∈ Icc D.s D.t) :
    |D.v a (x, τ)| ≤ Ck * ∫ y in D.K1, |D.u (y, τ)| := by
  have hu_int : Integrable (fun y => D.u (y, τ)) (volume.restrict D.K1) :=
    (D.hus τ hτ).integrable (by norm_num)
  rw [D.v_eq, ← Real.norm_eq_abs, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hu_int.abs.const_mul Ck)
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hCk _) (abs_nonneg _)

theorem exists_v_bound {a : ℝ} (ha : 0 < a) (haδ : a ≤ D.δ0) :
    ∃ B : ℝ, ∀ x ∈ D.K, ∀ τ ∈ Icc D.s D.t, |D.v a (x, τ)| ≤ B := by
  obtain ⟨Ck, hCk⟩ := kern_bound (d := d) ha
  obtain ⟨C1, hC1, hDh⟩ := D.exists_Dh_le ha
  refine ⟨Ck * (∫ y in D.K1, |D.u (y, D.s)|) + Ck * (∫ y in D.K1, |D.u (y, D.t)|) +
    C1 * (∫ σ in Ioc D.s D.t, D.gG σ), ?_⟩
  intro x hx τ hτ
  have hs : D.s ∈ Icc D.s D.t := ⟨le_rfl, D.hst.le⟩
  have ht : D.t ∈ Icc D.s D.t := ⟨D.hst.le, le_rfl⟩
  have h1s := D.abs_v_le (x := x) hCk D.s hs
  have h1t := D.abs_v_le (x := x) hCk D.t ht
  have h2 := D.abs_integral_Dh_le hC1 hDh x hs.1 hτ.1 hτ.2
  have h3 := D.abs_integral_Dh_le hC1 hDh x hτ.1 hτ.2 le_rfl
  have hlo := D.v_ge ha haδ hx hs.1 hτ.1 hτ.2
  have hhi := D.v_ge ha haδ hx hτ.1 hτ.2 le_rfl
  have hkl : 0 ≤ Ck * ∫ y in D.K1, |D.u (y, D.s)| :=
    (abs_nonneg _).trans h1s
  have hkt : 0 ≤ Ck * ∫ y in D.K1, |D.u (y, D.t)| :=
    (abs_nonneg _).trans h1t
  rw [abs_le] at h1s h1t h2 h3 ⊢
  constructor <;> linarith [h1s.1, h1s.2, h1t.1, h1t.2, h2.1, h2.2, h3.1, h3.2]

end SuperData

end PDE.Parabolic.Chain.Super
