module

public import EllipticRegularity.Parabolic.Energy.Pointwise

/-!
# Bounds and measurability for the Fubini step
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Energy

open MeasureTheory Set Filter Topology Metric PDE

variable {d : ℕ}

namespace Data

variable (D : Data d)

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

theorem exists_v_bound {a : ℝ} (ha : 0 < a) (haδ : a ≤ D.δ0) :
    ∃ B : ℝ, ∀ x ∈ D.K, ∀ τ ∈ Icc D.s D.t, |D.v a (x, τ)| ≤ B := by
  obtain ⟨Ck, hCk⟩ := kern_bound (d := d) ha
  obtain ⟨C1, hC1, hDh⟩ := D.exists_Dh_le ha
  refine ⟨Ck * (∫ y in D.K1, |D.u (y, D.s)|) + C1 * (∫ σ in Ioc D.s D.t, D.gG σ), ?_⟩
  intro x hx τ hτ
  have hs : D.s ∈ Icc D.s D.t := ⟨le_rfl, D.hst.le⟩
  have hu_int : Integrable (fun y => D.u (y, D.s)) (volume.restrict D.K1) :=
    (D.hus D.s hs).integrable (by norm_num)
  have h1 : |D.v a (x, D.s)| ≤ Ck * ∫ y in D.K1, |D.u (y, D.s)| := by
    rw [D.v_eq, ← Real.norm_eq_abs, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hu_int.abs.const_mul Ck) (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hCk _) (abs_nonneg _)
  have h2 : |∫ σ in D.s..τ, D.Dh a x σ| ≤ C1 * ∫ σ in Ioc D.s D.t, D.gG σ := by
    rw [intervalIntegral.integral_of_le hτ.1, ← Real.norm_eq_abs]
    have hsub : Ioc D.s τ ⊆ Ioc D.s D.t := Ioc_subset_Ioc le_rfl hτ.2
    have hint : IntegrableOn D.gG (Ioc D.s τ) := D.gG_integrableOn.mono_set hsub
    calc ‖∫ σ in Ioc D.s τ, D.Dh a x σ‖ ≤ ∫ σ in Ioc D.s τ, C1 * D.gG σ :=
          norm_integral_le_of_norm_le (hint.const_mul C1)
            (by
              have := ae_restrict_of_ae_restrict_of_subset hsub hDh
              filter_upwards [this] with σ hσ
              rw [Real.norm_eq_abs]; exact hσ x)
      _ = C1 * ∫ σ in Ioc D.s τ, D.gG σ := integral_const_mul _ _
      _ ≤ C1 * ∫ σ in Ioc D.s D.t, D.gG σ := by
          refine mul_le_mul_of_nonneg_left ?_ hC1
          exact setIntegral_mono_set D.gG_integrableOn (Filter.Eventually.of_forall D.gG_nonneg)
            (Filter.Eventually.of_forall hsub)
  rw [D.v_rep ha haδ hx hτ]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

end Data

end PDE.Parabolic.Energy
