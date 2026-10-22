module

public import EllipticRegularity.Parabolic.WeakHarnack.MeasuresLogTailBombieri
public import EllipticRegularity.Parabolic.WeakHarnack.MeasuresConvert
public import EllipticRegularity.Parabolic.ParabolicDef

/-!
# Measurable representatives for the weak Harnack assembly

The step estimates and the logarithmic estimate are stated for the given `u.toFun`, which is only
a.e. measurable on `D = B₁ × (-1,0]`.  The Bombieri-Giusti lemma and the measure-theoretic glue
need an everywhere measurable function; here we build a nonnegative measurable representative
`g` with `f = g` a.e. on `D`, and transfer
* `eLpNorm`s over normalized cylinder measures (`ae_cylMeasure_restrict`),
* the hypotheses of `posNegCyl_log_tail` (`transfer_logHyps`; null set `N` enlarged by the null set
  of times at which the slices differ).
-/

@[expose] public section

open MeasureTheory Set intervalIntegral
open scoped ENNReal

namespace PDE.Parabolic.WeakHarnack

variable {d : ℕ}

/-- The domain `B₁ × (-1,0]`. -/
def weakDomain (d : ℕ) : Set (Vec d × ℝ) := euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0

theorem measurableSet_weakDomain : MeasurableSet (weakDomain d) :=
  (measurableSet_euclideanBall _ _).prod measurableSet_Ioc

/-- A nonnegative everywhere measurable representative of an a.e. measurable, a.e. nonnegative
function. -/
theorem exists_measurable_nonneg_rep {μ : Measure (Vec d × ℝ)} {f : Vec d × ℝ → ℝ}
    (hf : AEStronglyMeasurable f μ) (h0 : ∀ᵐ z ∂μ, 0 ≤ f z) :
    ∃ g : Vec d × ℝ → ℝ, Measurable g ∧ (∀ z, 0 ≤ g z) ∧ f =ᵐ[μ] g := by
  refine ⟨fun z => max (hf.mk f z) 0, hf.stronglyMeasurable_mk.measurable.max measurable_const,
    fun z => le_max_right _ _, ?_⟩
  filter_upwards [hf.ae_eq_mk, h0] with z hz hz0
  rw [← hz]
  exact (max_eq_left hz0).symm

/-- Absolute continuity of the normalized cylinder measure with respect to `vol|_D`. -/
theorem ae_cylMeasure_restrict {S T : Set (Vec d × ℝ)} (hS : S ⊆ weakDomain d)
    {f g : Vec d × ℝ → ℝ} (h : f =ᵐ[volume.restrict (weakDomain d)] g) :
    f =ᵐ[(cylMeasure S).restrict T] g := by
  have hle : (cylMeasure S).restrict T ≤ (volume S)⁻¹ • volume.restrict (weakDomain d) := by
    rw [cylMeasure, Measure.restrict_smul]
    have h2 : (volume.restrict S).restrict T ≤ volume.restrict (weakDomain d) :=
      (Measure.restrict_le_self).trans (Measure.restrict_mono hS le_rfl)
    intro s
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_right (h2 s) _
  exact (Measure.absolutelyContinuous_of_le_smul hle).ae_eq h

/-- Slices of an a.e.-equality on `D`: for a.e. time in `(-1,0]` the spatial slices agree a.e. -/
theorem ae_slice_eq {f g : Vec d × ℝ → ℝ} (h : f =ᵐ[volume.restrict (weakDomain d)] g) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioc (-1 : ℝ) 0 →
      (fun x => f (x, t)) =ᵐ[(volume : Measure (Vec d)).restrict (euclideanBall (0 : Vec d) 1)]
        (fun x => g (x, t)) := by
  have hE : volume ({z | f z ≠ g z} ∩ weakDomain d) = 0 := by
    have := (ae_iff.1 h)
    rwa [Measure.restrict_apply' measurableSet_weakDomain] at this
  obtain ⟨E, hEsub, hEm, hE0⟩ := exists_measurable_superset_of_null hE
  have hswap : (volume.prod volume : Measure (ℝ × Vec d)) (Prod.swap ⁻¹' E) = 0 := by
    have := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure (Vec d)))).measure_preimage hEm.nullMeasurableSet
    rw [this]
    rwa [Measure.volume_eq_prod] at hE0
  have hae := Measure.measure_ae_null_of_prod_null hswap
  filter_upwards [hae] with t ht htI
  have ht0 : (volume : Measure (Vec d)) {x | (x, t) ∈ E} = 0 := ht
  rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_euclideanBall _ _)]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 ht0] with x hx hxB
  by_contra hne
  exact hx (hEsub ⟨hne, ⟨hxB, htI⟩⟩)

theorem cutoffMeasure_ac_ball (d : ℕ) :
    cutoffMeasure d ≪ volume.restrict (euclideanBall (0 : Vec d) 1) :=
  (withDensity_absolutelyContinuous _ _).smul_left _

/-- Transfer of the hypotheses of `posNegCyl_log_tail` between a.e.-equal functions on `D`
(the null set `N` is enlarged). -/
theorem transfer_logHyps {G G' : Vec d × ℝ → ℝ} (hGG : G =ᵐ[volume.restrict (weakDomain d)] G')
    {c K : ℝ} {N : Set ℝ} (hN : volume N = 0)
    (hL2 : ∀ t ∈ Icc (-7 / 8 : ℝ) 0, t ∉ N → MemLp (fun x => G (x, t)) 2 (cutoffMeasure d))
    (hV : IntervalIntegrable
      (fun t => ∫ x, (G (x, t) - ∫ y, G (y, t) ∂(cutoffMeasure d)) ^ 2 ∂(cutoffMeasure d))
      volume (-7 / 8) 0)
    (hdiff : ∀ t₁ ∈ Icc (-7 / 8 : ℝ) 0, ∀ t₂ ∈ Icc (-7 / 8 : ℝ) 0, t₁ ∉ N → t₂ ∉ N → t₁ < t₂ →
      ∫ τ in t₁..t₂, (c * ∫ x, (G (x, τ) - ∫ y, G (y, τ) ∂(cutoffMeasure d)) ^ 2
          ∂(cutoffMeasure d) - K) ≤
        (∫ x, G (x, t₂) ∂(cutoffMeasure d)) - ∫ x, G (x, t₁) ∂(cutoffMeasure d)) :
    ∃ N' : Set ℝ, volume N' = 0 ∧
      (∀ t ∈ Icc (-7 / 8 : ℝ) 0, t ∉ N' → MemLp (fun x => G' (x, t)) 2 (cutoffMeasure d)) ∧
      IntervalIntegrable
        (fun t => ∫ x, (G' (x, t) - ∫ y, G' (y, t) ∂(cutoffMeasure d)) ^ 2 ∂(cutoffMeasure d))
        volume (-7 / 8) 0 ∧
      (∀ t₁ ∈ Icc (-7 / 8 : ℝ) 0, ∀ t₂ ∈ Icc (-7 / 8 : ℝ) 0, t₁ ∉ N' → t₂ ∉ N' → t₁ < t₂ →
        ∫ τ in t₁..t₂, (c * ∫ x, (G' (x, τ) - ∫ y, G' (y, τ) ∂(cutoffMeasure d)) ^ 2
            ∂(cutoffMeasure d) - K) ≤
          (∫ x, G' (x, t₂) ∂(cutoffMeasure d)) - ∫ x, G' (x, t₁) ∂(cutoffMeasure d)) := by
  set Bad : Set ℝ := {t | ¬ (t ∈ Ioc (-1 : ℝ) 0 →
      (fun x => G (x, t)) =ᵐ[(volume : Measure (Vec d)).restrict (euclideanBall (0 : Vec d) 1)]
        (fun x => G' (x, t)))} with hBad
  have hBad0 : volume Bad = 0 := ae_iff.1 (ae_slice_eq hGG)
  have hN'0 : volume (N ∪ Bad) = 0 := measure_union_null hN hBad0
  -- slice equality off `N ∪ Bad`
  have hslice : ∀ t ∈ Icc (-7 / 8 : ℝ) 0, t ∉ N ∪ Bad →
      (fun x => G (x, t)) =ᵐ[cutoffMeasure d] (fun x => G' (x, t)) := by
    intro t ht htN
    have h1 : t ∈ Ioc (-1 : ℝ) 0 := ⟨by linarith [ht.1], ht.2⟩
    have h2 : t ∉ Bad := fun hb => htN (Or.inr hb)
    simp only [hBad, mem_ofPred_eq, not_not] at h2
    exact (cutoffMeasure_ac_ball d).ae_eq (h2 h1)
  have hint : ∀ t ∈ Icc (-7 / 8 : ℝ) 0, t ∉ N ∪ Bad →
      ∫ x, G' (x, t) ∂(cutoffMeasure d) = ∫ x, G (x, t) ∂(cutoffMeasure d) := fun t ht htN =>
    (integral_congr_ae (hslice t ht htN)).symm
  have hvar : ∀ t ∈ Icc (-7 / 8 : ℝ) 0, t ∉ N ∪ Bad →
      ∫ x, (G' (x, t) - ∫ y, G' (y, t) ∂(cutoffMeasure d)) ^ 2 ∂(cutoffMeasure d) =
        ∫ x, (G (x, t) - ∫ y, G (y, t) ∂(cutoffMeasure d)) ^ 2 ∂(cutoffMeasure d) := by
    intro t ht htN
    rw [hint t ht htN]
    refine integral_congr_ae ?_
    filter_upwards [hslice t ht htN] with x hx
    rw [hx]
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ N ∪ Bad := measure_eq_zero_iff_ae_notMem.1 hN'0
  refine ⟨N ∪ Bad, hN'0, ?_, ?_, ?_⟩
  · intro t ht htN
    exact (hL2 t ht (fun h => htN (Or.inl h))).ae_eq (hslice t ht htN)
  · rw [intervalIntegrable_iff] at hV ⊢
    refine hV.congr ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hae] with t htN htI
    have ht : t ∈ Icc (-7 / 8 : ℝ) 0 := by
      have : uIoc (-7 / 8 : ℝ) 0 ⊆ Icc (-7 / 8 : ℝ) 0 := by
        rw [uIoc_of_le (by norm_num)]; exact Ioc_subset_Icc_self
      exact this htI
    exact (hvar t ht htN).symm
  · intro t₁ h₁ t₂ h₂ ht₁ ht₂ h12
    have hN1 : t₁ ∉ N := fun h => ht₁ (Or.inl h)
    have hN2 : t₂ ∉ N := fun h => ht₂ (Or.inl h)
    have key := hdiff t₁ h₁ t₂ h₂ hN1 hN2 h12
    rw [hint t₂ h₂ ht₂, hint t₁ h₁ ht₁]
    refine le_of_eq_of_le (intervalIntegral.integral_congr_ae ?_) key
    filter_upwards [hae] with τ hτ hτI
    have hτ' : τ ∈ Icc (-7 / 8 : ℝ) 0 := by
      have : uIoc t₁ t₂ ⊆ Icc (-7 / 8 : ℝ) 0 := by
        rw [uIoc_of_le h12.le]
        exact (Ioc_subset_Icc_self).trans (Icc_subset_Icc h₁.1 h₂.2)
      exact this hτI
    rw [hvar τ hτ' hτ]

end PDE.Parabolic.WeakHarnack
