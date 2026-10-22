module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import PDEFoundation.Measure.SquareLoopFubini

/-!
# A common good radius for countably many square-trace quantities

This module isolates the countable selection step used after scalar square
Fubini estimates.  Summability of the `L¹` norms of the radius functions gives
pointwise summability for almost every radius; a single radius can therefore
be chosen outside any prescribed null set.

The result is deliberately measure-theoretic.  Square-side energies and their
shell estimates enter as the explicit hypotheses `hF_int` and `hF_sum`.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set ENNReal

noncomputable section

/-- A summable family of integral norms is pointwise summable almost
everywhere.  This is the Tonelli consequence needed to select one radius for
all members of a sequence. -/
theorem ae_summable_of_summable_integral_norm
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ}
    (hF_int : ∀ n, Integrable (F n) μ)
    (hF_sum : Summable fun n => ∫ x, ‖F n x‖ ∂μ) :
    ∀ᵐ x ∂μ, Summable fun n => F n x := by
  have hlintegral : ∑' n, ∫⁻ x : α, ‖F n x‖ₑ ∂μ ≠ ∞ := by
    have hnorm (n : ℕ) :
        ∫⁻ x, ‖F n x‖ₑ ∂μ = ‖∫ x, ‖F n x‖ ∂μ‖ₑ := by
      dsimp [enorm]
      rw [lintegral_coe_eq_integral _ (hF_int n).norm]
      simp only [coe_nnreal_eq, coe_nnnorm, Real.norm_eq_abs]
      rw [abs_of_nonneg (integral_nonneg fun x => abs_nonneg (F n x))]
    rw [funext hnorm]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <|
      NNReal.summable_coe.1 hF_sum.abs
  have hnorm_summable :
      ∀ᵐ x ∂μ, Summable fun n => (‖F n x‖₊ : ℝ) := by
    rw [← lintegral_tsum fun n => (hF_int n).aestronglyMeasurable.enorm] at hlintegral
    refine (ae_lt_top'
      (AEMeasurable.tsum fun n =>
        (hF_int n).aestronglyMeasurable.enorm) hlintegral).mono ?_
    intro x hx
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact hx.ne
  exact hnorm_summable.mono fun x hx => hx.of_norm

/-- Select one radius in `(r, 2r)` outside `N` at which all members of a
countable family are summable.  The assumptions explicitly require both
integrability of every radius function and summability of their integral
norms; no side-trace measurability is hidden in the conclusion. -/
theorem exists_common_square_radius_of_summable_integral_norm
    {F : ℕ → ℝ → ℝ} {r : ℝ} {N : Set ℝ}
    (hr : 0 < r)
    (hF_int : ∀ n, IntegrableOn (F n) (Ioo r (2 * r)))
    (hF_sum : Summable fun n => ∫ ρ in Ioo r (2 * r), ‖F n ρ‖)
    (hN : volume N = 0) :
    ∃ ρ ∈ Ioo r (2 * r), ρ ∉ N ∧ Summable (fun n => F n ρ) := by
  let I : Set ℝ := Ioo r (2 * r)
  have hIpos : volume I ≠ 0 := by
    rw [show I = Ioo r (2 * r) by rfl, Real.volume_Ioo]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  have hIrestrict : volume.restrict I ≠ 0 := by
    intro hzero
    apply hIpos
    calc
      volume I = (volume.restrict I) I :=
        (Measure.restrict_apply_self volume I).symm
      _ = 0 := by simp [hzero]
  have hNrestrict : (volume.restrict I) N = 0 := by
    rw [Measure.restrict_apply' (measurableSet_Ioo : MeasurableSet I)]
    exact measure_mono_null inter_subset_left hN
  have hIcomp : (volume.restrict I) Iᶜ = 0 := by
    rw [Measure.restrict_apply' (measurableSet_Ioo : MeasurableSet I)]
    rw [compl_inter_self]
    exact measure_empty
  have hSummable : ∀ᵐ ρ ∂volume.restrict I, Summable fun n => F n ρ := by
    apply ae_summable_of_summable_integral_norm
    · intro n
      simpa only [I] using! hF_int n
    · simpa only [I] using hF_sum
  have hMem : ∀ᵐ ρ ∂volume.restrict I, ρ ∈ I := by
    rw [ae_iff]
    change (volume.restrict I) Iᶜ = 0
    exact hIcomp
  have hNotMem : ∀ᵐ ρ ∂volume.restrict I, ρ ∉ N := by
    rw [ae_iff]
    simpa only [not_not] using! hNrestrict
  have hAll : ∀ᵐ ρ ∂volume.restrict I,
      ρ ∈ I ∧ ρ ∉ N ∧ Summable (fun n => F n ρ) := by
    filter_upwards [hMem, hNotMem, hSummable] with ρ hρI hρN hρsum
    exact ⟨hρI, hρN, hρsum⟩
  let : (ae (volume.restrict I)).NeBot :=
    MeasureTheory.ae_neBot.mpr hIrestrict
  obtain ⟨ρ, hρI, hρN, hρsum⟩ := hAll.exists
  exact ⟨ρ, hρI, hρN, hρsum⟩

/-- Combine the quantitative good-radius selector with an almost-everywhere
countable summability property.  The selected radius retains the exact
`4 / r` bound and lies outside the prescribed null set. -/
theorem exists_good_square_radius_and_summable_of_summable_integral_norm
    {B : ℝ → ℝ} {F : ℕ → ℝ → ℝ}
    {r E : ℝ} {N : Set ℝ}
    (hr : 0 < r)
    (hB : IntegrableOn B (Ioo r (2 * r)))
    (hstrip : ∫ ρ in Ioo r (2 * r), B ρ ≤ 4 * E)
    (hF_int : ∀ n, IntegrableOn (F n) (Ioo r (2 * r)))
    (hF_sum : Summable fun n =>
      ∫ ρ in Ioo r (2 * r), ‖F n ρ‖)
    (hN : volume N = 0) :
    ∃ ρ ∈ Ioo r (2 * r), ρ ∉ N ∧
      B ρ ≤ (4 / r) * E ∧ Summable (fun n => F n ρ) := by
  let I : Set ℝ := Ioo r (2 * r)
  have hSummable :
      ∀ᵐ ρ ∂volume.restrict I,
        Summable fun n => F n ρ := by
    apply ae_summable_of_summable_integral_norm
    · intro n
      simpa only [I] using! hF_int n
    · simpa only [I] using hF_sum
  let Nsum : Set ℝ :=
    I ∩ {ρ | ¬Summable fun n => F n ρ}
  have hNsum : volume Nsum = 0 := by
    have hbad :
        (volume.restrict I)
            {ρ | ¬Summable fun n => F n ρ} = 0 := by
      rw [← ae_iff]
      simpa only [not_not] using hSummable
    rw [Measure.restrict_apply'
      (measurableSet_Ioo : MeasurableSet I)] at hbad
    simpa only [Nsum, inter_comm] using hbad
  have hNullUnion : volume (N ∪ Nsum) = 0 :=
    measure_union_null hN hNsum
  obtain ⟨ρ, hρI, hρNotUnion, hρB⟩ :=
    exists_good_square_radius_of_strip_bound
      hr hB hstrip hNullUnion
  have hρN : ρ ∉ N := fun hmem =>
    hρNotUnion (Or.inl hmem)
  have hρSummable : Summable fun n => F n ρ := by
    by_contra hnot
    exact hρNotUnion (Or.inr ⟨hρI, hnot⟩)
  exact ⟨ρ, hρI, hρN, hρB, hρSummable⟩

/-- A common radius for a weighted sequence of scalar square-side energies.
The exact factor four from the four shell strips is retained in the
summability comparison. -/
theorem exists_common_square_radius_of_summable_weighted_scalar_energy
    {f : ℕ → Vec 2 → ℝ} {w : ℕ → ℝ}
    {x₀ : Vec 2} {r : ℝ} {N : Set ℝ}
    (hr : 0 < r)
    (hf : ∀ n,
      MemL2On (centeredAxisCube x₀ (2 * r)) (f n))
    (hw : ∀ n, 0 ≤ w n)
    (hsum : Summable fun n =>
      w n * squareShellScalarEnergy (f n) x₀ r)
    (hN : volume N = 0) :
    ∃ ρ ∈ Ioo r (2 * r), ρ ∉ N ∧
      Summable (fun n =>
        w n * enlargedSquareSideScalarEnergy (f n) x₀ r ρ) := by
  let F : ℕ → ℝ → ℝ :=
    fun n ρ =>
      w n * enlargedSquareSideScalarEnergy (f n) x₀ r ρ
  have hFIntegrable :
      ∀ n, IntegrableOn (F n) (Ioo r (2 * r)) := by
    intro n
    simpa only [F] using!
      (integrableOn_enlargedSquareSideScalarEnergy_of_memL2On
        (hf n)).const_mul (w n)
  have hIntegralBound :
      ∀ n,
        (∫ ρ in Ioo r (2 * r), ‖F n ρ‖) ≤
          4 * (w n * squareShellScalarEnergy (f n) x₀ r) := by
    intro n
    have hpointwise :
        (fun ρ => ‖F n ρ‖) =
          fun ρ => w n *
            enlargedSquareSideScalarEnergy (f n) x₀ r ρ := by
      funext ρ
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact mul_nonneg (hw n)
        (enlargedSquareSideScalarEnergy_nonneg
          (f n) x₀ r ρ)
    rw [hpointwise, MeasureTheory.integral_const_mul]
    calc
      w n *
          ∫ ρ in Ioo r (2 * r),
            enlargedSquareSideScalarEnergy (f n) x₀ r ρ ≤
          w n * (4 * squareShellScalarEnergy (f n) x₀ r) :=
        mul_le_mul_of_nonneg_left
          (integral_enlargedSquareSideScalarEnergy_le_four_mul_squareShellScalarEnergy
            (hf n))
          (hw n)
      _ = 4 * (w n * squareShellScalarEnergy (f n) x₀ r) := by
        ring
  have hIntegralSummable :
      Summable fun n =>
        ∫ ρ in Ioo r (2 * r), ‖F n ρ‖ := by
    refine Summable.of_nonneg_of_le
      (fun n => integral_nonneg fun ρ => norm_nonneg (F n ρ))
      hIntegralBound ?_
    exact hsum.mul_left 4
  simpa only [F] using
    exists_common_square_radius_of_summable_integral_norm
      hr hFIntegrable hIntegralSummable hN

end

end PDE
