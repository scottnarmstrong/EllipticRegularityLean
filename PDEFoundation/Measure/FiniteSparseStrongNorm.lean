module

public import PDEFoundation.Measure.FiniteSparseBilinearNorm
public import PDEFoundation.Measure.FiniteSparseSum
public import PDEFoundation.Measure.NonnegativeDualPower
public import PDEFoundation.Analysis.ENNRealPowerCancellation

@[expose] public section

namespace PDE
open BoxIntegral MeasureTheory
open scoped _root_.ENNReal

private theorem lintegral_nonnegative_rpow_eq_eLpNorm_rpow
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hfm : AEStronglyMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, (ENNReal.ofReal (f x)) ^ p ∂μ) =
      eLpNorm f (ENNReal.ofReal p) μ ^ p := by
  have hpne : ENNReal.ofReal p ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne ENNReal.ofReal_ne_top hfm,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul,
    show (1 / p) * p = 1 by field_simp, ENNReal.rpow_one]
  congr 1
  funext x
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hf0 x)]

/-- Every finite sparse sum with the actual three-quarter remainder geometry
has the exact norm coefficient `4p/3`. Its integrability is derived from its
literal finite support before the norming test and cancellation are used. -/
theorem eLpNorm_finiteSparseSum_le
    {d : ℕ} (I : Box (Fin d)) (S : Finset (List (Set (Fin d))))
    (b : Vec d → ℝ) (a : List (Set (Fin d)) → ℝ)
    (E : List (Set (Fin d)) → Set (Vec d))
    (ha : ∀ q ∈ S, 0 ≤ a q)
    (hE : ∀ q ∈ S, MeasurableSet (E q))
    (hsub : ∀ q ∈ S, E q ⊆ (dyadicDescendant I q : Set (Vec d)))
    (hdisj : (S : Set (List (Set (Fin d)))).PairwiseDisjoint E)
    (hpacking : ∀ q ∈ S, ENNReal.ofReal (3 / 4 : ℝ) *
      volume (dyadicDescendant I q : Set (Vec d)) ≤ volume (E q))
    (hminor : ∀ q ∈ S, ∀ᵐ x ∂volume.restrict (dyadicDescendant I q : Set (Vec d)),
      a q ≤ |b x|) {p : ℝ} (hp : 1 < p)
    (hb : MemLp b (ENNReal.ofReal p) (volume.restrict (I : Set (Vec d)))) :
    eLpNorm (finiteSparseSum I S a) (ENNReal.ofReal p)
        (volume.restrict (I : Set (Vec d))) ≤
      ENNReal.ofReal ((4 / 3 : ℝ) * p) *
        eLpNorm b (ENNReal.ofReal p) (volume.restrict (I : Set (Vec d))) := by
  let μ := volume.restrict (I : Set (Vec d))
  let f := finiteSparseSum I S a
  let N := eLpNorm f (ENNReal.ofReal p) μ
  let M := ∫⁻ x, (ENNReal.ofReal (f x)) ^ p ∂μ
  let φ := fun x => f x ^ (p - 1)
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hfnn : ∀ x, 0 ≤ f x := finiteSparseSum_nonneg I S a ha
  have hfmeas : Measurable f := measurable_finiteSparseSum I S a
  have hf : MemLp f (ENNReal.ofReal p) μ := memLp_finiteSparseSum I S a hp0
  have hφ : MemLp φ (ENNReal.ofReal (Real.conjExponent p)) μ :=
    memLp_nonnegativeDualPower hfmeas hfnn hp hf
  have hφmeas : Measurable φ := measurable_nonnegativeDualPower hfmeas hp
  have hφnn : ∀ x, 0 ≤ φ x := fun x => Real.rpow_nonneg (hfnn x) _
  have hφnorm : eLpNorm φ (ENNReal.ofReal (Real.conjExponent p)) μ = N ^ (p - 1) :=
    eLpNorm_nonnegativeDualPower hfnn hp
  have hpair := finite_sparse_pairing_le_eLpNorm_mul I S b φ a E
    hE hsub hdisj hpacking hminor hp hb hφ
  have heq := lintegral_finiteSparseSum_mul_of_nonneg I S a φ ha hφmeas hφnn
  have hmomentPair : (∫⁻ x, ENNReal.ofReal (f x) * ENNReal.ofReal (φ x) ∂μ) = M := by
    apply lintegral_congr
    intro x
    dsimp only [φ, M]
    rw [← ENNReal.ofReal_rpow_of_nonneg (hfnn x) (sub_nonneg.mpr hp.le)]
    have hexp : (1 : ℝ) + (p - 1) = p := by ring
    nth_rw 1 [← ENNReal.rpow_one (ENNReal.ofReal (f x))]
    rw [← ENNReal.rpow_add_of_nonneg (1 : ℝ) (p - 1) (by norm_num : (0 : ℝ) ≤ 1)
        (sub_nonneg.mpr hp.le), hexp]
  have hMN : M = N ^ p :=
    lintegral_nonnegative_rpow_eq_eLpNorm_rpow μ f hfnn hfmeas.aestronglyMeasurable hp0
  have hMtop : M ≠ ⊤ := by
    rw [hMN]
    exact ENNReal.rpow_ne_top_of_nonneg hp0.le hf.eLpNorm_lt_top.ne
  have hresidual : N ^ (p - 1) = M ^ ((p - 1) / p) := by
    rw [hMN, ← ENNReal.rpow_mul]
    congr 1
    field_simp
  have hmain : M ≤
      (ENNReal.ofReal ((4 / 3 : ℝ) * p) * eLpNorm b (ENNReal.ofReal p) μ) *
        M ^ ((p - 1) / p) := by
    have hbound : M ≤
        ENNReal.ofReal ((4 / 3 : ℝ) * p) * eLpNorm b (ENNReal.ofReal p) μ *
          eLpNorm φ (ENNReal.ofReal (Real.conjExponent p)) μ := by
      rw [← hmomentPair, heq]
      simpa only [abs_of_nonneg (hφnn _)] using hpair
    rw [hφnorm, hresidual] at hbound
    exact hbound
  have hcancel := ENNReal.rpow_one_div_le_of_le_mul_rpow hp hMtop hmain
  have hroot : M ^ (1 / p) = N := by
    rw [hMN, ← ENNReal.rpow_mul,
      show p * (1 / p) = 1 by field_simp, ENNReal.rpow_one]
  rw [hroot] at hcancel
  exact hcancel

end PDE
