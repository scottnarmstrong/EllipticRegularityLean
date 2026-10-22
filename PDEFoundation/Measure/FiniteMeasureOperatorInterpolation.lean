module

public import PDEFoundation.Measure.FiniteAtomInputInterpolation
public import PDEFoundation.Measure.LpTendsto
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

@[expose] public section

namespace PDE

open Filter MeasureTheory Set Function
open scoped ENNReal Topology

noncomputable section

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Genuine `L²` and `L⁴` operator bounds interpolate on arbitrary finite
measure spaces, with output membership derived from finite atom approximation. -/
theorem memLp_and_eLpNorm_operator_le_of_two_four
    (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν)
    {p M : ℝ} (hp : 2 ≤ p) (hpFour : p ≤ 4) (hM : 1 ≤ M)
    (hTwo : ∀ f : Lp ℝ 2 μ, MemLp f 2 μ →
      eLpNorm (T f) 2 ν ≤ ENNReal.ofReal M * eLpNorm f 2 μ)
    (hFour : ∀ f : Lp ℝ 2 μ, MemLp f 4 μ →
      eLpNorm (T f) 4 ν ≤ ENNReal.ofReal M * eLpNorm f 4 μ)
    (f : Lp ℝ 2 μ) (hfp : MemLp f (ENNReal.ofReal p) μ) :
    MemLp (T f) (ENNReal.ofReal p) ν ∧
      eLpNorm (T f) (ENNReal.ofReal p) ν ≤
        ENNReal.ofReal M * eLpNorm f (ENNReal.ofReal p) μ := by
  let ε : ℕ → ENNReal := fun n => ((n + 1 : ℕ) : ENNReal)⁻¹
  have hεne (n : ℕ) : ε n ≠ 0 := by simp [ε]
  have hex (n : ℕ) : ∃ g : SimpleFunc α ℝ,
      eLpNorm ((f : α → ℝ) - ⇑g) (ENNReal.ofReal p) μ < ε n ∧
        MemLp g (ENNReal.ofReal p) μ :=
    hfp.exists_simpleFunc_eLpNorm_sub_lt ENNReal.ofReal_ne_top (hεne n)
  choose s hs hsp using hex
  have hε : Tendsto ε atTop (𝓝 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have hsconv : Tendsto
      (fun n => eLpNorm ((f : α → ℝ) - ⇑(s n))
        (ENNReal.ofReal p) μ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hε (fun _ => bot_le) (fun n => (hs n).le)
  have hsconv' : Tendsto
      (fun n => eLpNorm (⇑(s n) - (f : α → ℝ))
        (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
    have heq : (fun n => eLpNorm (⇑(s n) - (f : α → ℝ))
        (ENNReal.ofReal p) μ) =
        fun n => eLpNorm ((f : α → ℝ) - ⇑(s n))
          (ENNReal.ofReal p) μ := by
      funext n
      rw [← eLpNorm_neg]
      apply eLpNorm_congr_ae
      exact Filter.Eventually.of_forall fun x => by simp
    rw [heq]
    exact hsconv
  have hpENN : (2 : ENNReal) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_ofNat]
    exact ENNReal.ofReal_le_ofReal hp
  have hsTwo (n : ℕ) : MemLp (s n) 2 μ :=
    (hsp n).mono_exponent hpENN
  let s₂ : ℕ → Lp ℝ 2 μ := fun n => (hsTwo n).toLp (s n)
  have hmeasureTop : μ Set.univ ≠ ∞ := measure_ne_top μ Set.univ
  let C : ENNReal := μ Set.univ ^
    (1 / (2 : ENNReal).toReal - 1 / (ENNReal.ofReal p).toReal)
  have hCtop : C ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg
    · rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ p)]
      norm_num
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) hp
    · exact hmeasureTop
  have hsTwoConv : Tendsto
      (fun n => eLpNorm (⇑(s n) - (f : α → ℝ)) 2 μ)
      atTop (𝓝 0) := by
    have hbound (n : ℕ) :
        eLpNorm (⇑(s n) - (f : α → ℝ)) 2 μ ≤
          eLpNorm (⇑(s n) - (f : α → ℝ)) (ENNReal.ofReal p) μ * C := by
      exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpENN
        ((hsp n).sub hfp).aestronglyMeasurable
    have hupper : Tendsto
        (fun n => eLpNorm (⇑(s n) - (f : α → ℝ))
          (ENNReal.ofReal p) μ * C) atTop (𝓝 0) := by
      simpa only [zero_mul] using
        ENNReal.Tendsto.mul_const hsconv' (Or.inr hCtop)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hupper (fun _ => bot_le) hbound
  have hsLp : Tendsto s₂ atTop (𝓝 f) := by
    simpa only [s₂, Lp.toLp_coeFn] using
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (fun n => ⇑(s n)) hsTwo (f : α → ℝ) (Lp.memLp f)).mpr hsTwoConv
  have hTLp : Tendsto (fun n => T (s₂ n)) atTop (𝓝 (T f)) :=
    T.continuous.continuousAt.tendsto.comp hsLp
  have hToutTwo : Tendsto
      (fun n => eLpNorm ((T (s₂ n) : β → ℝ) - (T f : β → ℝ)) 2 ν)
      atTop (𝓝 0) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n => (T (s₂ n) : β → ℝ)) (fun n => Lp.memLp (T (s₂ n)))
      (T f : β → ℝ) (Lp.memLp (T f))).mp
    simpa only [Lp.toLp_coeFn] using hTLp
  have hconv : TendstoInMeasure ν (fun n => (T (s₂ n) : β → ℝ)) atTop (T f) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hToutTwo
  have hsAtom (n : ℕ) :
      s₂ n = finiteAtomInputLinearMap μ
        (simpleFuncAtomSet (s n)) (measurableSet_simpleFuncAtomSet (s n))
        (simpleFuncAtomValue (s n)) := by
    apply Lp.ext
    filter_upwards [(hsTwo n).coeFn_toLp,
      finiteAtomInputLinearMap_ae_eq_finiteDisjointAtomSum μ
        (simpleFuncAtomSet (s n)) (measurableSet_simpleFuncAtomSet (s n))
        (simpleFuncAtomValue (s n))] with x hx hsx
    rw [hsx, finiteDisjointAtomSum_simpleFuncAtomSet]
    exact hx
  have happrox (n : ℕ) :
      MemLp (T (s₂ n)) (ENNReal.ofReal p) ν ∧
        eLpNorm (T (s₂ n)) (ENNReal.ofReal p) ν ≤
          ENNReal.ofReal M * eLpNorm (s n) (ENNReal.ofReal p) μ := by
    rw [hsAtom n]
    simpa only [finiteDisjointAtomSum_simpleFuncAtomSet] using
      memLp_and_eLpNorm_operator_finiteAtomInput_le_of_two_four
        μ ν (simpleFuncAtomSet (s n))
        (measurableSet_simpleFuncAtomSet (s n))
        (pairwise_disjoint_simpleFuncAtomSet (s n)) T
        hp hpFour hM hTwo hFour (simpleFuncAtomValue (s n))
  have hnorms : Tendsto
      (fun n => eLpNorm (s n) (ENNReal.ofReal p) μ)
      atTop (𝓝 (eLpNorm f (ENNReal.ofReal p) μ)) :=
    tendsto_eLpNorm_of_tendsto_sub
      (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith))
      (fun n => (hsp n).aestronglyMeasurable) hfp.aestronglyMeasurable
      hfp.eLpNorm_ne_top hsconv'
  let B : ENNReal := ENNReal.ofReal M * eLpNorm f (ENNReal.ofReal p) μ
  have hBtop : B ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfp.eLpNorm_ne_top
  have hb : Tendsto
      (fun n => ENNReal.ofReal M * eLpNorm (s n) (ENNReal.ofReal p) μ)
      atTop (𝓝 B) := by
    exact ENNReal.Tendsto.const_mul hnorms (Or.inr ENNReal.ofReal_ne_top)
  exact memLp_and_eLpNorm_le_of_tendstoInMeasure
    (fun n => (T (s₂ n) : β → ℝ)) (T f)
    (fun n => (happrox n).1) hconv
    (fun n => ENNReal.ofReal M * eLpNorm (s n) (ENNReal.ofReal p) μ)
    B hBtop hb (fun n => (happrox n).2)

end

end PDE
