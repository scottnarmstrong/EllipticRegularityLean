module

public import EllipticRegularity.Parabolic.WeakHarnack.IterationChain
public import EllipticRegularity.DeGiorgi.MoserIter.EssSup

/-!
# `L^∞` bound from a negative-type power step (Moser iteration)

Iterating the step along `p_k = χ^k` on the sets `U (δ + (1-δ) 2^{-k})` bounds
`‖g‖_{χ^N, U δ}` uniformly in `N`; on a probability measure the limit `N → ∞` is the
essential supremum.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace PDE.ParabIter

variable {X : Type*} [MeasurableSpace X]

/-- The constant `C` of the `L^∞` bound. -/
noncomputable def linC (χ A β m : ℝ) : ℝ :=
  (A * 2 ^ β * 2 ^ m) ^ (χ / (χ - 1) / 1) * (χ ^ β * 2 ^ m) ^ (χ / (χ - 1) ^ 2 / 1)

/-- The exponent `m''` of the `L^∞` bound. -/
noncomputable def linM (χ m : ℝ) : ℝ := m * (χ / (χ - 1) / 1)

/-- Moser iteration for a negative-type power step: the `L^∞` norm on `U δ` is bounded by
`C (1-δ)^{-m''}` times the `L^1` norm on `U 1`; `C, m''` depend only on `A, β, m, χ`. -/
theorem linfty_of_negStep (ν : Measure X) [IsProbabilityMeasure ν] (U : ℝ → Set X)
    (g : X → ℝ) (hg : Measurable g) (hpos : ∀ x, 0 < g x)
    {δ χ A β m : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hχ : 1 < χ) (hA : 1 ≤ A) (hβ : 0 ≤ β)
    (hm : 0 < m)
    (hUmono : ∀ σ' σ, δ ≤ σ' → σ' ≤ σ → σ ≤ 1 → U σ' ⊆ U σ)
    (hstep : ∀ σ' σ : ℝ, δ ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm g (ENNReal.ofReal (χ * p)) (ν.restrict (U σ')) ≤
        ENNReal.ofReal ((A * (1 + p) ^ β * (σ - σ') ^ (-m)) ^ (1 / p)) *
          eLpNorm g (ENNReal.ofReal p) (ν.restrict (U σ))) :
    eLpNorm g ⊤ (ν.restrict (U δ)) ≤
      ENNReal.ofReal (linC χ A β m * (1 - δ) ^ (-linM χ m)) *
        eLpNorm g (ENNReal.ofReal 1) (ν.restrict (U 1)) := by
  have hχ0 : 0 < χ := by linarith
  have hg0 : 0 < 1 - δ := by linarith
  have hg1 : 1 - δ ≤ 1 := by linarith
  have h2β : (1 : ℝ) ≤ 2 ^ β := Real.one_le_rpow (by norm_num) hβ
  have hA' : 1 ≤ A * 2 ^ β := by nlinarith
  have hB : 1 ≤ χ ^ β := Real.one_le_rpow hχ.le hβ
  have hchain : ∀ N : ℕ, eLpNorm g (ENNReal.ofReal (1 * χ ^ N)) (ν.restrict (U δ)) ≤
      ENNReal.ofReal (linC χ A β m * (1 - δ) ^ (-linM χ m)) *
        eLpNorm g (ENNReal.ofReal 1) (ν.restrict (U 1)) := by
    intro N
    have hc := chain_geometric ν U g δ χ m hδ hχ (fun _ => True)
      (fun p => A * (1 + p) ^ β) (fun σ' σ h1 h2 h3 p hp _ => hstep σ' σ h1 h2 h3 p hp)
      hUmono (p₀ := 1) (A₁ := A * 2 ^ β) (B₁ := χ ^ β) hm one_pos hA' hB N
      (fun _ _ => trivial) (fun k _ => by positivity)
      (fun k _ => by
        have hk1 : (1 : ℝ) ≤ χ ^ k := one_le_pow₀ hχ.le
        have h1 : (1 + 1 * χ ^ k) ^ β ≤ (2 * χ ^ k) ^ β :=
          Real.rpow_le_rpow (by positivity) (by linarith) hβ
        have h2 : (2 * χ ^ k) ^ β = 2 ^ β * (χ ^ β) ^ k := by
          rw [Real.mul_rpow (by norm_num) (by positivity), Real.rpow_pow_comm hχ0.le]
        show A * (1 + 1 * χ ^ k) ^ β ≤ A * 2 ^ β * (χ ^ β) ^ k
        calc A * (1 + 1 * χ ^ k) ^ β ≤ A * (2 * χ ^ k) ^ β := by gcongr
          _ = _ := by rw [h2]; ring)
      le_rfl hδ1 le_rfl
    refine hc.trans (le_of_eq ?_)
    congr 2
    simp only [linC, linM]
    have hX : 0 ≤ A * 2 ^ β * 2 ^ m := by positivity
    rw [Real.mul_rpow hX (Real.rpow_nonneg hg0.le _), ← Real.rpow_mul hg0.le]
    have : -(m * (χ / (χ - 1) / 1)) = -m * (χ / (χ - 1) / 1) := by ring
    rw [this]; ring
  have hfin := PDE.DGNMMoser.essSup_ofReal_le_of_eLpNorm_le (μ := ν.restrict (U δ)) (f := g)
    hg.aemeasurable (q := fun N : ℕ => 1 * χ ^ N)
    (Filter.Tendsto.const_mul_atTop one_pos (tendsto_pow_atTop_atTop_of_one_lt hχ)) hchain
  have htop : eLpNorm g ⊤ (ν.restrict (U δ)) =
      essSup (fun x => ENNReal.ofReal (g x)) (ν.restrict (U δ)) := by
    rw [eLpNorm_exponent_top hg.aestronglyMeasurable, eLpNormEssSup_eq_essSup_enorm]
    congr 1
    funext x
    exact Real.enorm_of_nonneg (hpos x).le
  rw [htop]
  exact hfin

end PDE.ParabIter
