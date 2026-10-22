module

public import PDEFoundation.Analysis.HilbertLpDualPower
public import PDEFoundation.Measure.LpPairingNorm
public import Mathlib.Basic.Real.ConjExponents
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! # Exact norm of Hilbert-valued Lp pairings -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

variable {α E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {μ : Measure α}

private theorem norm_hilbertLpPairing_le
    {p q : ENNReal} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (g : Lp E p μ) :
    ‖(innerSL ℝ).lpPairing μ p q g‖ ≤ ‖g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g)
  intro f
  have heq : (innerSL ℝ).lpPairing μ p q g f =
      L1.integral ((innerSL ℝ).holder 1 g f) := by
    rw [ContinuousLinearMap.lpPairing_eq_integral, L1.integral_eq_integral]
    exact integral_congr_ae ((innerSL ℝ).coeFn_holder g f).symm
  rw [heq]
  calc
    _ ≤ ‖((innerSL ℝ).holder 1 g) f‖ := L1.norm_integral_le _
    _ ≤ ‖innerSL ℝ‖ * ‖g‖ * ‖f‖ :=
      ContinuousLinearMap.norm_holder_apply_apply_le _ _ _
    _ ≤ 1 * ‖g‖ * ‖f‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg g)
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro x
      simpa only [one_mul, innerSL_apply_norm] using le_rfl
    _ = ‖g‖ * ‖f‖ := by rw [one_mul]

/-- The standard Hilbert integral pairing against `g` has exactly the `Lʳ`
norm of `g`. -/
theorem norm_hilbertLpPairing_eq
    {r : ℝ} (hr : 1 < r)
    [Fact (1 ≤ ENNReal.ofReal r)]
    [Fact (1 ≤ ENNReal.ofReal (r / (r - 1)))]
    (g : Lp E (ENNReal.ofReal r) μ) :
    letI : ENNReal.HolderConjugate (ENNReal.ofReal r)
        (ENNReal.ofReal (r / (r - 1))) :=
      (Real.HolderConjugate.conjExponent hr).ennrealOfReal
    ‖(innerSL ℝ).lpPairing μ (ENNReal.ofReal r)
        (ENNReal.ofReal (r / (r - 1))) g‖ = ‖g‖ := by
  let : ENNReal.HolderConjugate (ENNReal.ofReal r)
      (ENNReal.ofReal (r / (r - 1))) :=
    (Real.HolderConjugate.conjExponent hr).ennrealOfReal
  let q : ENNReal := ENNReal.ofReal (r / (r - 1))
  let J := (innerSL ℝ).lpPairing μ (ENNReal.ofReal r) q g
  apply le_antisymm
  · exact norm_hilbertLpPairing_le g
  · let gfun : α → E := fun x => g x
    have hg : MemLp gfun (ENNReal.ofReal r) μ := Lp.memLp g
    let hfun : α → E := fun x => hilbertDualPower r (g x)
    have hh := memLp_hilbertDualPower hr hg
    let h : Lp E q μ := hh.1.toLp hfun
    have hnorm : ‖h‖ = ‖g‖ ^ (r - 1) := by
      rw [Lp.norm_toLp, hh.2]
      rw [← ENNReal.toReal_rpow]
      simp only [gfun, Lp.norm_def]
    have hpair : J h = ‖g‖ ^ r := by
      have hmom : ∫ x, inner ℝ (g x) (hilbertDualPower r (g x)) ∂μ =
          ‖g‖ ^ r := by
        simpa only [gfun, Lp.norm_def] using
          integral_real_inner_hilbertDualPower hr hg
      dsimp only [J]
      rw [ContinuousLinearMap.lpPairing_eq_integral]
      rw [← hmom]
      apply integral_congr_ae
      filter_upwards [hh.1.coeFn_toLp] with x hx
      rw [hx]
      rfl
    by_cases hg0 : ‖g‖ = 0
    · rw [hg0]
      exact norm_nonneg ((innerSL ℝ).lpPairing μ (ENNReal.ofReal r)
        (ENNReal.ofReal (r / (r - 1))) g)
    · have hgpos : 0 < ‖g‖ := lt_of_le_of_ne (norm_nonneg g) (Ne.symm hg0)
      have hop : |J h| ≤ ‖J‖ * ‖h‖ := by
        simpa only [Real.norm_eq_abs] using J.le_opNorm h
      rw [hpair, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg g) _), hnorm] at hop
      have hsplit : ‖g‖ ^ r = ‖g‖ * ‖g‖ ^ (r - 1) := by
        calc
          ‖g‖ ^ r = ‖g‖ ^ (1 + (r - 1)) := by congr 1; ring
          _ = ‖g‖ ^ (1 : ℝ) * ‖g‖ ^ (r - 1) := Real.rpow_add hgpos _ _
          _ = ‖g‖ * ‖g‖ ^ (r - 1) := by rw [Real.rpow_one]
      rw [hsplit] at hop
      exact le_of_mul_le_mul_right hop (Real.rpow_pos_of_pos hgpos _)

end

end PDE
