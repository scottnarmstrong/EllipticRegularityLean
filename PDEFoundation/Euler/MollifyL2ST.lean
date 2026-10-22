module

public import PDEFoundation.Euler.MollifySpaceTime
public import PDEFoundation.Euler.MollifyLp

/-!
# `L²(eulerMeasure)` convergence of spatial mollification

For a space-time function `u`, a.e. strongly measurable for `eulerMeasure T`, `ℤ²`-periodic in `x` at every
time, and a.e. bounded, `mollifyST (aₙ) u → u` in `L²(eulerMeasure T)` along any sequence `aₙ ∈ (0,1]`
tending to `0`.  Proof: Tonelli in `t`, the slice theorem `tendsto_eLpNorm_mollify_cube` for a.e. `t`, and
dominated convergence with the constant bound `(2B)²`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE

theorem lintegral_enorm_sq_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (hf : AEStronglyMeasurable f μ) : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = eLpNorm f 2 μ ^ 2 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  simp

theorem tendsto_lintegral_sq_mollifyST {T : ℝ} {u : Vec 2 × ℝ → ℝ}
    (hu : AEStronglyMeasurable u (eulerMeasure T))
    (hup : ∀ t, IsTorusPeriodic (fun x => u (x, t))) {B : ℝ}
    (hB : ∀ᵐ z ∂(eulerMeasure T), |u z| ≤ B) {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n ≤ 1)
    (ha0 : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ z, ‖mollifyST (a n) u z - u z‖ₑ ^ 2 ∂(eulerMeasure T)) atTop (𝓝 0) := by
  set μc : Measure (Vec 2) := volume.restrict torusCube with hμc
  set νT : Measure ℝ := volume.restrict (Icc 0 T) with hνT
  have hprod : eulerMeasure T = μc.prod νT := eulerMeasure_eq_prod T
  have hfin : IsFiniteMeasure μc :=
    ⟨by rw [hμc, Measure.restrict_apply_univ]; exact (isCompact_Icc : IsCompact torusCube).measure_lt_top⟩
  have hext := aestronglyMeasurable_ext_of_periodic hu hup
  have hmolE : ∀ n, AEStronglyMeasurable (mollifyST (a n) u) (eulerMeasure T) := fun n =>
    (aestronglyMeasurable_mollifyST (a n) hext).mono_measure (eulerMeasure_le_ext T)
  have hgm : ∀ n, AEStronglyMeasurable (fun z => mollifyST (a n) u z - u z) (eulerMeasure T) :=
    fun n => (hmolE n).sub hu
  have hsq : ∀ n, AEMeasurable (fun z => ‖mollifyST (a n) u z - u z‖ₑ ^ 2) (μc.prod νT) := fun n => by
    rw [← hprod]; exact ((hgm n).enorm).pow_const 2
  have hiter : ∀ n, ∫⁻ z, ‖mollifyST (a n) u z - u z‖ₑ ^ 2 ∂(eulerMeasure T) =
      ∫⁻ t, ∫⁻ x, ‖mollifyST (a n) u (x, t) - u (x, t)‖ₑ ^ 2 ∂μc ∂νT := fun n => by
    rw [hprod]; exact lintegral_prod_symm (fun z => ‖mollifyST (a n) u z - u z‖ₑ ^ 2) (hsq n)
  simp_rw [hiter]
  -- slice facts
  have hmeas_t : ∀ᵐ t ∂νT, AEStronglyMeasurable (fun x => u (x, t)) μc := by
    rw [hprod] at hu; exact hu.prodMk_right
  have hbd_t : ∀ᵐ t ∂νT, ∀ᵐ x ∂μc, |u (x, t)| ≤ B := by
    rw [hprod] at hB
    have h1 := (Measure.measurePreserving_swap (μ := νT) (ν := μc)).quasiMeasurePreserving.ae hB
    exact Measure.ae_ae_of_ae_prod h1
  have hgood : ∀ᵐ t ∂νT, AEStronglyMeasurable (fun x => u (x, t)) μc ∧ ∀ᵐ x ∂μc, |u (x, t)| ≤ B :=
    hmeas_t.and hbd_t
  set c : ℝ≥0∞ := ENNReal.ofReal (2 * B) ^ 2 * volume torusCube with hc
  have hcfin : c ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ?_
    exact (isCompact_Icc : IsCompact torusCube).measure_lt_top.ne
  have hFmeas : ∀ n, AEMeasurable (fun t => ∫⁻ x, ‖mollifyST (a n) u (x, t) - u (x, t)‖ₑ ^ 2 ∂μc) νT :=
    fun n => (hsq n).lintegral_prod_left'
  refine (tendsto_lintegral_of_dominated_convergence' (μ := νT)
    (F := fun n t => ∫⁻ x, ‖mollifyST (a n) u (x, t) - u (x, t)‖ₑ ^ 2 ∂μc) (f := fun _ => 0)
    (fun _ => c) hFmeas ?_ ?_ ?_).trans (by simp)
  · -- domination
    intro n
    filter_upwards [hgood] with t ⟨hmeas, hbnd⟩
    have hL2 : MemLp (fun x => u (x, t)) 2 μc := MemLp.of_bound hmeas B hbnd
    have hloc : LocallyIntegrable (fun x => u (x, t)) volume :=
      (hup t).locallyIntegrable (hL2.integrable (by norm_num))
    have hbvol : ∀ᵐ y ∂(volume : Measure (Vec 2)), |u (y, t)| ≤ B :=
      (hup t).ae_of_ae_cube (P := fun r => |r| ≤ B) hbnd
    calc ∫⁻ x, ‖mollifyST (a n) u (x, t) - u (x, t)‖ₑ ^ 2 ∂μc ≤ ∫⁻ _x, ENNReal.ofReal (2 * B) ^ 2 ∂μc := by
          refine lintegral_mono_ae ?_
          filter_upwards [hbnd] with x hx
          have hm := abs_mollify_le (ha n) hloc hbvol x
          have h2 : |mollifyST (a n) u (x, t) - u (x, t)| ≤ 2 * B := by
            have : |mollifyST (a n) u (x, t) - u (x, t)| ≤ |mollifyST (a n) u (x, t)| + |u (x, t)| :=
              abs_sub _ _
            simp only [mollifyST] at this ⊢
            linarith
          gcongr
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal h2
      _ = c := by rw [lintegral_const, hc, hμc, Measure.restrict_apply_univ]
  · -- finiteness
    rw [lintegral_const, hνT, Measure.restrict_apply_univ]
    exact ENNReal.mul_ne_top hcfin (by simp)
  · -- pointwise limit
    filter_upwards [hgood] with t ⟨hmeas, hbnd⟩
    have hL2 : MemLp (fun x => u (x, t)) 2 μc := MemLp.of_bound hmeas B hbnd
    have hconv := tendsto_eLpNorm_mollify_cube (hup t) hL2 ha ha1 ha0
    have hloc : LocallyIntegrable (fun x => u (x, t)) volume :=
      (hup t).locallyIntegrable (hL2.integrable (by norm_num))
    have hsl : ∀ n, AEStronglyMeasurable (fun x => mollify (a n) (fun x => u (x, t)) x - u (x, t)) μc :=
      fun n => ((mollify_contDiff (ha n) hloc).continuous.aestronglyMeasurable).sub hmeas
    have heq : ∀ n, ∫⁻ x, ‖mollifyST (a n) u (x, t) - u (x, t)‖ₑ ^ 2 ∂μc =
        eLpNorm (fun x => mollify (a n) (fun x => u (x, t)) x - u (x, t)) 2 μc ^ 2 := fun n =>
      lintegral_enorm_sq_eq μc _ (hsl n)
    simp_rw [heq]
    have := ((ENNReal.continuous_pow 2).tendsto 0).comp hconv
    rw [show (0 : ℝ≥0∞) ^ 2 = 0 by simp] at this
    exact this

end PDE
