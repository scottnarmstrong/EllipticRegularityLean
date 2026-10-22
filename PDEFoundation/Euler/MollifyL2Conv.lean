module

public import PDEFoundation.Euler.CrossDefs
public import PDEFoundation.Euler.MollifyL2ST
public import PDEFoundation.Euler.L2Prod

/-!
# `L²(eulerMeasure)` convergence of `mollifyVecST (tDelta k)` in `eLpNorm` form, and weighted limits
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE

theorem tendsto_eLpNorm_of_tendsto_lintegral_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} (hf : ∀ k, AEStronglyMeasurable (f k) μ)
    (h : Tendsto (fun k => ∫⁻ z, ‖f k z‖ₑ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (f k) 2 μ) atTop (𝓝 0) := by
  have h2 : Tendsto (fun k => eLpNorm (f k) 2 μ ^ 2) atTop (𝓝 0) :=
    h.congr (fun k => lintegral_enorm_sq_eq μ (f k) (hf k))
  have hroot := ((ENNReal.continuous_rpow_const (y := (2⁻¹ : ℝ))).tendsto 0).comp h2
  have e0 : (0 : ℝ≥0∞) ^ (2⁻¹ : ℝ) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
  rw [e0] at hroot
  refine hroot.congr (fun k => ?_)
  simp only [Function.comp]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem tendsto_eLpNorm_mollifyVecST {T B : ℝ} {w : Vec 2 × ℝ → Vec 2} (hw : EulerBdd T B w) (i : Fin 2) :
    Tendsto (fun k => eLpNorm (fun z => mollifyVecST (tDelta k) w z i - w z i) 2 (eulerMeasure T))
      atTop (𝓝 0) := by
  have h := tendsto_lintegral_sq_mollifyST (T := T) (u := fun z => w z i) (hw.coord_aesm i)
    (fun t => (hw.per t).comp (fun r => r i)) (B := Real.sqrt B) (hw.abs_coord_le i)
    tDelta_pos tDelta_le_one tendsto_tDelta
  refine tendsto_eLpNorm_of_tendsto_lintegral_sq (fun k => ?_) h
  exact (hw.mol_aesm (tDelta k) i).sub (hw.coord_aesm i)

theorem memLp_two_of_bdd {μ : Measure (Vec 2 × ℝ)} [IsFiniteMeasure μ] {f : Vec 2 × ℝ → ℝ}
    (hf : AEStronglyMeasurable f μ) {C : ℝ} (hC : ∀ᵐ z ∂μ, |f z| ≤ C) : MemLp f 2 μ :=
  MemLp.of_bound hf C (hC.mono fun z hz => by simpa [Real.norm_eq_abs] using hz)

end PDE
