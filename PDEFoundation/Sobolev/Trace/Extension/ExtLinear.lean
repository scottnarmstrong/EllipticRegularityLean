module

public import PDEFoundation.Sobolev.Trace.Extension.Defs
public import PDEFoundation.Sobolev.Trace.Extension.ExtBesov
import PDEFoundation.Sobolev.Trace.Smooth.Scalar
import PDEFoundation.Sobolev.Trace.Smooth.Pullback

/-!
# Linearity of the extension operator

The flat boundary data `D.flat j g` is linear in `g` and lies in `L^p(Vec n)` for `g` in the Besov
class, so linearity of `modelExt` (on `L^p`) gives linearity of `D.ext` on the Besov class.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped ENNReal NNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

theorem ExtData.flat_add (D : ExtData Ω) (j : Fin D.A.N) (g h : Vec (n + 1) → ℝ) :
    D.flat j (g + h) = D.flat j g + D.flat j h := by
  funext x'
  simp [ExtData.flat, flatPullback, mul_add]

theorem ExtData.flat_smul (D : ExtData Ω) (j : Fin D.A.N) (a : ℝ) (g : Vec (n + 1) → ℝ) :
    D.flat j (a • g) = a • D.flat j g := by
  funext x'
  simp [ExtData.flat, flatPullback]
  ring

theorem ExtData.contDiff_ζ (D : ExtData Ω) (j : Fin D.A.N) : ContDiff ℝ 1 (D.A.ζ j) :=
  (D.A.ζ_smooth j).of_le (by exact_mod_cast le_top)

theorem ExtData.contDiff_η (D : ExtData Ω) (j : Fin D.A.N) : ContDiff ℝ 1 (D.η j) :=
  (D.η_smooth j).of_le (by exact_mod_cast le_top)

/-- The flat data of a function in `L^p(σ)` is a.e. strongly measurable. -/
theorem ExtData.aestronglyMeasurable_flat (D : ExtData Ω) (j : Fin D.A.N) {g : Vec (n + 1) → ℝ}
    (hg : AEMeasurable g (boundarySurfaceMeasure Ω)) :
    AEStronglyMeasurable (D.flat j g) volume := by
  have h1 := flatPullback_ae_eq (D.A.chart j) (D.A.ζ_tsupport j) hg.ae_eq_mk
  have hmap : Measurable fun x' : Vec n => (D.A.chart j).map (x', 0) :=
    (D.A.chart j).continuous_map.measurable.comp (measurable_id.prodMk measurable_const)
  have hm : Measurable (flatPullback (D.A.chart j) (D.A.ζ j) (hg.mk g)) :=
    ((D.contDiff_ζ j).continuous.measurable.comp hmap).mul (hg.measurable_mk.comp hmap)
  exact (hm.aestronglyMeasurable.congr h1.symm)

/-- The `p`-th power integral of a function in the Besov class is finite. -/
theorem ext_lintegral_rpow_lt_top {p : ℝ} (hp : 1 < p) {g : Vec (n + 1) → ℝ}
    (hg : IsBesov Ω (1 - 1 / p) p g) :
    ∫⁻ x, ENNReal.ofReal (|g x| ^ p) ∂boundarySurfaceMeasure Ω < ⊤ := by
  rw [lintegral_ofReal_rpow_eq (by linarith) hg.1.aestronglyMeasurable]
  refine ENNReal.rpow_lt_top_of_nonneg (by linarith) (lt_top_iff_ne_top.1 ?_)
  exact (le_self_add.trans_lt hg.2)

theorem ExtData.memLp_flat (D : ExtData Ω) (j : Fin D.A.N) {p : ℝ} (hp : 1 < p)
    {g : Vec (n + 1) → ℝ} (hg : IsBesov Ω (1 - 1 / p) p g) :
    MemLp (D.flat j g) (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  have hm := D.aestronglyMeasurable_flat j hg.1
  obtain ⟨C, hC⟩ := flatPullback_Lp_le (D.A.chart j) (D.contDiff_ζ j).continuous
    (D.A.ζ_compact j) (D.A.ζ_tsupport j) hp
  show eLpNorm _ _ _ < ⊤
  rw [eLpNorm_eq_lintegral_ofReal_rpow hp0 hm]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) (lt_top_iff_ne_top.1 ?_)
  exact ((hC g hg.1).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top
    (ext_lintegral_rpow_lt_top hp hg)))

theorem ExtData.ext_add (D : ExtData Ω) {p : ℝ} (hp : 1 < p) {g h : Vec (n + 1) → ℝ}
    (hg : IsBesov Ω (1 - 1 / p) p g) (hh : IsBesov Ω (1 - 1 / p) p h) :
    D.ext (g + h) = D.ext g + D.ext h := by
  funext x
  simp only [ExtData.ext, Pi.add_apply, ← Finset.sum_add_distrib, ← mul_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [D.flat_add, modelExt_add hp _ _ (D.memLp_flat j hp hg) (D.memLp_flat j hp hh)]
  rfl

theorem ExtData.ext_smul (D : ExtData Ω) (a : ℝ) (g : Vec (n + 1) → ℝ) :
    D.ext (a • g) = a • D.ext g := by
  funext x
  simp only [ExtData.ext, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [D.flat_smul, modelExt_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end PDE.TraceLane
