module

public import PDEFoundation.Euler.CrossSlices
public import PDEFoundation.Euler.PeriodExt
public import PDEFoundation.Euler.MollifySymmL1

/-!
# The mollified datum

`ζ₀ = mollifyVec a (periodExt v₀)` is a smooth periodic divergence-free field when `v₀ ∈ L²(cube)` is weakly
divergence free, and `crossD a v₀ w σ = ∑ᵢ ∫_cube wᵢ(x,σ) ζ₀ᵢ(x) dx` for a.e. `σ`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace PDE

theorem datum_coord_integrable {v₀ : Vec 2 → Vec 2} (hv₀ : MemLp v₀ 2 (volume.restrict torusCube))
    (i : Fin 2) : Integrable (fun x => v₀ x i) (volume.restrict torusCube) :=
  (hv₀.eval i).integrable (by norm_num)

theorem datum_periodExt_locInt {v₀ : Vec 2 → Vec 2} (hv₀ : MemLp v₀ 2 (volume.restrict torusCube))
    (i : Fin 2) : LocallyIntegrable (fun x => periodExt v₀ x i) volume := by
  have hp : IsTorusPeriodic (fun x => periodExt v₀ x i) := (isTorusPeriodic_periodExt v₀).comp (fun r => r i)
  refine hp.locallyIntegrable ?_
  refine (datum_coord_integrable hv₀ i).congr ?_
  filter_upwards [ae_periodExt_eq v₀] with x hx
  rw [hx]

theorem datum_mollify_props {v₀ : Vec 2 → Vec 2} {a : ℝ} (ha : 0 < a)
    (hv₀ : MemLp v₀ 2 (volume.restrict torusCube))
    (hdiv₀ : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsTorusPeriodic ψ →
      ∫ x in torusCube, vecDot (v₀ x) (fun j => fderiv ℝ ψ x (basisVec j)) = 0) :
    (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => mollifyVec a (periodExt v₀) x i)) ∧
    IsTorusPeriodic (mollifyVec a (periodExt v₀)) ∧
    (∀ x, torusDiv (mollifyVec a (periodExt v₀)) x = 0) := by
  have hloc := datum_periodExt_locInt hv₀
  refine ⟨contDiff_mollifyVec ha hloc, isTorusPeriodic_mollifyVec (isTorusPeriodic_periodExt v₀),
    fun x => torusDiv_mollifyVec ha (isTorusPeriodic_periodExt v₀) hloc (fun ψ hψ hψp => ?_) x⟩
  rw [← hdiv₀ ψ hψ hψp]
  refine integral_congr_ae ?_
  filter_upwards [ae_periodExt_eq v₀] with x hx
  simp only [hx, pd_def]

theorem crossD_integrable {T : ℝ} {v₀ : Vec 2 → Vec 2} (hv₀ : MemLp v₀ 2 (volume.restrict torusCube))
    {B : ℝ} {w : Vec 2 × ℝ → Vec 2} (hw : EulerBdd T B w) {a : ℝ} (ha : 0 < a) :
    Integrable (crossD a v₀ w) (volume.restrict (Icc (0 : ℝ) T)) := by
  unfold crossD
  refine integrable_finsetSum _ fun i _ => ?_
  have := datum_integrable (μ := volume.restrict torusCube) (T := T)
    (b := fun p => mollifyVecST a w p i) (B := Real.sqrt B) (datum_coord_integrable hv₀ i)
    (by rw [← eulerMeasure_eq_prod]; exact hw.mol_aesm a i)
    (by rw [← eulerMeasure_eq_prod]; exact hw.abs_mol_le ha i)
  exact this

theorem crossD_eq_ae {T : ℝ} {v₀ : Vec 2 → Vec 2} (hv₀ : MemLp v₀ 2 (volume.restrict torusCube))
    {B : ℝ} {w : Vec 2 × ℝ → Vec 2} (hw : EulerBdd T B w) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ σ ∂(volume.restrict (Icc (0 : ℝ) T)), crossD a v₀ w σ =
      ∑ i, ∫ x in torusCube, w (x, σ) i * mollifyVec a (periodExt v₀) x i := by
  filter_upwards [ae_slice_locInt hw.meas hw.per hw.bdd] with σ hσ
  unfold crossD
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsymm := integral_cube_mollify_mul_comm_L1 ha (f := fun y => periodExt v₀ y i)
    (g := fun y => w (y, σ) i) ((isTorusPeriodic_periodExt v₀).comp (fun r => r i))
    ((hw.per σ).comp (fun r => r i)) (datum_periodExt_locInt hv₀ i) (hσ.1 i)
    (Bg := Real.sqrt B) (abs_slice_coord_le hσ.2 i)
  have h1 : ∫ x in torusCube, v₀ x i * mollifyVecST a w (x, σ) i =
      ∫ x in torusCube, mollify a (fun y => w (y, σ) i) x * periodExt v₀ x i := by
    refine integral_congr_ae ?_
    filter_upwards [ae_periodExt_eq v₀] with x hx
    simp only [mollifyVecST, mollifyVec_apply, hx]
    ring
  rw [h1, hsymm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [mollifyVec_apply]
  ring

end PDE
