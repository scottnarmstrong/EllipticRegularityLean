module

public import PDEFoundation.Euler.CrossLimitTerms

/-!
# The cross-term identity (manuscript Step 3)

For bounded weak solutions `u`, `v` with the same datum `v₀`, `v` having the space-time weak gradient `G`
(`SpaceTimeGrad`), and every smooth `χ` vanishing near `T`:

`∑ᵢ ∫ χ'(t) uᵢvᵢ + ∑ᵢⱼ ∫ χ(t) (uⱼ - vⱼ) uᵢ Gᵢⱼ + χ(0) ‖v₀‖² = 0`,

i.e. `d/dt ⟨u,v⟩ = ∫ ((u-v)·∇v)·u` in the sense of distributions on `[0,T)` with `⟨u,v⟩(0) = ‖v₀‖²`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE

theorem cross_identity {T : ℝ} (hT : 0 < T) {v₀ : Vec 2 → Vec 2} {u v : Vec 2 × ℝ → Vec 2}
    (hu : IsEulerWeakSolutionWithDatum T v₀ u) (hv : IsEulerWeakSolutionWithDatum T v₀ v)
    {B1 B2 : ℝ} (hbu : EulerBdd T B1 u) (hbv : EulerBdd T B2 v)
    {G : Vec 2 × ℝ → Fin 2 → Fin 2 → ℝ} (hG : SpaceTimeGrad T B2 v G)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {b : ℝ} (hbT : b < T) (hχb : ∀ τ, b ≤ τ → χ τ = 0) :
    (∑ i, ∫ z, deriv χ z.2 * (u z i * v z i) ∂(eulerMeasure T)) +
      (∑ i, ∑ j, ∫ z, χ z.2 * (((u z j - v z j) * u z i) * G z i j) ∂(eulerMeasure T)) +
      χ 0 * (∑ i, ∫ x in torusCube, v₀ x i * v₀ x i) = 0 := by
  have hv₀ : MemLp v₀ 2 (volume.restrict torusCube) := hu.2.1
  have hχc : Continuous χ := hχ.continuous
  have hχ'c : Continuous (deriv χ) := continuous_deriv_of_contDiff_top hχ
  have hdivu := ae_slice_div_of_weak hu.1
  have hk : ∀ k, (∫ τ in Icc (0 : ℝ) T, deriv χ τ * crossF (tDelta k) u v τ τ) +
      (∫ τ in Icc (0 : ℝ) T, χ τ * crossH (tDelta k) u v τ τ) +
      (∫ τ in Icc (0 : ℝ) T, χ τ * crossK (tDelta k) u v τ τ) +
      χ 0 * ∑ i, ∫ x in torusCube, v₀ x i * mollifyVec (tDelta k) (periodExt v₀) x i = 0 :=
    fun k => cross_identity_mollified hT hu hv hbu hbv (tDelta_pos k) hχ hbT hχb
  have hlim := (((tendsto_crossF_diag hbu hbv hχ'c).add (tendsto_crossH_diag hbu hbv hG hχc)).add
    (tendsto_crossK_diag hT hbu hbv hdivu hG hχc)).add ((tendsto_datum_term hv₀).const_mul (χ 0))
  have hlim' := hlim.congr (fun k => hk k)
  have h0 := tendsto_nhds_unique hlim' tendsto_const_nhds
  -- rearrange the limit
  have hint : ∀ i j, Integrable (fun z => χ z.2 * (u z i * u z j * G z i j)) (eulerMeasure T) := by
    intro i j
    have h1 : Integrable (fun z => u z i * u z j * G z i j) (eulerMeasure T) := by
      have : Integrable (fun z => G z i j) (eulerMeasure T) := (hG.memLp i j).integrable (by norm_num)
      exact this.bdd_mul ((hbu.prod_aesm i j)) ((hbu.abs_prod_le i j).mono fun z hz => by
        simpa [Real.norm_eq_abs] using hz) |>.congr (Filter.Eventually.of_forall fun z => by simp only)
    exact integrable_cont_mul_coord h1 (hχc.comp continuous_snd)
  have hint2 : ∀ i j, Integrable (fun z => χ z.2 * (u z i * (v z j * G z i j))) (eulerMeasure T) := by
    intro i j
    have h1 : Integrable (fun z => u z i * (v z j * G z i j)) (eulerMeasure T) :=
      ((memLp_coord_mul hbv hG i j).integrable (by norm_num)).bdd_mul (hbu.coord_aesm i)
        ((hbu.abs_coord_le i).mono fun z hz => by simpa [Real.norm_eq_abs] using hz)
    exact integrable_cont_mul_coord h1 (hχc.comp continuous_snd)
  have e : ∀ i j, ∫ z, χ z.2 * (((u z j - v z j) * u z i) * G z i j) ∂(eulerMeasure T) =
      (∫ z, χ z.2 * ((u z i * u z j) * G z i j) ∂(eulerMeasure T)) -
        ∫ z, χ z.2 * (u z i * (v z j * G z i j)) ∂(eulerMeasure T) := by
    intro i j
    rw [← integral_sub (hint i j) (hint2 i j)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only
    ring
  simp only [e, Finset.sum_sub_distrib]
  linarith

end PDE
