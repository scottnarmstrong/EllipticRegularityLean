module

public import PDEFoundation.Euler.CrossDatum

/-!
# The cross-term identity at a fixed mollification scale

For two bounded weak solutions `u`, `v` with the same datum `v₀`, a mollification scale `a > 0` and a smooth
cut-off `χ` vanishing near `T`:

`∫ χ'(τ) ⟨u(τ), vᵃ(τ)⟩ + ∫ χ(τ) (⟨uuᵀ(τ), ∇vᵃ(τ)⟩ + ⟨vvᵀ(τ), ∇uᵃ(τ)⟩) + χ(0) ⟨v₀, ζ₀ᵃ⟩ = 0`,

where `ζ₀ᵃ` is the mollified periodic extension of `v₀`.  Proof: the time-mollified product rule
(`time_product_identity`) with the slice hypotheses `cross_hU`, `cross_hV`, followed by the diagonal limit
`n → ∞` of the time mollifier and weak continuity at time zero.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace PDE

theorem cross_identity_mollified {T : ℝ} (hT : 0 < T) {v₀ : Vec 2 → Vec 2} {u v : Vec 2 × ℝ → Vec 2}
    (hu : IsEulerWeakSolutionWithDatum T v₀ u) (hv : IsEulerWeakSolutionWithDatum T v₀ v)
    {B1 B2 : ℝ} (hbu : EulerBdd T B1 u) (hbv : EulerBdd T B2 v) {a : ℝ} (ha : 0 < a)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {b : ℝ} (hbT : b < T)
    (hχb : ∀ τ, b ≤ τ → χ τ = 0) :
    (∫ τ, deriv χ τ * crossF a u v τ τ ∂(volume.restrict (Icc (0 : ℝ) T))) +
      (∫ τ, χ τ * crossH a u v τ τ ∂(volume.restrict (Icc (0 : ℝ) T))) +
      (∫ τ, χ τ * crossK a u v τ τ ∂(volume.restrict (Icc (0 : ℝ) T))) +
      χ 0 * ∑ i, ∫ x in torusCube, v₀ x i * mollifyVec a (periodExt v₀) x i = 0 := by
  set ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) T) with hν
  have hv₀ : MemLp v₀ 2 (volume.restrict torusCube) := hu.2.1
  obtain ⟨hζs, hζp, hζd⟩ := datum_mollify_props ha hv₀ hu.2.2.1
  set ζ0 : Vec 2 → Vec 2 := mollifyVec a (periodExt v₀) with hζ0
  set D0 : ℝ := ∑ i, ∫ x in torusCube, v₀ x i * ζ0 x i with hD0
  have hχc : Continuous χ := hχ.continuous
  have hχ'c : Continuous (deriv χ) := continuous_deriv_of_contDiff_top hχ
  -- integrability hypotheses of the product rule
  have hFi : Integrable (fun p : ℝ × ℝ => crossF a u v p.1 p.2) (ν.prod ν) := by
    have := integrable_finsetSum (Finset.univ : Finset (Fin 2)) fun i _ =>
      bilin_integrable (μ := volume.restrict torusCube) (T := T) (A := Real.sqrt B1) (B := Real.sqrt B2)
        (a := fun p => u p i) (b := fun p => mollifyVecST a v p i) (Real.sqrt_nonneg _)
        (by rw [← eulerMeasure_eq_prod]; exact hbu.coord_aesm i)
        (by rw [← eulerMeasure_eq_prod]; exact hbv.mol_aesm a i)
        (by rw [← eulerMeasure_eq_prod]; exact hbu.abs_coord_le i)
        (by rw [← eulerMeasure_eq_prod]; exact hbv.abs_mol_le ha i)
    exact this
  have hHi : Integrable (fun p : ℝ × ℝ => crossH a u v p.1 p.2) (ν.prod ν) := by
    have := integrable_finsetSum (Finset.univ : Finset (Fin 2 × Fin 2)) fun p _ =>
      bilin_integrable (μ := volume.restrict torusCube) (T := T) (A := B1)
        (B := pdMolKNorm a p.2 * Real.sqrt B2)
        (a := fun z => u z p.1 * u z p.2) (b := fun z => gradMollST a v z p.1 p.2) hbu.nonneg
        (by rw [← eulerMeasure_eq_prod]; exact hbu.prod_aesm p.1 p.2)
        (by rw [← eulerMeasure_eq_prod]; exact hbv.grad_aesm ha p.1 p.2)
        (by rw [← eulerMeasure_eq_prod]; exact hbu.abs_prod_le p.1 p.2)
        (by rw [← eulerMeasure_eq_prod]; exact hbv.abs_grad_le ha p.1 p.2)
    have e : ∀ p : ℝ × ℝ, crossH a u v p.1 p.2 = ∑ q : Fin 2 × Fin 2, ∫ x in torusCube,
        (u (x, p.1) q.1 * u (x, p.1) q.2) * gradMollST a v (x, p.2) q.1 q.2 :=
      fun p => crossH_eq_sum a u v p.1 p.2
    simp only [e]
    exact this
  have hKi : Integrable (fun p : ℝ × ℝ => crossK a u v p.1 p.2) (ν.prod ν) := by
    have := integrable_finsetSum (Finset.univ : Finset (Fin 2 × Fin 2)) fun p _ =>
      bilin_integrable (μ := volume.restrict torusCube) (T := T)
        (A := pdMolKNorm a p.2 * Real.sqrt B1) (B := B2)
        (a := fun z => gradMollST a u z p.1 p.2) (b := fun z => v z p.1 * v z p.2)
        (mul_nonneg (pdMolKNorm_nonneg a p.2) (Real.sqrt_nonneg _))
        (by rw [← eulerMeasure_eq_prod]; exact hbu.grad_aesm ha p.1 p.2)
        (by rw [← eulerMeasure_eq_prod]; exact hbv.prod_aesm p.1 p.2)
        (by rw [← eulerMeasure_eq_prod]; exact hbu.abs_grad_le ha p.1 p.2)
        (by rw [← eulerMeasure_eq_prod]; exact hbv.abs_prod_le p.1 p.2)
    have e : ∀ p : ℝ × ℝ, crossK a u v p.1 p.2 = ∑ q : Fin 2 × Fin 2, ∫ x in torusCube,
        gradMollST a u (x, p.1) q.1 q.2 * (v (x, p.2) q.1 * v (x, p.2) q.2) := by
      intro p
      rw [crossK_eq_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      ring
    simp only [e]
    exact this
  have hU := cross_hU hT hu hv hbu hbv ha
  have hV := cross_hV hT hu hv hbu hbv ha
  -- limits of the five terms
  have hdat1 : Tendsto (fun n : ℕ => ∫ σ, etaK n σ * crossD a v₀ v σ ∂ν) atTop (𝓝 ((1 / 2) * D0)) := by
    have hwc := weak_cont_zero hT hv hbv.bdd (ζ := ζ0) hζs hζp hζd (χ := fun _ => (1 : ℝ)) contDiff_const
    simp only [one_mul] at hwc
    refine hwc.congr' (Filter.Eventually.of_forall fun n => ?_)
    refine integral_congr_ae ?_
    filter_upwards [crossD_eq_ae hv₀ hbv ha] with σ hσ
    rw [hσ]
  have hdat2 : Tendsto (fun n : ℕ => ∫ τ, χ τ * (etaK n τ * crossD a v₀ u τ) ∂ν) atTop
      (𝓝 (χ 0 * (1 / 2) * D0)) := by
    have hwc := weak_cont_zero hT hu hbu.bdd (ζ := ζ0) hζs hζp hζd hχ
    refine hwc.congr' (Filter.Eventually.of_forall fun n => ?_)
    refine integral_congr_ae ?_
    filter_upwards [crossD_eq_ae hv₀ hbu ha] with τ hτ
    rw [hτ]
  have hn : ∀ᶠ n : ℕ in atTop, b + tDelta n < T := by
    exact (tendsto_tDelta.eventually (gt_mem_nhds (sub_pos.2 hbT))).mono fun n hn => by linarith
  have hE : ∀ᶠ n : ℕ in atTop,
      (∫ τ, deriv χ τ * ∫ σ, etaK n (σ - τ) * crossF a u v τ σ ∂ν ∂ν) +
      (∫ τ, χ τ * ∫ σ, etaK n (σ - τ) * crossH a u v τ σ ∂ν ∂ν) +
      (∫ τ, χ τ * ∫ σ, etaK n (σ - τ) * crossK a u v τ σ ∂ν ∂ν) +
      χ 0 * (∫ σ, etaK n σ * crossD a v₀ v σ ∂ν) +
      (∫ τ, χ τ * (etaK n τ * crossD a v₀ u τ) ∂ν) = 0 := by
    filter_upwards [hn] with n hn
    exact time_product_identity n hFi hHi hKi (crossD_integrable hv₀ hbv ha)
      (crossD_integrable hv₀ hbu ha) hU hV hχ hn hχb
  have hlim := (((((tendsto_crossF hbu hbv ha hχ'c).add (tendsto_crossH hbu hbv ha hχc)).add
    (tendsto_crossK hbu hbv ha hχc)).add (hdat1.const_mul (χ 0))).add hdat2)
  have h0 : Tendsto (fun n : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have hlim' := hlim.congr' (hE.mono fun n hn => hn)
  have := tendsto_nhds_unique hlim' h0
  linarith

end PDE
