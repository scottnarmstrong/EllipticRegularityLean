module

public import PDEFoundation.Euler.SliceCor
public import PDEFoundation.Euler.GradLimitBasic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# The weak formulation tested with products `θ(t) ζ(x)`

For a weak solution `u` with datum `v₀` that is a.e. bounded, a smooth periodic divergence-free field `ζ(x)` and
a smooth `θ(t)` vanishing near the terminal time, the identity of `Defs.lean` takes the integrated-in-time form
`∫₀ᵀ θ'(τ) ⟨u(τ),ζ⟩ + θ(τ) ⟨u(τ)⊗u(τ), ∇ζ⟩ dτ + θ(0) ⟨v₀, ζ⟩ = 0`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

theorem fderiv_timeSplit_time {χ : ℝ → ℝ} {φ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (z : Vec 2 × ℝ) :
    fderiv ℝ (timeSplit χ φ) z (0, 1) = deriv χ z.2 * φ z.1 := by
  have h1 : HasFDerivAt (fun z : Vec 2 × ℝ => χ z.2)
      ((fderiv ℝ χ z.2).comp (ContinuousLinearMap.snd ℝ (Vec 2) ℝ)) z :=
    ((hχ.differentiable (by simp)) z.2).hasFDerivAt.comp z (ContinuousLinearMap.snd ℝ (Vec 2) ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun z : Vec 2 × ℝ => φ z.1)
      ((fderiv ℝ φ z.1).comp (ContinuousLinearMap.fst ℝ (Vec 2) ℝ)) z :=
    ((hφ.differentiable (by simp)) z.1).hasFDerivAt.comp z (ContinuousLinearMap.fst ℝ (Vec 2) ℝ).hasFDerivAt
  have h3 : HasFDerivAt (fun z : Vec 2 × ℝ => χ z.2 * φ z.1)
      (χ z.2 • (fderiv ℝ φ z.1).comp (ContinuousLinearMap.fst ℝ (Vec 2) ℝ) +
        φ z.1 • (fderiv ℝ χ z.2).comp (ContinuousLinearMap.snd ℝ (Vec 2) ℝ)) z := h1.mul h2
  rw [show timeSplit χ φ = fun z => χ z.2 * φ z.1 from rfl, h3.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', map_zero, smul_eq_mul]
  rw [mul_zero, zero_add, mul_comm]
  rfl

/-- The vector product test field `θ(t) ζ(x)`. -/
noncomputable def timeSplitVec (θ : ℝ → ℝ) (ζ : Vec 2 → Vec 2) : Vec 2 × ℝ → Vec 2 :=
  fun z i => θ z.2 * ζ z.1 i

theorem eulerTimeDeriv_timeSplitVec {θ : ℝ → ℝ} {ζ : Vec 2 → Vec 2} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hζ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => ζ x i)) (z : Vec 2 × ℝ) (i : Fin 2) :
    eulerTimeDeriv (timeSplitVec θ ζ) z i = deriv θ z.2 * ζ z.1 i :=
  fderiv_timeSplit_time hθ (hζ i) z

theorem eulerSpaceDeriv_timeSplitVec {θ : ℝ → ℝ} {ζ : Vec 2 → Vec 2} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hζ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => ζ x i)) (z : Vec 2 × ℝ) (i j : Fin 2) :
    eulerSpaceDeriv (timeSplitVec θ ζ) z i j = θ z.2 * gradMat ζ z.1 i j :=
  fderiv_timeSplit hθ (hζ i) z j

theorem integrable_cont_mul_coord {T : ℝ} {A : Vec 2 × ℝ → ℝ} (hA : Integrable A (eulerMeasure T))
    {g : Vec 2 × ℝ → ℝ} (hg : Continuous g) : Integrable (fun z => g z * A z) (eulerMeasure T) := by
  simpa only [mul_comm] using integrable_mul_cont_ST hA hg

theorem integrable_coord_mul_coord {T : ℝ} {u : Vec 2 × ℝ → Vec 2}
    (hu : AEStronglyMeasurable u (eulerMeasure T)) {B : ℝ}
    (hB : ∀ᵐ z ∂(eulerMeasure T), vecNormSq (u z) ≤ B) (i j : Fin 2) :
    Integrable (fun z => u z i * u z j) (eulerMeasure T) := by
  refine Integrable.of_bound (C := Real.sqrt B * Real.sqrt B)
    (((continuous_apply i).comp_aestronglyMeasurable hu).mul
      ((continuous_apply j).comp_aestronglyMeasurable hu)) ?_
  filter_upwards [hB] with z hz
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (abs_coord_le_sqrt hz i) (abs_coord_le_sqrt hz j) (abs_nonneg _)
    ((abs_nonneg _).trans (abs_coord_le_sqrt hz i))

theorem integrable_datum_mul {v₀ : Vec 2 → Vec 2} (hv₀ : MemLp v₀ 2 (volume.restrict torusCube))
    {ζ : Vec 2 → ℝ} (hζ : Continuous ζ) (i : Fin 2) :
    Integrable (fun x => v₀ x i * ζ x) (volume.restrict torusCube) := by
  have h1 : Integrable (fun x => v₀ x i) (volume.restrict torusCube) :=
    (hv₀.eval i).integrable (by norm_num)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact torusCube).exists_bound_of_continuousOn hζ.continuousOn
  exact h1.mul_bdd hζ.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hC))

/-- **Weak formulation with product test fields**, integrated in time, componentwise form
`∫₀ᵀ θ' ∑ᵢ ⟨uᵢ(τ), ζᵢ⟩ + θ ∑ᵢⱼ ⟨uᵢuⱼ(τ), ∂ⱼζᵢ⟩ dτ + θ(0) ∑ᵢ ⟨v₀ᵢ, ζᵢ⟩ = 0`. -/
theorem weak_formulation_product {T : ℝ} {v₀ : Vec 2 → Vec 2} {u : Vec 2 × ℝ → Vec 2}
    (hu : IsEulerWeakSolutionWithDatum T v₀ u) {B : ℝ}
    (hB : ∀ᵐ z ∂(eulerMeasure T), vecNormSq (u z) ≤ B)
    {ζ : Vec 2 → Vec 2} (hζ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => ζ x i)) (hζp : IsTorusPeriodic ζ)
    (hζd : ∀ x, torusDiv ζ x = 0) {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) {b : ℝ} (hbT : b < T)
    (hθb : ∀ τ, b ≤ τ → θ τ = 0) :
    (∫ τ in Icc (0 : ℝ) T, (deriv θ τ * (∑ i, ∫ x in torusCube, u (x, τ) i * ζ x i) +
        θ τ * (∑ i, ∑ j, ∫ x in torusCube, (u (x, τ) i * u (x, τ) j) * gradMat ζ x i j))) +
      θ 0 * (∑ i, ∫ x in torusCube, v₀ x i * ζ x i) = 0 := by
  obtain ⟨⟨hmeas, _, _, _, _⟩, hv₀, _, hweak⟩ := hu
  set E := eulerMeasure T with hE
  have hsm : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec 2 × ℝ => timeSplitVec θ ζ z i) := fun i =>
    (isPeriodicSmooth_timeSplit hθ (hζ i) (hζp.comp (fun w => w i))).1
  have hps : IsPeriodicSmooth (timeSplitVec θ ζ) := by
    refine ⟨contDiff_pi.2 hsm, fun t => ?_⟩
    intro i x
    funext k
    simp only [timeSplitVec]
    rw [hζp i x]
  have hvan : VanishesNearTerminal T (timeSplitVec θ ζ) :=
    ⟨b, hbT, fun x t ht => by funext k; simp [timeSplitVec, hθb t ht]⟩
  have hdivφ : ∀ z, eulerDiv (timeSplitVec θ ζ) z = 0 := by
    intro z
    simp only [eulerDiv, Fin.sum_univ_two, eulerSpaceDeriv_timeSplitVec hθ hζ]
    have := hζd z.1
    simp only [torusDiv] at this
    simp only [gradMat]
    rw [← mul_add, this, mul_zero]
  have h := hweak _ hps hvan hdivφ
  have hcθ' : Continuous (deriv θ) := hθ.continuous_deriv (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have hint : ∀ i, Integrable (fun z => u z i) E := integrable_coord_of_bounded hmeas hB
  set P1 : Fin 2 → Vec 2 × ℝ → ℝ := fun i z => (deriv θ z.2 * ζ z.1 i) * u z i with hP1
  set P2 : Fin 2 → Fin 2 → Vec 2 × ℝ → ℝ :=
    fun i j z => (θ z.2 * gradMat ζ z.1 i j) * (u z i * u z j) with hP2
  have hint1 : ∀ i, Integrable (P1 i) E := fun i =>
    integrable_cont_mul_coord (hint i) ((hcθ'.comp continuous_snd).mul
      ((hζ i).continuous.comp continuous_fst))
  have hint2 : ∀ i j, Integrable (P2 i j) E := fun i j =>
    integrable_cont_mul_coord (integrable_coord_mul_coord hmeas hB i j)
      ((hθ.continuous.comp continuous_snd).mul ((continuous_gradMat_apply hζ i j).comp continuous_fst))
  have hpt : ∀ z, eulerWeakIntegrand u (timeSplitVec θ ζ) z =
      ∑ i, P1 i z + ∑ i, ∑ j, P2 i j z := by
    intro z
    simp only [eulerWeakIntegrand, vecDot, Fin.sum_univ_two, eulerTimeDeriv_timeSplitVec hθ hζ,
      eulerSpaceDeriv_timeSplitVec hθ hζ, hP1, hP2]
    ring
  have hdat : ∫ x in torusCube, vecDot (v₀ x) (timeSplitVec θ ζ (x, 0)) =
      θ 0 * ∑ i, ∫ x in torusCube, v₀ x i * ζ x i := by
    have e : ∀ x, vecDot (v₀ x) (timeSplitVec θ ζ (x, 0)) =
        θ 0 * ∑ i, v₀ x i * ζ x i := by
      intro x
      simp only [vecDot, Fin.sum_univ_two, timeSplitVec]
      ring
    simp_rw [e]
    rw [integral_const_mul, integral_finsetSum _ (fun i _ => integrable_datum_mul hv₀
      (hζ i).continuous i)]
  rw [hdat] at h
  simp_rw [hpt] at h
  have hI : ∫ z, (∑ i, P1 i z + ∑ i, ∑ j, P2 i j z) ∂E =
      (∑ i, ∫ z, P1 i z ∂E) + ∑ i, ∑ j, ∫ z, P2 i j z ∂E := by
    rw [integral_add (integrable_finsetSum _ fun i _ => hint1 i)
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint2 i j),
      integral_finsetSum _ (fun i _ => hint1 i)]
    congr 1
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hint2 i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => hint2 i j)]
  rw [hI] at h
  have hprod := eulerMeasure_eq_prod T
  have hs1 : ∀ i, ∫ z, P1 i z ∂E = ∫ τ in Icc (0 : ℝ) T,
      deriv θ τ * ∫ x in torusCube, u (x, τ) i * ζ x i := by
    intro i
    have hi : Integrable (P1 i) ((volume.restrict torusCube).prod (volume.restrict (Icc (0 : ℝ) T))) := by
      rw [← hprod]; exact hint1 i
    rw [hE, hprod, integral_prod_symm _ hi]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only [hP1]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  have hs2 : ∀ i j, ∫ z, P2 i j z ∂E = ∫ τ in Icc (0 : ℝ) T,
      θ τ * ∫ x in torusCube, (u (x, τ) i * u (x, τ) j) * gradMat ζ x i j := by
    intro i j
    have hi : Integrable (P2 i j) ((volume.restrict torusCube).prod (volume.restrict (Icc (0 : ℝ) T))) := by
      rw [← hprod]; exact hint2 i j
    rw [hE, hprod, integral_prod_symm _ hi]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only [hP2]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  have hc1 : ∀ i, Integrable (fun τ => deriv θ τ * ∫ x in torusCube, u (x, τ) i * ζ x i)
      (volume.restrict (Icc (0 : ℝ) T)) := by
    intro i
    have hi : Integrable (P1 i) ((volume.restrict torusCube).prod (volume.restrict (Icc (0 : ℝ) T))) := by
      rw [← hprod]; exact hint1 i
    have := hi.integral_prod_right
    refine this.congr (Filter.Eventually.of_forall fun τ => ?_)
    simp only [hP1]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  have hc2 : ∀ i j, Integrable (fun τ => θ τ * ∫ x in torusCube,
      (u (x, τ) i * u (x, τ) j) * gradMat ζ x i j) (volume.restrict (Icc (0 : ℝ) T)) := by
    intro i j
    have hi : Integrable (P2 i j) ((volume.restrict torusCube).prod (volume.restrict (Icc (0 : ℝ) T))) := by
      rw [← hprod]; exact hint2 i j
    have := hi.integral_prod_right
    refine this.congr (Filter.Eventually.of_forall fun τ => ?_)
    simp only [hP2]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  simp_rw [hs1, hs2] at h
  have e1 : ∫ τ in Icc (0 : ℝ) T, (deriv θ τ * (∑ i, ∫ x in torusCube, u (x, τ) i * ζ x i) +
        θ τ * (∑ i, ∑ j, ∫ x in torusCube, (u (x, τ) i * u (x, τ) j) * gradMat ζ x i j)) =
      (∑ i, ∫ τ in Icc (0 : ℝ) T, deriv θ τ * ∫ x in torusCube, u (x, τ) i * ζ x i) +
        ∑ i, ∑ j, ∫ τ in Icc (0 : ℝ) T, θ τ * ∫ x in torusCube,
          (u (x, τ) i * u (x, τ) j) * gradMat ζ x i j := by
    simp_rw [Finset.mul_sum]
    rw [integral_add (integrable_finsetSum _ fun i _ => hc1 i)
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hc2 i j),
      integral_finsetSum _ (fun i _ => hc1 i)]
    congr 1
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hc2 i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => hc2 i j)]
  rw [e1]
  exact h

theorem integrable_slice_pairing {T : ℝ} {u : Vec 2 × ℝ → Vec 2}
    (hmeas : AEStronglyMeasurable u (eulerMeasure T)) {B : ℝ}
    (hB : ∀ᵐ z ∂(eulerMeasure T), vecNormSq (u z) ≤ B) {ζ : Vec 2 → Vec 2}
    (hζ : ∀ i, Continuous (fun x => ζ x i)) :
    Integrable (fun τ => ∑ i, ∫ x in torusCube, u (x, τ) i * ζ x i)
      (volume.restrict (Icc (0 : ℝ) T)) := by
  have hint : ∀ i, Integrable (fun z => u z i) (eulerMeasure T) := integrable_coord_of_bounded hmeas hB
  have hprod := eulerMeasure_eq_prod T
  refine integrable_finsetSum _ fun i _ => ?_
  have h1 : Integrable (fun z : Vec 2 × ℝ => ζ z.1 i * u z i) (eulerMeasure T) :=
    integrable_cont_mul_coord (hint i) ((hζ i).comp continuous_fst)
  rw [hprod] at h1
  have := h1.integral_prod_right
  refine this.congr (Filter.Eventually.of_forall fun τ => ?_)
  simp only
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  ring

theorem integrable_slice_quad {T : ℝ} {u : Vec 2 × ℝ → Vec 2}
    (hmeas : AEStronglyMeasurable u (eulerMeasure T)) {B : ℝ}
    (hB : ∀ᵐ z ∂(eulerMeasure T), vecNormSq (u z) ≤ B) {G : Vec 2 → Fin 2 → Fin 2 → ℝ}
    (hG : ∀ i j, Continuous (fun x => G x i j)) :
    Integrable (fun τ => ∑ i, ∑ j, ∫ x in torusCube, (u (x, τ) i * u (x, τ) j) * G x i j)
      (volume.restrict (Icc (0 : ℝ) T)) := by
  have hprod := eulerMeasure_eq_prod T
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  have h1 : Integrable (fun z : Vec 2 × ℝ => G z.1 i j * (u z i * u z j)) (eulerMeasure T) :=
    integrable_cont_mul_coord (integrable_coord_mul_coord hmeas hB i j) ((hG i j).comp continuous_fst)
  rw [hprod] at h1
  have := h1.integral_prod_right
  refine this.congr (Filter.Eventually.of_forall fun τ => ?_)
  simp only
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  ring

end PDE
