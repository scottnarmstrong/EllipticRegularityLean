module

public import PDEFoundation.Euler.SliceDense

/-!
# Slice identities for divergence and curl

From the space-time weak formulations of `Defs.lean` to identities valid for a.e. `t` and all smooth periodic
test functions `φ` on the cube:
* `ae_slice_div`: `∫_cube v(x,t)·∇φ(x) dx = 0` from the divergence-free clause of `IsEulerWeakSolution`;
* `ae_slice_curl`: `∫_cube ω φ = ∫_cube (v₁ ∂₂φ - v₂ ∂₁φ)` from the last clause of `HasBoundedVorticity`.
These are exactly the hypotheses of `torusDiv_mollifyVec` and `torusCurl_mollifyVec`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

theorem integrable_of_ae_abs_le {T : ℝ} {f : Vec 2 × ℝ → ℝ} (hf : AEStronglyMeasurable f (eulerMeasure T))
    {B : ℝ} (hB : ∀ᵐ z ∂(eulerMeasure T), |f z| ≤ B) : Integrable f (eulerMeasure T) :=
  Integrable.of_bound hf B (hB.mono fun z hz => by simpa [Real.norm_eq_abs] using hz)

theorem abs_coord_le_sqrt {B : ℝ} {w : Vec 2} (hw : vecNormSq w ≤ B) (i : Fin 2) : |w i| ≤ Real.sqrt B := by
  have h1 : w i ^ 2 ≤ vecNormSq w := by
    simp only [vecNormSq, vecDot, Fin.sum_univ_two]
    fin_cases i <;> simp <;> nlinarith [mul_self_nonneg (w 0), mul_self_nonneg (w 1)]
  exact Real.abs_le_sqrt (h1.trans hw)

/-- Coordinates of an a.e.-bounded measurable field are integrable on `eulerMeasure T`. -/
theorem integrable_coord_of_bounded {T : ℝ} {v : Vec 2 × ℝ → Vec 2}
    (hv : AEStronglyMeasurable v (eulerMeasure T)) {B : ℝ}
    (hB : ∀ᵐ z ∂(eulerMeasure T), vecNormSq (v z) ≤ B) (i : Fin 2) :
    Integrable (fun z => v z i) (eulerMeasure T) :=
  integrable_of_ae_abs_le ((continuous_apply i).comp_aestronglyMeasurable hv)
    (hB.mono fun _ hz => abs_coord_le_sqrt hz i)

theorem integrable_mul_cont_ST {T : ℝ} {A : Vec 2 × ℝ → ℝ} (hA : Integrable A (eulerMeasure T))
    {g : Vec 2 × ℝ → ℝ} (hg : Continuous g) : Integrable (fun z => A z * g z) (eulerMeasure T) := by
  have hK : IsCompact (torusCube ×ˢ Icc (0 : ℝ) T) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine hA.mul_bdd (c := C) hg.aestronglyMeasurable ?_
  have : ∀ᵐ z ∂(eulerMeasure T), z ∈ torusCube ×ˢ Icc (0 : ℝ) T := by
    unfold eulerMeasure
    exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
  filter_upwards [this] with z hz
  exact hC z hz

theorem ae_slice_div {T : ℝ} (hT : 0 < T) {v : Vec 2 × ℝ → Vec 2}
    (hv : ∀ i, Integrable (fun z => v z i) (eulerMeasure T))
    (hdiv : ∀ ψ : Vec 2 × ℝ → ℝ, IsPeriodicSmooth ψ → VanishesOutsideInterior T ψ →
      ∫ z, vecDot (v z) (fun j => fderiv ℝ ψ z (basisVec j, 0)) ∂(eulerMeasure T) = 0) :
    ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      IsTorusPeriodic φ → ∫ x in torusCube, vecDot (v (x, t)) (fun j => pd j φ x) = 0 := by
  have h := ae_forall_sliceFunctional_eq_zero hT (A := fun _ => 0) (B₀ := fun z => v z 0)
    (B₁ := fun z => v z 1) (integrable_zero _ _ _) (hv 0) (hv 1) (by
      intro ψ hψ hvz
      refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)) (hdiv ψ hψ hvz)
      simp [vecDot, Fin.sum_univ_two])
  filter_upwards [h] with t ht φ hφ hp
  have := ht φ hφ hp
  unfold sliceFunctional at this
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)) this
  simp [vecDot, Fin.sum_univ_two, pd]

theorem ae_slice_curl {T : ℝ} (hT : 0 < T) {v : Vec 2 × ℝ → Vec 2} {ω : Vec 2 × ℝ → ℝ}
    (hv : ∀ i, Integrable (fun z => v z i) (eulerMeasure T)) (hω : Integrable ω (eulerMeasure T))
    (hcurl : ∀ ψ : Vec 2 × ℝ → ℝ, IsPeriodicSmooth ψ → VanishesOutsideInterior T ψ →
      ∫ z, ω z * ψ z ∂(eulerMeasure T) =
        ∫ z, (v z 0 * fderiv ℝ ψ z (basisVec 1, 0) - v z 1 * fderiv ℝ ψ z (basisVec 0, 0))
          ∂(eulerMeasure T)) :
    ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      IsTorusPeriodic φ → ∫ x in torusCube, ω (x, t) * φ x =
        ∫ x in torusCube, (v (x, t) 0 * pd 1 φ x - v (x, t) 1 * pd 0 φ x) := by
  have hweak : ∀ ψ : Vec 2 × ℝ → ℝ, IsPeriodicSmooth ψ → VanishesOutsideInterior T ψ →
      ∫ z, (ω z * ψ z + v z 1 * fderiv ℝ ψ z (basisVec 0, 0) + (-v z 0) * fderiv ℝ ψ z (basisVec 1, 0))
        ∂(eulerMeasure T) = 0 := by
    intro ψ hψ hvz
    have hd : ∀ j, Continuous fun z => fderiv ℝ ψ z (basisVec j, 0) := fun j =>
      (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    have i1 : Integrable (fun z => ω z * ψ z) (eulerMeasure T) := integrable_mul_cont_ST hω hψ.1.continuous
    have i2 : Integrable (fun z => v z 0 * fderiv ℝ ψ z (basisVec 1, 0)) (eulerMeasure T) :=
      integrable_mul_cont_ST (hv 0) (hd 1)
    have i3 : Integrable (fun z => v z 1 * fderiv ℝ ψ z (basisVec 0, 0)) (eulerMeasure T) :=
      integrable_mul_cont_ST (hv 1) (hd 0)
    have h1 := hcurl ψ hψ hvz
    have i23 : Integrable (fun z => v z 0 * fderiv ℝ ψ z (basisVec 1, 0) -
        v z 1 * fderiv ℝ ψ z (basisVec 0, 0)) (eulerMeasure T) := i2.sub i3
    calc ∫ z, (ω z * ψ z + v z 1 * fderiv ℝ ψ z (basisVec 0, 0) + (-v z 0) * fderiv ℝ ψ z (basisVec 1, 0))
          ∂(eulerMeasure T) = ∫ z, (ω z * ψ z - (v z 0 * fderiv ℝ ψ z (basisVec 1, 0) -
            v z 1 * fderiv ℝ ψ z (basisVec 0, 0))) ∂(eulerMeasure T) :=
          integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
      _ = (∫ z, ω z * ψ z ∂(eulerMeasure T)) - ∫ z, (v z 0 * fderiv ℝ ψ z (basisVec 1, 0) -
            v z 1 * fderiv ℝ ψ z (basisVec 0, 0)) ∂(eulerMeasure T) := integral_sub i1 i23
      _ = 0 := by rw [h1, sub_self]
  have h := ae_forall_sliceFunctional_eq_zero hT (A := ω) (B₀ := fun z => v z 1)
    (B₁ := fun z => - v z 0) hω (hv 1) (hv 0).neg hweak
  have prod_eq : eulerMeasure T = (volume.restrict torusCube).prod (volume.restrict (Icc (0 : ℝ) T)) :=
    eulerMeasure_eq_prod T
  have hωs := hω
  have hv0 := hv 0
  have hv1 := hv 1
  rw [prod_eq] at hωs hv0 hv1
  filter_upwards [h, hωs.prod_left_ae, hv0.prod_left_ae, hv1.prod_left_ae] with t ht i1 i2 i3 φ hφ hp
  have := ht φ hφ hp
  unfold sliceFunctional at this
  have hc0 : Continuous φ := hφ.continuous
  have hc1 : ∀ j, Continuous (pd j φ) := fun j => (contDiff_pd_top hφ j).continuous
  have e1 := integrable_mul_cont_cube i1 hc0
  have e2 := integrable_mul_cont_cube i3 (hc1 0)
  have e3 := integrable_mul_cont_cube i2 (hc1 1)
  have e23 : Integrable (fun x => v (x, t) 0 * pd 1 φ x - v (x, t) 1 * pd 0 φ x)
      (volume.restrict torusCube) := e3.sub e2
  have hsplit : ∫ x in torusCube, (ω (x, t) * φ x + v (x, t) 1 * pd 0 φ x + (-v (x, t) 0) * pd 1 φ x) =
      (∫ x in torusCube, ω (x, t) * φ x) -
        ∫ x in torusCube, (v (x, t) 0 * pd 1 φ x - v (x, t) 1 * pd 0 φ x) := by
    rw [← integral_sub e1 e23]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hsplit] at this
  exact sub_eq_zero.mp this

end PDE
