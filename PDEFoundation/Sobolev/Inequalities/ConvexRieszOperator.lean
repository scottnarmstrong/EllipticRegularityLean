module

public import PDEFoundation.Sobolev.Inequalities.ConvexRieszSmooth

/-!
# The Riesz potential as an operator on `L¹` of a convex domain

The `ℝ≥0∞`-valued Riesz potential `x ↦ ∫_V |x - y| ^ (1 - d) h y dy` of a weight on a bounded open
convex domain `V` of Euclidean diameter at most `D`. It is additive and, by Tonelli, bounded on
`L¹(V)` with the finite constant `∫_{B_{D+1}} |z| ^ (1 - d) dz`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE

variable {d : ℕ}

/-- The `ℝ≥0∞`-valued Riesz potential `x ↦ ∫_V |x - y| ^ (1 - d) h y dy` of a weight on `V`. -/
noncomputable def lintegralRieszOn (V : Set (Vec d)) (h : Vec d → ℝ≥0∞) (x : Vec d) : ℝ≥0∞ :=
  ∫⁻ y in V, ENNReal.ofReal (vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d)) * h y

theorem measurable_rieszKernelPair (d : ℕ) :
    Measurable fun q : Vec d × Vec d =>
      ENNReal.ofReal (vecEuclideanNorm (q.1 - q.2) ^ ((1 : ℝ) - d)) :=
  ENNReal.measurable_ofReal.comp
    ((continuous_vecEuclideanNorm.comp (continuous_fst.sub continuous_snd)).measurable.pow_const _)

private theorem measurable_lintegralRieszOn_aux (V : Set (Vec d)) {h : Vec d → ℝ≥0∞}
    (hh : Measurable h) :
    Measurable (lintegralRieszOn V h) := by
  unfold lintegralRieszOn
  exact Measurable.lintegral_prod_right'
    (f := fun q : Vec d × Vec d =>
      ENNReal.ofReal (vecEuclideanNorm (q.1 - q.2) ^ ((1 : ℝ) - d)) * h q.2)
    ((measurable_rieszKernelPair d).mul (hh.comp measurable_snd))

private theorem lintegralRieszOn_add_aux {V : Set (Vec d)} {h₁ h₂ : Vec d → ℝ≥0∞}
    (h₁m : Measurable h₁) (x : Vec d) :
    lintegralRieszOn V (fun y => h₁ y + h₂ y) x = lintegralRieszOn V h₁ x +
      lintegralRieszOn V h₂ x := by
  unfold lintegralRieszOn
  simp only [mul_add]
  rw [lintegral_add_left]
  exact (ENNReal.measurable_ofReal.comp
    ((continuous_vecEuclideanNorm.comp
      (continuous_const.sub continuous_id)).measurable.pow_const _)).mul h₁m

/-- The Riesz potential is bounded on `L¹(V)` for a bounded convex domain of diameter at
most `D`, with the explicit finite constant `∫_{B_{D+1}} |z| ^ (1 - d)`. -/
private theorem lintegral_lintegralRieszOn_le_aux {V : Set (Vec d)} {D : ℝ}
    (hV : IsOpenBoundedConvexDomain V) (hVD : HasEuclideanDiameterLE V D) (hD : 0 ≤ D)
    {h : Vec d → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ x in V, lintegralRieszOn V h x ≤
      (∫⁻ z in euclideanBall (0 : Vec d) (D + 1),
          ENNReal.ofReal (vecEuclideanNorm z ^ ((1 : ℝ) - d))) * ∫⁻ y in V, h y := by
  unfold lintegralRieszOn
  rw [lintegral_lintegral_swap]
  swap
  · exact (((measurable_rieszKernelPair d).mul (hh.comp measurable_snd))).aemeasurable
  calc _ ≤ ∫⁻ y in V, (∫⁻ z in euclideanBall (0 : Vec d) (D + 1),
          ENNReal.ofReal (vecEuclideanNorm z ^ ((1 : ℝ) - d))) * h y := by
        refine setLIntegral_mono' hV.measurableSet fun y hy => ?_
        have hk : Measurable fun x : Vec d =>
            ENNReal.ofReal (vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d)) :=
          ENNReal.measurable_ofReal.comp
            ((continuous_vecEuclideanNorm.comp
              (continuous_id.sub continuous_const)).measurable.pow_const _)
        rw [lintegral_mul_const _ hk]
        refine mul_le_mul' ?_ le_rfl
        have hsub : V ⊆ {x | vecEuclideanNorm (y - x) < D + 1} := by
          intro x hx
          have := hVD hy hx
          show vecEuclideanNorm (y - x) < D + 1
          linarith
        rw [← lintegral_riesz_kernel_ball y (by linarith)]
        calc _ = ∫⁻ x in V, ENNReal.ofReal (vecEuclideanNorm (y - x) ^ ((1 : ℝ) - d)) := by
              refine lintegral_congr fun x => ?_
              rw [vecEuclideanNorm_sub_comm]
          _ ≤ _ := lintegral_mono_set hsub
    _ = _ := lintegral_const_mul _ hh

theorem lintegralRieszOn_congr_ae {V : Set (Vec d)} {h h' : Vec d → ℝ≥0∞}
    (hh : h =ᵐ[volume.restrict V] h') (x : Vec d) :
    lintegralRieszOn V h x = lintegralRieszOn V h' x := by
  unfold lintegralRieszOn
  refine lintegral_congr_ae ?_
  filter_upwards [hh] with y hy
  rw [hy]

theorem measurable_lintegralRieszOn (V : Set (Vec d)) {h : Vec d → ℝ≥0∞}
    (hh : AEMeasurable h (volume.restrict V)) : Measurable (lintegralRieszOn V h) := by
  have : lintegralRieszOn V h = lintegralRieszOn V (hh.mk h) :=
    funext (lintegralRieszOn_congr_ae hh.ae_eq_mk)
  rw [this]
  exact measurable_lintegralRieszOn_aux V hh.measurable_mk

theorem lintegralRieszOn_add {V : Set (Vec d)} {h₁ h₂ : Vec d → ℝ≥0∞}
    (h₁m : AEMeasurable h₁ (volume.restrict V)) (x : Vec d) :
    lintegralRieszOn V (fun y => h₁ y + h₂ y) x = lintegralRieszOn V h₁ x +
      lintegralRieszOn V h₂ x := by
  rw [lintegralRieszOn_congr_ae (h' := fun y => h₁m.mk h₁ y + h₂ y)
    (by filter_upwards [h₁m.ae_eq_mk] with y hy; rw [hy]),
    lintegralRieszOn_add_aux h₁m.measurable_mk, lintegralRieszOn_congr_ae h₁m.ae_eq_mk]

/-- The Riesz potential is bounded on `L¹(V)` for a bounded convex domain of diameter at
most `D`, with the explicit finite constant `∫_{B_{D+1}} |z| ^ (1 - d)`. -/
theorem lintegral_lintegralRieszOn_le {V : Set (Vec d)} {D : ℝ}
    (hV : IsOpenBoundedConvexDomain V) (hVD : HasEuclideanDiameterLE V D) (hD : 0 ≤ D)
    {h : Vec d → ℝ≥0∞} (hh : AEMeasurable h (volume.restrict V)) :
    ∫⁻ x in V, lintegralRieszOn V h x ≤
      (∫⁻ z in euclideanBall (0 : Vec d) (D + 1),
          ENNReal.ofReal (vecEuclideanNorm z ^ ((1 : ℝ) - d))) * ∫⁻ y in V, h y := by
  have h1 : lintegralRieszOn V h = lintegralRieszOn V (hh.mk h) :=
    funext (lintegralRieszOn_congr_ae hh.ae_eq_mk)
  rw [h1, lintegral_congr_ae hh.ae_eq_mk]
  exact lintegral_lintegralRieszOn_le_aux hV hVD hD hh.measurable_mk

/-- The constant in the boundedness of the Riesz potential is finite. -/
theorem lintegral_riesz_kernel_euclideanBall_lt_top (hd : 0 < d) {R : ℝ} (hR : 0 < R) :
    ∫⁻ z in euclideanBall (0 : Vec d) R, ENNReal.ofReal (vecEuclideanNorm z ^ ((1 : ℝ) - d)) <
      ∞ := by
  have h := (integrableOn_vecEuclideanNorm_rpow_euclideanBall_iff hd (s := (1 : ℝ) - d) hR).2
    (by linarith)
  exact Integrable.lintegral_lt_top h

end PDE
