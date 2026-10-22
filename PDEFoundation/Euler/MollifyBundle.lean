module

public import PDEFoundation.Euler.SliceCor
public import PDEFoundation.Euler.MollifyCurl
public import PDEFoundation.Euler.MollifyL2ST
public import PDEFoundation.Euler.PeriodExt

/-!
# Mollified slices of a weak solution: bundled consequences

For a space-time field `v` measurable on `eulerMeasure T`, periodic in `x` for every `t`, a.e. bounded, and
distributionally divergence free in space-time (the clause of `IsEulerWeakSolution`), for a.e. `t` and every
mollification scale `a > 0`, the slice mollification `mollifyVec a (v(·,t))` is smooth, periodic,
pointwise divergence free and bounded by the `L^∞` bound of `v`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

theorem ae_mollify_slice_div {T : ℝ} (hT : 0 < T) {v : Vec 2 × ℝ → Vec 2}
    (hmeas : AEStronglyMeasurable v (eulerMeasure T))
    (hper : ∀ t, IsTorusPeriodic (fun x => v (x, t))) {B : ℝ}
    (hB : ∀ᵐ z ∂(eulerMeasure T), vecNormSq (v z) ≤ B)
    (hdiv : ∀ ψ : Vec 2 × ℝ → ℝ, IsPeriodicSmooth ψ → VanishesOutsideInterior T ψ →
      ∫ z, vecDot (v z) (fun j => fderiv ℝ ψ z (basisVec j, 0)) ∂(eulerMeasure T) = 0) :
    ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ a : ℝ, 0 < a →
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => mollifyVec a (fun y => v (y, t)) x i)) ∧
      IsTorusPeriodic (mollifyVec a (fun y => v (y, t))) ∧
      (∀ x, torusDiv (mollifyVec a (fun y => v (y, t))) x = 0) ∧
      (∀ x i, |mollifyVec a (fun y => v (y, t)) x i| ≤ Real.sqrt B) := by
  have hint : ∀ i, Integrable (fun z => v z i) (eulerMeasure T) :=
    integrable_coord_of_bounded hmeas hB
  have prod_eq : eulerMeasure T = (volume.restrict torusCube).prod (volume.restrict (Icc (0 : ℝ) T)) :=
    eulerMeasure_eq_prod T
  have hbt : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ᵐ x ∂(volume.restrict torusCube),
      vecNormSq (v (x, t)) ≤ B := by
    rw [prod_eq] at hB
    have h1 := (Measure.measurePreserving_swap (μ := volume.restrict (Icc (0 : ℝ) T))
      (ν := volume.restrict torusCube)).quasiMeasurePreserving.ae hB
    exact Measure.ae_ae_of_ae_prod h1
  have hint0 := hint 0
  have hint1 := hint 1
  rw [prod_eq] at hint0 hint1
  filter_upwards [ae_slice_div hT hint hdiv, hint0.prod_left_ae, hint1.prod_left_ae, hbt]
    with t hd i0 i1 hb a ha
  have hloc : ∀ i, LocallyIntegrable (fun x => v (x, t) i) volume := by
    intro i
    have hi : Integrable (fun x => v (x, t) i) (volume.restrict torusCube) := by fin_cases i <;> assumption
    exact IsTorusPeriodic.locallyIntegrable ((hper t).comp (fun w => w i)) hi
  have hbvol : ∀ᵐ y ∂(volume : Measure (Vec 2)), vecNormSq (v (y, t)) ≤ B :=
    (hper t).ae_of_ae_cube (P := fun w => vecNormSq w ≤ B) hb
  refine ⟨contDiff_mollifyVec ha hloc, isTorusPeriodic_mollifyVec (hper t),
    torusDiv_mollifyVec ha (hper t) hloc (fun ψ hψ hψp => ?_), fun x i => ?_⟩
  · exact hd ψ hψ hψp
  · exact abs_mollifyVec_le ha hloc (B := Real.sqrt B)
      (hbvol.mono fun y hy i => abs_coord_le_sqrt hy i) x i

/-- Mollified vorticity slices: `curl (mollifyVec a v(·,t)) = mollify a ω̃(·,t)` and `|mollify a ω̃| ≤ M`,
where `ω̃(·,t)` is the periodic extension of `ω(·,t)`. -/
theorem ae_mollify_slice_curl {T : ℝ} (hT : 0 < T) {v : Vec 2 × ℝ → Vec 2} {ω : Vec 2 × ℝ → ℝ}
    (hmeas : AEStronglyMeasurable v (eulerMeasure T))
    (hper : ∀ t, IsTorusPeriodic (fun x => v (x, t))) {B : ℝ}
    (hB : ∀ᵐ z ∂(eulerMeasure T), vecNormSq (v z) ≤ B)
    (hωm : AEStronglyMeasurable ω (eulerMeasure T)) {M : ℝ} (hωM : ∀ᵐ z ∂(eulerMeasure T), |ω z| ≤ M)
    (hcurl : ∀ ψ : Vec 2 × ℝ → ℝ, IsPeriodicSmooth ψ → VanishesOutsideInterior T ψ →
      ∫ z, ω z * ψ z ∂(eulerMeasure T) =
        ∫ z, (v z 0 * fderiv ℝ ψ z (basisVec 1, 0) - v z 1 * fderiv ℝ ψ z (basisVec 0, 0))
          ∂(eulerMeasure T)) :
    ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ a : ℝ, 0 < a →
      (∀ x, torusCurl (mollifyVec a (fun y => v (y, t))) x =
        mollify a (periodExt (fun y => ω (y, t))) x) ∧
      (∀ x, |mollify a (periodExt (fun y => ω (y, t))) x| ≤ M) := by
  have hint : ∀ i, Integrable (fun z => v z i) (eulerMeasure T) :=
    integrable_coord_of_bounded hmeas hB
  have hωint : Integrable ω (eulerMeasure T) := integrable_of_ae_abs_le hωm hωM
  have prod_eq : eulerMeasure T = (volume.restrict torusCube).prod (volume.restrict (Icc (0 : ℝ) T)) :=
    eulerMeasure_eq_prod T
  have hωbt : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ᵐ x ∂(volume.restrict torusCube), |ω (x, t)| ≤ M := by
    rw [prod_eq] at hωM
    have h1 := (Measure.measurePreserving_swap (μ := volume.restrict (Icc (0 : ℝ) T))
      (ν := volume.restrict torusCube)).quasiMeasurePreserving.ae hωM
    exact Measure.ae_ae_of_ae_prod h1
  have hint0 := hint 0
  have hint1 := hint 1
  have hωint' := hωint
  rw [prod_eq] at hint0 hint1 hωint'
  filter_upwards [ae_slice_curl hT hint hωint hcurl, hint0.prod_left_ae, hint1.prod_left_ae,
    hωint'.prod_left_ae, hωbt] with t hc i0 i1 iω hb a ha
  have hloc : ∀ i, LocallyIntegrable (fun x => v (x, t) i) volume := by
    intro i
    have hi : Integrable (fun x => v (x, t) i) (volume.restrict torusCube) := by fin_cases i <;> assumption
    exact IsTorusPeriodic.locallyIntegrable ((hper t).comp (fun w => w i)) hi
  have hωp : IsTorusPeriodic (periodExt (fun y => ω (y, t))) := isTorusPeriodic_periodExt _
  have hωae := ae_periodExt_eq (fun y => ω (y, t))
  have hωi : Integrable (periodExt (fun y => ω (y, t))) (volume.restrict torusCube) :=
    iω.congr (hωae.mono fun x hx => hx.symm)
  have hωloc : LocallyIntegrable (periodExt (fun y => ω (y, t))) volume :=
    IsTorusPeriodic.locallyIntegrable hωp hωi
  have hbvol : ∀ᵐ y ∂(volume : Measure (Vec 2)), |periodExt (fun y => ω (y, t)) y| ≤ M := by
    refine hωp.ae_of_ae_cube (P := fun r => |r| ≤ M) ?_
    filter_upwards [hb, hωae] with x hx hxe
    rw [hxe]; exact hx
  refine ⟨fun x => ?_, fun x => abs_mollify_le ha hωloc hbvol x⟩
  refine torusCurl_mollifyVec ha (hper t) hloc hωp hωloc (fun ψ hψ hψp => ?_) x
  rw [← hc ψ hψ hψp]
  exact integral_congr_ae (hωae.mono fun x hx => by simp only [hx])

end PDE
