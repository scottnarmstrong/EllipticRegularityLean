module

public import PDEFoundation.Euler.MollifyCommute

/-!
# Mollification commutes with the curl

If `ω` is the distributional curl of the periodic field `v` (against smooth periodic test functions on the
cube, with the sign convention of `HasBoundedVorticity`), then `curl (mollifyVec a v) = mollify a ω`
pointwise.  If moreover `|ω| ≤ M` a.e., then `|mollify a ω| ≤ M` everywhere.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

theorem torusCurl_mollifyVec {a : ℝ} (ha : 0 < a) {v : Vec 2 → Vec 2} (hup : IsTorusPeriodic v)
    (hloc : ∀ i, LocallyIntegrable (fun x => v x i) volume) {ω : Vec 2 → ℝ} (hωp : IsTorusPeriodic ω)
    (hωloc : LocallyIntegrable ω volume)
    (hcurl : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsTorusPeriodic ψ →
      ∫ x in torusCube, ω x * ψ x =
        ∫ x in torusCube, (v x 0 * pd 1 ψ x - v x 1 * pd 0 ψ x)) (x : Vec 2) :
    torusCurl (mollifyVec a v) x = mollify a ω x := by
  set w := mollifyVec a v with hw
  have hws : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => w x i) := contDiff_mollifyVec ha hloc
  have hwp : IsTorusPeriodic w := isTorusPeriodic_mollifyVec hup
  have hwpi : ∀ i, IsTorusPeriodic (fun x => w x i) := fun i => hwp.comp (fun u => u i)
  have hvp : ∀ i, IsTorusPeriodic (fun x => v x i) := fun i => hup.comp (fun u => u i)
  have hms : ContDiff ℝ (⊤ : ℕ∞) (mollify a ω) := mollify_contDiff ha hωloc
  have hmp : IsTorusPeriodic (mollify a ω) := mollify_periodic hωp
  set g : Vec 2 → ℝ := fun x => torusCurl w x - mollify a ω x with hg
  have hcs : ContDiff ℝ (⊤ : ℕ∞) (torusCurl w) :=
    ContDiff.sub (contDiff_pd_top (hws 1) 0) (contDiff_pd_top (hws 0) 1)
  have hgs : ContDiff ℝ (⊤ : ℕ∞) g := ContDiff.sub hcs hms
  have hgp : IsTorusPeriodic g :=
    (((hwpi 1).pd 0).sub ((hwpi 0).pd 1)).sub hmp
  have key : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsTorusPeriodic ψ →
      ∫ x in torusCube, g x * ψ x = 0 := by
    intro ψ hψ hψp
    have hcj : ∀ j, Continuous (pd j ψ) := fun j => (contDiff_pd_top hψ j).continuous
    have hpj : ∀ j, IsTorusPeriodic (pd j ψ) := fun j => hψp.pd j
    have hibp : ∀ j k, ∫ x in torusCube, pd j (fun y => w y k) x * ψ x =
        -∫ x in torusCube, w x k * pd j ψ x := fun j k =>
      torus_integral_by_parts ((hws k).of_le (by exact_mod_cast le_top))
        (hψ.of_le (by exact_mod_cast le_top)) (hwpi k) hψp j
    have hpair : ∀ j k, ∫ x in torusCube, w x k * pd j ψ x =
        ∫ t, molK a t * ∫ y in torusCube, v y k * pd j ψ (t + y) := fun j k =>
      integral_cube_mollify_mul ha (hvp k) (hloc k) (hcj j) (hpj j)
    have hint : ∀ j k, Integrable (fun t => molK a t * ∫ y in torusCube, v y k * pd j ψ (t + y)) :=
      fun j k => integrable_mollify_pairing ha (hvp k) (hloc k) (hcj j) (hpj j)
    have hJ : ∫ x in torusCube, mollify a ω x * ψ x =
        ∫ t, molK a t * ∫ y in torusCube, ω y * ψ (t + y) :=
      integral_cube_mollify_mul ha hωp hωloc hψ.continuous hψp
    have hzero : ∀ t, (∫ y in torusCube, ω y * ψ (t + y)) =
        (∫ y in torusCube, v y 0 * pd 1 ψ (t + y)) - ∫ y in torusCube, v y 1 * pd 0 ψ (t + y) := by
      intro t
      have hφ := hcurl (fun y => ψ (t + y)) (contDiff_translate hψ t) (by
        intro i y
        simp only
        rw [show t + (y + basisVec i) = (t + y) + basisVec i by abel, hψp i])
      have hc : ∀ j k, IntegrableOn (fun y => v y k * pd j ψ (t + y)) torusCube := fun j k =>
        integrableOn_cube_mul_continuous (hloc k) ((hcj j).comp (continuous_const.add continuous_id))
      rw [hφ, ← integral_sub (hc 1 0) (hc 0 1)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [pd_comp_add_left]
    have hsplit : ∫ x in torusCube, g x * ψ x =
        ((∫ x in torusCube, pd 0 (fun y => w y 1) x * ψ x) -
          ∫ x in torusCube, pd 1 (fun y => w y 0) x * ψ x) -
          ∫ x in torusCube, mollify a ω x * ψ x := by
      have c1 : IntegrableOn (fun x => pd 0 (fun y => w y 1) x * ψ x) torusCube :=
        ((contDiff_pd_top (hws 1) 0).continuous.mul hψ.continuous).continuousOn.integrableOn_Icc
      have c2 : IntegrableOn (fun x => pd 1 (fun y => w y 0) x * ψ x) torusCube :=
        ((contDiff_pd_top (hws 0) 1).continuous.mul hψ.continuous).continuousOn.integrableOn_Icc
      have c3 : IntegrableOn (fun x => mollify a ω x * ψ x) torusCube :=
        (hms.continuous.mul hψ.continuous).continuousOn.integrableOn_Icc
      have c12 : IntegrableOn (fun x => pd 0 (fun y => w y 1) x * ψ x -
          pd 1 (fun y => w y 0) x * ψ x) torusCube := c1.sub c2
      rw [← integral_sub c1 c2, ← integral_sub c12 c3]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hg, torusCurl]; ring
    rw [hsplit, hibp 0 1, hibp 1 0, hJ, hpair 0 1, hpair 1 0]
    have : ∀ t, molK a t * ∫ y in torusCube, ω y * ψ (t + y) =
        molK a t * (∫ y in torusCube, v y 0 * pd 1 ψ (t + y)) -
          molK a t * ∫ y in torusCube, v y 1 * pd 0 ψ (t + y) := fun t => by
      rw [hzero t, mul_sub]
    simp only [neg_sub_neg]
    rw [← integral_sub (hint 1 0) (hint 0 1)]
    rw [sub_eq_zero]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    exact (this t).symm
  have hz := eq_zero_of_periodic_orthogonal hgs.continuous hgp (key _ hgs hgp)
  have := hz x
  simp only [hg] at this
  linarith

/-- The mollified vorticity inherits the pointwise bound. -/
theorem abs_mollify_vorticity_le {a : ℝ} (ha : 0 < a) {ω : Vec 2 → ℝ}
    (hωloc : LocallyIntegrable ω volume) {M : ℝ} (hM : ∀ᵐ y, |ω y| ≤ M) (x : Vec 2) :
    |mollify a ω x| ≤ M :=
  abs_mollify_le ha hωloc hM x

end PDE
