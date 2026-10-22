module

public import PDEFoundation.Euler.MollifyPairing
public import PDEFoundation.Euler.PeriodicCZWeak

/-!
# Mollification commutes with divergence and curl

For a periodic field `v` with locally integrable coordinates, `mollifyVec a v = (molK a ⋆ vᵢ)ᵢ` is smooth
and periodic.  If `v` is distributionally divergence free (tested against smooth periodic functions on the
cube), then `div (mollifyVec a v) = 0` pointwise; if `ω` is the distributional curl of `v`, then
`curl (mollifyVec a v) = mollify a ω` pointwise.  Proof: pair with smooth periodic `ψ` using
`mollify_pairing` and the torus integration by parts, then use `eq_zero_of_periodic_orthogonal`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

/-- Coordinatewise spatial mollification of a planar field. -/
noncomputable def mollifyVec (a : ℝ) (v : Vec 2 → Vec 2) : Vec 2 → Vec 2 :=
  fun x i => mollify a (fun y => v y i) x

theorem mollifyVec_apply (a : ℝ) (v : Vec 2 → Vec 2) (x : Vec 2) (i : Fin 2) :
    mollifyVec a v x i = mollify a (fun y => v y i) x := rfl

/-- A continuous periodic function orthogonal to itself on the cube vanishes. -/
theorem eq_zero_of_periodic_orthogonal {g : Vec 2 → ℝ} (hg : Continuous g) (hp : IsTorusPeriodic g)
    (h : ∫ x in torusCube, g x * g x = 0) : ∀ x, g x = 0 := by
  have hz : ∀ z ∈ torusCube, g z = 0 := by
    intro z hz
    have h9 := setIntegral_ball_comp_add_le (f := fun x => g x * g x) (hg.mul hg) (hp.mul hp)
      (fun x => mul_self_nonneg _) hz
    rw [h, mul_zero] at h9
    have hcont : Continuous fun x => g (z + x) * g (z + x) :=
      (hg.comp (continuous_const.add continuous_id)).mul (hg.comp (continuous_const.add continuous_id))
    have hB : euclideanBall (0 : Vec 2) 1 ⊆ Icc (-1 : Vec 2) 1 := by
      intro x hx
      have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt one_pos).1 hx
      rw [sub_zero] at hx'
      constructor <;> intro i <;> simp <;> linarith [(abs_le.mp (abs_apply_le_vecEuclideanNorm x i))]
    have hint : IntegrableOn (fun x => g (z + x) * g (z + x)) (euclideanBall (0 : Vec 2) 1) :=
      (hcont.continuousOn.integrableOn_Icc (a := (-1 : Vec 2)) (b := 1)).mono_set hB
    have hnn : ∫ x in euclideanBall (0 : Vec 2) 1, g (z + x) * g (z + x) = 0 :=
      le_antisymm h9 (setIntegral_nonneg (isOpen_euclideanBall _ _).measurableSet
        fun x _ => mul_self_nonneg _)
    have hae := (setIntegral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => mul_self_nonneg _) hint).1 hnn
    have heq := Measure.eqOn_open_of_ae_eq hae (isOpen_euclideanBall (0 : Vec 2) 1)
      hcont.continuousOn continuousOn_const
    have h0 : (0 : Vec 2) ∈ euclideanBall (0 : Vec 2) 1 := by
      rw [mem_euclideanBall_iff_vecEuclideanNorm_lt one_pos]
      simp [vecEuclideanNorm, vecNormSq, vecDot]
    have := heq h0
    simp only [add_zero, Pi.zero_apply] at this
    exact mul_self_eq_zero.mp this
  intro x
  have hmem : x - latVec (fun i => ⌊x i⌋) ∈ torusCube := by
    constructor <;> intro i <;> simp only [Pi.sub_apply, latVec_apply, Pi.zero_apply, Pi.one_apply]
    · linarith [Int.floor_le (x i)]
    · linarith [Int.lt_floor_add_one (x i)]
  rw [← hp.sub_latVec (fun i => ⌊x i⌋) x]
  exact hz _ hmem

section
variable {a : ℝ} {v : Vec 2 → Vec 2}

theorem contDiff_mollifyVec (ha : 0 < a) (hloc : ∀ i, LocallyIntegrable (fun x => v x i) volume) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => mollifyVec a v x i) :=
  mollify_contDiff ha (hloc i)

theorem isTorusPeriodic_mollifyVec (hup : IsTorusPeriodic v) : IsTorusPeriodic (mollifyVec a v) := by
  intro k x
  funext i
  exact mollify_periodic (hup.comp (fun u => u i)) k x

theorem abs_mollifyVec_le (ha : 0 < a) (hloc : ∀ i, LocallyIntegrable (fun x => v x i) volume) {B : ℝ}
    (hB : ∀ᵐ y, ∀ i, |v y i| ≤ B) (x : Vec 2) (i : Fin 2) : |mollifyVec a v x i| ≤ B :=
  abs_mollify_le ha (hloc i) (hB.mono fun _ hy => hy i) x

end

/-- Pairing of a mollified coordinate with a smooth periodic function, in the form used below. -/
theorem integrableOn_cube_mul_continuous {f g : Vec 2 → ℝ} (hf : LocallyIntegrable f volume)
    (hg : Continuous g) : IntegrableOn (fun x => f x * g x) torusCube :=
  (hf.integrableOn_isCompact (isCompact_Icc : IsCompact torusCube)).mul_continuousOn hg.continuousOn
    isCompact_Icc

theorem torusDiv_mollifyVec {a : ℝ} (ha : 0 < a) {v : Vec 2 → Vec 2} (hup : IsTorusPeriodic v)
    (hloc : ∀ i, LocallyIntegrable (fun x => v x i) volume)
    (hdiv : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsTorusPeriodic ψ →
      ∫ x in torusCube, vecDot (v x) (fun j => pd j ψ x) = 0) (x : Vec 2) :
    torusDiv (mollifyVec a v) x = 0 := by
  set w := mollifyVec a v with hw
  have hws : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => w x i) := contDiff_mollifyVec ha hloc
  have hwp : IsTorusPeriodic w := isTorusPeriodic_mollifyVec hup
  have hwpi : ∀ i, IsTorusPeriodic (fun x => w x i) := fun i => hwp.comp (fun u => u i)
  have hvp : ∀ i, IsTorusPeriodic (fun x => v x i) := fun i => hup.comp (fun u => u i)
  have hgs : ContDiff ℝ (⊤ : ℕ∞) (torusDiv w) :=
    ContDiff.add (contDiff_pd_top (hws 0) 0) (contDiff_pd_top (hws 1) 1)
  have hgp : IsTorusPeriodic (torusDiv w) :=
    ((hwpi 0).pd 0).add ((hwpi 1).pd 1)
  have key : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsTorusPeriodic ψ →
      ∫ x in torusCube, torusDiv w x * ψ x = 0 := by
    intro ψ hψ hψp
    have hcj : ∀ j, Continuous (pd j ψ) := fun j => (contDiff_pd_top hψ j).continuous
    have hpj : ∀ j, IsTorusPeriodic (pd j ψ) := fun j => hψp.pd j
    have hibp : ∀ j, ∫ x in torusCube, pd j (fun y => w y j) x * ψ x =
        -∫ x in torusCube, w x j * pd j ψ x := fun j =>
      torus_integral_by_parts ((hws j).of_le (by exact_mod_cast le_top)) (hψ.of_le (by exact_mod_cast le_top))
        (hwpi j) hψp j
    have hpair : ∀ j, ∫ x in torusCube, w x j * pd j ψ x =
        ∫ t, molK a t * ∫ y in torusCube, v y j * pd j ψ (t + y) := fun j =>
      integral_cube_mollify_mul ha (hvp j) (hloc j) (hcj j) (hpj j)
    have hint : ∀ j, Integrable (fun t => molK a t * ∫ y in torusCube, v y j * pd j ψ (t + y)) :=
      fun j => integrable_mollify_pairing ha (hvp j) (hloc j) (hcj j) (hpj j)
    have hzero : ∀ t, (∫ y in torusCube, v y 0 * pd 0 ψ (t + y)) +
        ∫ y in torusCube, v y 1 * pd 1 ψ (t + y) = 0 := by
      intro t
      have hφ := hdiv (fun y => ψ (t + y)) (contDiff_translate hψ t) (by
        intro i y
        simp only
        rw [show t + (y + basisVec i) = (t + y) + basisVec i by abel, hψp i])
      have hc : ∀ j, IntegrableOn (fun y => v y j * pd j ψ (t + y)) torusCube := fun j =>
        integrableOn_cube_mul_continuous (hloc j) ((hcj j).comp (continuous_const.add continuous_id))
      rw [← integral_add (hc 0) (hc 1)]
      rw [← hφ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [vecDot, Fin.sum_univ_two, pd_comp_add_left]
    have hsplit : ∫ x in torusCube, torusDiv w x * ψ x =
        (∫ x in torusCube, pd 0 (fun y => w y 0) x * ψ x) +
          ∫ x in torusCube, pd 1 (fun y => w y 1) x * ψ x := by
      rw [← integral_add]
      · refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [torusDiv]; ring
      · exact (((contDiff_pd_top (hws 0) 0).continuous.mul hψ.continuous).continuousOn).integrableOn_Icc
      · exact (((contDiff_pd_top (hws 1) 1).continuous.mul hψ.continuous).continuousOn).integrableOn_Icc
    rw [hsplit, hibp 0, hibp 1, hpair 0, hpair 1, ← neg_add, ← integral_add (hint 0) (hint 1)]
    simp only [← mul_add, hzero, mul_zero, integral_zero, neg_zero]
  have hz := eq_zero_of_periodic_orthogonal hgs.continuous hgp (key _ hgs hgp)
  exact hz x

end PDE
