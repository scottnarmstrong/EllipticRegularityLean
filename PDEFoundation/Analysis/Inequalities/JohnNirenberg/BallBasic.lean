module

public import PDEFoundation.Analysis.Inequalities.JohnNirenberg.Cube
public import PDEFoundation.Measure.BoxCircumscribedBallVolume
public import PDEFoundation.Geometry.BoxCenterDisplacement
public import PDEFoundation.Geometry.BoxCircumscribedContainment

/-!
# Elementary ball facts for the John–Nirenberg inequality

The comparison of averages over nested balls (display (1.32) of Proposition 1.17) and Step 1 of its proof: the mean oscillation on every dyadic subcube of a
cube whose circumscribed closed ball lies in `B` is at most `2 ω M`, where
`ω = |B₁| (√d / 2) ^ d` is the ratio between the volume of the circumscribed ball and the cube.
-/

@[expose] public section

namespace PDE.JohnNirenberg

open BoxIntegral MeasureTheory Set Filter
open scoped ENNReal

variable {d : ℕ}

/-- The hypothesis of Proposition 1.17: `M` bounds the mean oscillation of `u` over
every ball whose closure lies in `U`. -/
def BMOBound (U : Set (Vec d)) (u : Vec d → ℝ) (M : ℝ) : Prop :=
  ∀ (y : Vec d) (r : ℝ), 0 < r → closure (euclideanBall y r) ⊆ U →
    integralAverage (euclideanBall y r) (fun z => |u z - integralAverage (euclideanBall y r) u|) ≤
      M

/-- The dimensional ratio `|B₁| (√d / 2) ^ d` between a circumscribed ball and its cube. -/
noncomputable def cubeBallRatio (d : ℕ) : ℝ :=
  (volume (euclideanBall (0 : Vec d) 1)).toReal * (Real.sqrt d / 2) ^ d

theorem cubeBallRatio_pos (hd : 0 < d) : 0 < cubeBallRatio d := by
  have h := volume_euclideanBall_toReal_pos (0 : Vec d) (R := 1) one_pos
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  unfold cubeBallRatio
  positivity

/-- Averages over a subset are controlled by the volume ratio. -/
theorem integralAverage_le_ratio_mul_of_ae_subset {E G : Set (Vec d)} {f : Vec d → ℝ}
    (hEG : E ≤ᵐ[volume] G) (hf : IntegrableOn f G volume) (hnn : ∀ x, 0 ≤ f x)
    (hEpos : 0 < volume E) (hGtop : volume G < ∞) :
    integralAverage E f ≤ (volume G).toReal / (volume E).toReal * integralAverage G f := by
  have hEG' : volume E ≤ volume G := measure_mono_ae hEG
  have hEtop : volume E < ∞ := hEG'.trans_lt hGtop
  have hE : 0 < (volume E).toReal := ENNReal.toReal_pos hEpos.ne' hEtop.ne
  have hG : 0 < (volume G).toReal :=
    ENNReal.toReal_pos (hEpos.trans_le hEG').ne' hGtop.ne
  have hint : ∫ x in E, f x ∂volume ≤ ∫ x in G, f x ∂volume :=
    setIntegral_mono_set hf (ae_of_all _ hnn) hEG
  unfold integralAverage
  rw [show (volume G).toReal / (volume E).toReal * ((volume G).toReal⁻¹ * ∫ x in G, f x) =
      (volume E).toReal⁻¹ * ∫ x in G, f x by field_simp]
  exact mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hE.le)

/-- Adding a constant shifts the average by that constant. -/
theorem integralAverage_add_const {U : Set (Vec d)} {g : Vec d → ℝ}
    (hg : IntegrableOn g U volume) (hUpos : 0 < volume U) (hUtop : volume U < ∞) (c : ℝ) :
    integralAverage U (fun x => g x + c) = integralAverage U g + c := by
  have hV : 0 < (volume U).toReal := ENNReal.toReal_pos hUpos.ne' hUtop.ne
  unfold integralAverage
  rw [integral_add hg (integrableOn_const hUtop.ne), setIntegral_const, smul_eq_mul,
    measureReal_def]
  field_simp

/-- The mean oscillation about the mean is at most twice the oscillation about any constant. -/
theorem integralAverage_abs_sub_integralAverage_le_two_mul {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : IntegrableOn f U volume) (hUpos : 0 < volume U) (hUtop : volume U < ∞) (a : ℝ) :
    integralAverage U (fun x => |f x - integralAverage U f|) ≤
      2 * integralAverage U (fun x => |f x - a|) := by
  have hV : 0 < (volume U).toReal := ENNReal.toReal_pos hUpos.ne' hUtop.ne
  have hfa : IntegrableOn (fun x => |f x - a|) U volume :=
    (hf.sub (integrableOn_const hUtop.ne)).abs
  have hfm : IntegrableOn (fun x => |f x - integralAverage U f|) U volume :=
    (hf.sub (integrableOn_const hUtop.ne)).abs
  have hmean := abs_integralAverage_sub_le_integralAverage_abs_sub a hf hUpos hUtop
  have hpt : ∀ x, |f x - integralAverage U f| ≤ |f x - a| + |integralAverage U f - a| := by
    intro x
    calc |f x - integralAverage U f| = |(f x - a) - (integralAverage U f - a)| := by ring_nf
      _ ≤ |f x - a| + |integralAverage U f - a| := abs_sub _ _
  have hmono : integralAverage U (fun x => |f x - integralAverage U f|) ≤
      integralAverage U (fun x => |f x - a| + |integralAverage U f - a|) := by
    unfold integralAverage
    exact mul_le_mul_of_nonneg_left
      (setIntegral_mono hfm (hfa.add (integrableOn_const hUtop.ne)) hpt) (inv_nonneg.mpr hV.le)
  rw [integralAverage_add_const hfa hUpos hUtop] at hmono
  linarith

/-- The closure of an open round ball lies in the closed round ball. -/
theorem closure_euclideanBall_subset (y : Vec d) (r : ℝ) :
    closure (euclideanBall y r) ⊆ euclideanClosedBall y r :=
  closure_minimal (euclideanBall_subset_euclideanClosedBall y r)
    (isClosed_euclideanClosedBall y r)

/-- A displaced closed ball stays inside a closed ball by the triangle inequality. -/
theorem euclideanClosedBall_subset_of_norm_add_le {c z : Vec d} {r R : ℝ} (hr : 0 ≤ r)
    (hbound : vecEuclideanNorm (z - c) + r ≤ R) :
    euclideanClosedBall z r ⊆ euclideanClosedBall c R := by
  intro x hx
  have hR : 0 ≤ R := le_trans (by linarith [vecEuclideanNorm_nonneg (z - c)]) hbound
  apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR).mpr
  have hxz := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr).mp hx
  calc
    vecEuclideanNorm (x - c) = vecEuclideanNorm ((x - z) + (z - c)) := by congr 1; abel
    _ ≤ vecEuclideanNorm (x - z) + vecEuclideanNorm (z - c) := vecEuclideanNorm_add_le _ _
    _ ≤ R := by linarith

section Ball

variable {U : Set (Vec d)} {u : Vec d → ℝ} {M : ℝ}

/-- Integrability on a set contained in a closed ball inside the domain. -/
theorem integrableOn_of_subset_euclideanClosedBall (hloc : LocallyIntegrableOn u U volume)
    {y : Vec d} {r : ℝ} (hr : 0 ≤ r) (hyU : euclideanClosedBall y r ⊆ U) {S : Set (Vec d)}
    (hS : S ⊆ euclideanClosedBall y r) : IntegrableOn u S volume :=
  (hloc.integrableOn_compact_subset hyU (isCompact_euclideanClosedBall y hr)).mono_set hS

/-- Display (1.32): for nested balls `E ⊆ G` with `closure G ⊆ U`,
`|(u)_E - (u)_G| ≤ (r / ρ) ^ d M`. -/
theorem abs_integralAverage_sub_le_of_ball_subset (hloc : LocallyIntegrableOn u U volume)
    (hM : BMOBound U u M) {z y : Vec d} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hEG : euclideanBall z ρ ⊆ euclideanBall y r) (hGU : euclideanClosedBall y r ⊆ U) :
    |integralAverage (euclideanBall z ρ) u - integralAverage (euclideanBall y r) u| ≤
      (r / ρ) ^ d * M := by
  set a := integralAverage (euclideanBall y r) u
  have hGint : IntegrableOn u (euclideanBall y r) volume :=
    integrableOn_of_subset_euclideanClosedBall hloc hr.le hGU
      (euclideanBall_subset_euclideanClosedBall y r)
  have hEint : IntegrableOn u (euclideanBall z ρ) volume := hGint.mono_set hEG
  have hEpos := volume_euclideanBall_pos z hρ
  have hEtop := (volume_euclideanBall_ne_top z hρ.le).lt_top
  have hGtop := (volume_euclideanBall_ne_top y hr.le).lt_top
  have h1 := abs_integralAverage_sub_le_integralAverage_abs_sub a hEint hEpos hEtop
  have h2 := integralAverage_le_ratio_mul_of_ae_subset (E := euclideanBall z ρ)
    (G := euclideanBall y r) (f := fun x => |u x - a|) hEG.eventuallyLE ((hGint.sub (integrableOn_const hGtop.ne)).abs) (fun x => abs_nonneg _)
    hEpos hGtop
  have h3 : integralAverage (euclideanBall y r) (fun x => |u x - a|) ≤ M :=
    hM y r hr ((closure_euclideanBall_subset y r).trans hGU)
  rw [volume_euclideanBall_toReal_div_eq_div_pow y z hρ hr] at h2
  have hpow : 0 ≤ (r / ρ) ^ d := by positivity
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ (r / ρ) ^ d * M := mul_le_mul_of_nonneg_left h3 hpow

/-- Step 1 for a single equal-side box `J` whose closed circumscribed ball lies in `U`:
integrability, comparison with the circumscribed ball, and the oscillation bound `2 ω M`. -/
theorem box_oscillation_bounds (hd : 0 < d) (hloc : LocallyIntegrableOn u U volume)
    (hM : BMOBound U u M) (J : Box (Fin d)) {ℓ : ℝ} (hwidth : ∀ i, J.upper i - J.lower i = ℓ)
    (hJU : euclideanClosedBall (boxCenter J) (Real.sqrt d * ℓ / 2) ⊆ U) :
    IntegrableOn u (J : Set (Vec d)) volume ∧
      |integralAverage (J : Set (Vec d)) u -
          integralAverage (euclideanBall (boxCenter J) (Real.sqrt d * ℓ / 2)) u| ≤
        cubeBallRatio d * M ∧
      integralAverage (J : Set (Vec d))
          (fun x => |u x - integralAverage (J : Set (Vec d)) u|) ≤ 2 * (cubeBallRatio d * M) := by
  set ρ := Real.sqrt d * ℓ / 2
  set G := euclideanBall (boxCenter J) ρ
  set a := integralAverage G u
  have hℓ : 0 < ℓ := by
    rw [← hwidth ⟨0, hd⟩]; exact sub_pos.mpr (J.lower_lt_upper _)
  have hρ : 0 < ρ := by
    have := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd : (0 : ℝ) < d); positivity
  have hJint : IntegrableOn u (J : Set (Vec d)) volume :=
    integrableOn_of_subset_euclideanClosedBall hloc hρ.le hJU
      (Box.coe_subset_euclideanClosedBall_boxCenter J ℓ hd hwidth)
  have hGint : IntegrableOn u G volume :=
    integrableOn_of_subset_euclideanClosedBall hloc hρ.le hJU
      (euclideanBall_subset_euclideanClosedBall _ _)
  have hGtop := (volume_euclideanBall_ne_top (boxCenter J) hρ.le).lt_top
  have hJpos : 0 < volume (J : Set (Vec d)) :=
    (ENNReal.toReal_pos_iff.mp (volume_box_toReal_pos J)).1
  have hJtop := J.measure_coe_lt_top volume
  have hJG : (J : Set (Vec d)) ≤ᵐ[volume] G :=
    (Box.coe_ae_eq_Ioo J).le.trans
      (Box.Ioo_subset_euclideanBall_boxCenter J ℓ hd hwidth).eventuallyLE
  have hosc : integralAverage (J : Set (Vec d)) (fun x => |u x - a|) ≤ cubeBallRatio d * M := by
    have h := integralAverage_le_ratio_mul_of_ae_subset (E := (J : Set (Vec d))) (G := G)
      (f := fun x => |u x - a|) hJG
      ((hGint.sub (integrableOn_const hGtop.ne)).abs) (fun x => abs_nonneg _) hJpos hGtop
    rw [volume_euclideanBall_boxCenter_div_box_of_commonWidth J ℓ hd hwidth] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (cubeBallRatio_pos hd).le)
    exact hM _ _ hρ ((closure_euclideanBall_subset _ _).trans hJU)
  refine ⟨hJint, ?_, ?_⟩
  · exact (abs_integralAverage_sub_le_integralAverage_abs_sub a hJint hJpos hJtop).trans hosc
  · exact (integralAverage_abs_sub_integralAverage_le_two_mul hJint hJpos hJtop a).trans
      (by linarith)

/-- Step 1: every dyadic subcube of an equal-side box `Q` whose closed circumscribed ball lies
in `U` has mean oscillation at most `2 ω M`. -/
theorem dyadicDescendant_oscillation_le (hd : 0 < d) (hloc : LocallyIntegrableOn u U volume)
    (hM : BMOBound U u M) (Q : Box (Fin d)) {ℓ : ℝ} (hwidth : ∀ i, Q.upper i - Q.lower i = ℓ)
    (hQU : euclideanClosedBall (boxCenter Q) (Real.sqrt d * ℓ / 2) ⊆ U)
    (p : List (Set (Fin d))) :
    integralAverage (dyadicDescendant Q p : Set (Vec d))
        (fun x => |u x - integralAverage (dyadicDescendant Q p : Set (Vec d)) u|) ≤
      2 * (cubeBallRatio d * M) := by
  set ℓp := ℓ / (2 : ℝ) ^ p.length
  have hwidth' := upper_sub_lower_dyadicDescendant_of_commonWidth Q ℓ hwidth p
  have hℓ : 0 < ℓ := by
    rw [← hwidth ⟨0, hd⟩]; exact sub_pos.mpr (Q.lower_lt_upper _)
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hsub : euclideanClosedBall (boxCenter (dyadicDescendant Q p)) (Real.sqrt d * ℓp / 2) ⊆
      euclideanClosedBall (boxCenter Q) (Real.sqrt d * ℓ / 2) := by
    apply euclideanClosedBall_subset_of_norm_add_le (by positivity)
    have hmove := vecEuclideanNorm_boxCenter_dyadicDescendant_sub_le Q ℓ hd hwidth p
    have : Real.sqrt d * (ℓ - ℓp) / 2 + Real.sqrt d * ℓp / 2 = Real.sqrt d * ℓ / 2 := by ring
    linarith
  exact (box_oscillation_bounds hd hloc hM (dyadicDescendant Q p) hwidth'
    (hsub.trans hQU)).2.2

/-- Step 1 conclusion (display (1.34)): Lemma 1.16 with `2 ω M` in place of
`N`. -/
theorem volume_lt_abs_sub_box_le (hd : 0 < d) (hloc : LocallyIntegrableOn u U volume)
    (hM : BMOBound U u M) (hMpos : 0 < M) (Q : Box (Fin d)) {ℓ : ℝ}
    (hwidth : ∀ i, Q.upper i - Q.lower i = ℓ)
    (hQU : euclideanClosedBall (boxCenter Q) (Real.sqrt d * ℓ / 2) ⊆ U) (t : ℝ) :
    (volume {x ∈ (Q : Set (Vec d)) | t < |u x - integralAverage (Q : Set (Vec d)) u|}).toReal ≤
      Real.exp 2 * Real.exp (-(t / ((2 : ℝ) ^ d * Real.exp 1 * (2 * (cubeBallRatio d * M))))) *
        (volume (Q : Set (Vec d))).toReal := by
  have hQint := (box_oscillation_bounds hd hloc hM Q hwidth hQU).1
  have hN : 0 < 2 * (cubeBallRatio d * M) := by
    have := cubeBallRatio_pos hd; positivity
  exact volume_lt_abs_sub_integralAverage_le hd Q hQint hN
    (dyadicDescendant_oscillation_le hd hloc hM Q hwidth hQU) t

end Ball

end PDE.JohnNirenberg
