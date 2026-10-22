module

public import EllipticRegularity.Guerra.Scalar.Identities

/-!
# Guerra sharpness: the homogeneous function `u`

`uProf i γ α x = |x|^α tanh(γ x_i/|x|)/tanh γ` (`u(0) = 0`), for a coordinate index `i`
(the statement uses `i = ⟨d-1, _⟩`). Pointwise bounds, ray values and continuity.
-/

@[expose] public section

namespace PDE.Guerra

open Real PDE

/-- The function `u(x) = |x|^α tanh(γ x_i/|x|)/tanh γ`, `u(0)=0`; definitionally the `u` of the
statement when `i = ⟨d-1, _⟩`. -/
noncomputable def uProf {d : ℕ} (i : Fin d) (γ α : ℝ) (x : Vec d) : ℝ :=
  if x = 0 then 0 else
    vecEuclideanNorm x ^ α * (Real.tanh (γ * x i / vecEuclideanNorm x) / Real.tanh γ)

variable {d : ℕ}

theorem vecEuclideanNorm_pos_of_ne {x : Vec d} (hx : x ≠ 0) : 0 < vecEuclideanNorm x :=
  vecEuclideanNorm_pos_iff.2 hx

theorem uProf_zero (i : Fin d) (γ α : ℝ) : uProf i γ α 0 = 0 := by simp [uProf]

theorem uProf_eq_of_ne (i : Fin d) (γ α : ℝ) {x : Vec d} (hx : x ≠ 0) :
    uProf i γ α x = vecEuclideanNorm x ^ α * phi γ (x i / vecEuclideanNorm x) := by
  simp only [uProf, hx, ↓reduceIte, phi]
  rw [mul_div_assoc]

/-- `|u(x)| ≤ |x|^α`. -/
theorem abs_uProf_le (i : Fin d) {γ α : ℝ} (hγ : 1 ≤ γ) (hα : 0 < α) (x : Vec d) :
    |uProf i γ α x| ≤ vecEuclideanNorm x ^ α := by
  by_cases hx : x = 0
  · subst hx; simp [uProf_zero, vecEuclideanNorm, vecNormSq, vecDot, hα.ne']
  · have hr := vecEuclideanNorm_pos_of_ne hx
    rw [uProf_eq_of_ne i γ α hx, abs_mul, abs_of_nonneg (Real.rpow_nonneg hr.le _)]
    have : |phi γ (x i / vecEuclideanNorm x)| ≤ 1 := by
      apply abs_phi_le_one hγ
      rw [abs_div, abs_of_pos hr, div_le_one hr]
      exact abs_apply_le_vecEuclideanNorm x i
    nlinarith [Real.rpow_nonneg hr.le α]

theorem vecEuclideanNorm_smul_single (i : Fin d) {s : ℝ} (hs : 0 < s) :
    vecEuclideanNorm (s • (Pi.single i (1 : ℝ) : Vec d)) = s := by
  rw [vecEuclideanNorm_smul]
  have : vecEuclideanNorm (Pi.single i (1 : ℝ) : Vec d) = 1 := by
    unfold vecEuclideanNorm vecNormSq vecDot
    simp [Pi.single_apply]
  rw [this, abs_of_pos hs, mul_one]

theorem smul_single_ne_zero (i : Fin d) {s : ℝ} (hs : 0 < s) :
    (s • (Pi.single i (1 : ℝ) : Vec d)) ≠ 0 := by
  intro h
  have := congrFun h i
  simp at this
  linarith

/-- `u(s e_i) = s^α` for `s > 0`. -/
theorem uProf_ray (i : Fin d) {γ : ℝ} (hγ : 1 ≤ γ) (α : ℝ) {s : ℝ} (hs : 0 < s) :
    uProf i γ α (s • (Pi.single i (1 : ℝ) : Vec d)) = s ^ α := by
  have hne := smul_single_ne_zero i hs
  simp only [uProf, hne, ↓reduceIte, vecEuclideanNorm_smul_single i hs]
  have : (s • (Pi.single i (1 : ℝ) : Vec d)) i = s := by simp
  rw [this, mul_div_assoc, div_self hs.ne', mul_one, div_self (tanh_pos_of_one_le hγ).ne', mul_one]

/-- `u(-s e_i) = -s^α` for `s > 0`. -/
theorem uProf_neg_ray (i : Fin d) {γ : ℝ} (hγ : 1 ≤ γ) (α : ℝ) {s : ℝ} (hs : 0 < s) :
    uProf i γ α (-(s • (Pi.single i (1 : ℝ) : Vec d))) = -(s ^ α) := by
  have hne := smul_single_ne_zero i hs
  have hne' : (-(s • (Pi.single i (1 : ℝ) : Vec d))) ≠ 0 := neg_ne_zero.2 hne
  simp only [uProf, hne', ↓reduceIte, vecEuclideanNorm_neg, vecEuclideanNorm_smul_single i hs]
  have : (-(s • (Pi.single i (1 : ℝ) : Vec d))) i = -s := by simp
  rw [this, mul_neg, neg_div, mul_div_assoc, div_self hs.ne', mul_one, tanh_neg,
    neg_div, div_self (tanh_pos_of_one_le hγ).ne', mul_neg, mul_one]

theorem continuous_tanh' : Continuous tanh :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_tanh' x).continuousAt

/-- `u` is continuous on all of `Vec d` (in particular on `B_1` and at `0`). -/
theorem continuous_uProf (i : Fin d) {γ α : ℝ} (hγ : 1 ≤ γ) (hα : 0 < α) :
    Continuous (uProf i γ α) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hnorm : Continuous fun y : Vec d => vecEuclideanNorm y := continuous_vecEuclideanNorm
  by_cases hx : x = 0
  · subst hx
    have h0 : vecEuclideanNorm (0 : Vec d) = 0 := by
      simp [vecEuclideanNorm, vecNormSq, vecDot]
    have hrp : Continuous fun y : Vec d => vecEuclideanNorm y ^ α :=
      hnorm.rpow_const (fun _ => Or.inr hα.le)
    have hb : Filter.Tendsto (fun y : Vec d => vecEuclideanNorm y ^ α) (nhds 0) (nhds 0) := by
      have := hrp.tendsto 0
      simpa [h0, Real.zero_rpow hα.ne'] using this
    have hb' : Filter.Tendsto (fun y : Vec d => -(vecEuclideanNorm y ^ α)) (nhds 0) (nhds 0) := by
      simpa using hb.neg
    show Filter.Tendsto (uProf i γ α) (nhds 0) (nhds (uProf i γ α 0))
    rw [uProf_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hb' hb
      (fun y => neg_le_of_abs_le (abs_uProf_le i hγ hα y))
      (fun y => (le_abs_self _).trans (abs_uProf_le i hγ hα y))
  · have hr := vecEuclideanNorm_pos_of_ne hx
    have hcoord : Continuous fun y : Vec d => y i := continuous_apply i
    have hc : ContinuousAt (fun y : Vec d => vecEuclideanNorm y ^ α *
        (Real.tanh (γ * y i / vecEuclideanNorm y) / Real.tanh γ)) x := by
      refine ContinuousAt.mul (hnorm.continuousAt.rpow_const (Or.inl hr.ne')) ?_
      refine ContinuousAt.div_const ?_ _
      refine continuous_tanh'.continuousAt.comp ?_
      exact ContinuousAt.div (continuousAt_const.mul hcoord.continuousAt) hnorm.continuousAt hr.ne'
    refine hc.congr ?_
    have : {y : Vec d | y ≠ 0} ∈ nhds x := (isOpen_ne).mem_nhds hx
    filter_upwards [this] with y hy
    simp [uProf, hy]

end PDE.Guerra
