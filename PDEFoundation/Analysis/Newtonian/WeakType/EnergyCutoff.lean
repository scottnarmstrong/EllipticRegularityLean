module

public import PDEFoundation.Analysis.Newtonian.WeakType.EnergyWeak
public import PDEFoundation.Sobolev.Cutoff.Ball
public import PDEFoundation.Measure.BallVolume

/-!
# Cutoff error terms for the energy estimate

For `h` smooth with `tsupport h ⊆ B_{R₀}`, `u = u_h`, and the cutoff `χ_R` (equal to one on `B_R`,
supported in `B_{2R}`, `|∇χ_R| ≤ 32/R`), the error integral `∫ χ_R u ∇u · ∇χ_R` is `O(1/R)`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.NewtonWeakType

noncomputable section

variable {d : ℕ}

/-- A compactly supported function has topological support in a round ball. -/
theorem exists_tsupport_subset_euclideanBall {β : Type*} [Zero β] {f : Vec d → β}
    (hf : HasCompactSupport f) : ∃ R : ℝ, 0 < R ∧ tsupport f ⊆ euclideanBall 0 R := by
  obtain ⟨R, hR, hs⟩ := exists_radius_of_hasCompactSupport hf
  refine ⟨R + 1, by linarith, ?_⟩
  have h1 : tsupport f ⊆ euclideanClosedBall (0 : Vec d) R := by
    refine closure_minimal (fun y hy => ?_) (isClosed_euclideanClosedBall _ _)
    rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR.le, sub_zero]
    exact (hs y hy).le
  exact h1.trans (euclideanClosedBall_subset_euclideanBall hR.le (by linarith))

/-- The cutoff `χ_R`, one on `B_R` and supported in `B_{2R}`. -/
def cutoff (R : ℝ) : Vec d → ℝ := canonicalBallCutoff (0 : Vec d) R (2 * R)

theorem contDiff_cutoff {R : ℝ} (hR : 0 < R) : ContDiff ℝ (⊤ : ℕ∞) (cutoff (d := d) R) :=
  canonicalBallCutoff_smooth _ hR.le (by linarith)

theorem hasCompactSupport_cutoff {R : ℝ} (hR : 0 < R) : HasCompactSupport (cutoff (d := d) R) :=
  canonicalBallCutoff_hasCompactSupport hR.le (by linarith)

theorem cutoff_nonneg (R : ℝ) (x : Vec d) : 0 ≤ cutoff R x := canonicalBallCutoff_nonneg _ _ _ _

theorem cutoff_le_one (R : ℝ) (x : Vec d) : cutoff R x ≤ 1 := canonicalBallCutoff_le_one _ _ _ _

theorem cutoff_eq_one {R : ℝ} (hR : 0 < R) {x : Vec d} (hx : vecEuclideanNorm x < R) :
    cutoff R x = 1 := by
  refine canonicalBallCutoff_eq_one_on_inner hR.le (by linarith) ?_
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR, sub_zero]
  exact hx

theorem cutoff_eq_zero {R : ℝ} (hR : 0 < R) {x : Vec d} (hx : 2 * R ≤ vecEuclideanNorm x) :
    cutoff R x = 0 := by
  have hsub := canonicalBallCutoff_tsupport_subset_outer (x₀ := (0 : Vec d)) hR.le
    (show R < 2 * R by linarith)
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith)).mp (hsub hmem)
  rw [sub_zero] at this
  linarith

theorem classicalGradient_cutoff_eq_zero {R : ℝ} (hR : 0 < R) {x : Vec d}
    (hx : vecEuclideanNorm x < R) : classicalGradient (cutoff R) x = 0 := by
  have hmax : IsMaxOn (cutoff (d := d) R) Set.univ x := by
    intro y _
    rw [cutoff_eq_one hR hx]
    exact cutoff_le_one R y
  have hfd : fderiv ℝ (cutoff (d := d) R) x = 0 := IsLocalMax.fderiv_eq_zero (hmax.isLocalMax (by simp))
  funext i
  rw [classicalGradient_apply, hfd]
  rfl

theorem vecEuclideanNorm_classicalGradient_cutoff_le {R : ℝ} (hR : 0 < R) (x : Vec d) :
    vecEuclideanNorm (classicalGradient (cutoff R) x) ≤ 32 / R := by
  have := canonicalBallCutoff_gradient_bound (x₀ := (0 : Vec d)) hR.le
    (show R < 2 * R by linarith) x
  have h2 : 2 * R - R = R := by ring
  rw [h2] at this
  exact this

/-- Decay of `u_h` and of the coordinates of `∇u_h`. -/
theorem exists_decay_newtonPotential (hd : 0 < d) {h : Vec d → Vec d}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hsupp : tsupport h ⊆ euclideanBall 0 R₀) :
    ∃ Cu Cg : ℝ, 0 ≤ Cu ∧ 0 ≤ Cg ∧ ∀ x : Vec d, 2 * R₀ ≤ vecEuclideanNorm x →
      |newtonPotential h x| ≤ Cu * vecEuclideanNorm x ^ ((1 : ℝ) - d) ∧
      vecEuclideanNorm (classicalGradient (newtonPotential h) x) ≤
        Cg * vecEuclideanNorm x ^ (-(d : ℝ)) := by
  obtain ⟨Cu, hCu, hu⟩ := abs_newtonPotential_le hd hh.continuous hhc hR₀ hsupp
  have hk := fun k : Fin d => abs_coordDeriv_newtonPotential_le hd hh hhc hR₀ hsupp k
  choose Ck hCk0 hCk using hk
  refine ⟨Cu, ∑ k, Ck k, hCu, Finset.sum_nonneg fun k _ => hCk0 k, fun x hx => ⟨hu x hx, ?_⟩⟩
  calc vecEuclideanNorm (classicalGradient (newtonPotential h) x)
      ≤ ∑ k : Fin d, |classicalGradient (newtonPotential h) x k| := vecEuclideanNorm_le_sum_abs _
    _ ≤ ∑ k : Fin d, Ck k * vecEuclideanNorm x ^ (-(d : ℝ)) :=
        Finset.sum_le_sum fun k _ => hCk k x hx
    _ = (∑ k, Ck k) * vecEuclideanNorm x ^ (-(d : ℝ)) := by rw [Finset.sum_mul]

/-- The cutoff error integral is `O(1/R)`. -/
theorem exists_cutoff_error_bound (hd : 0 < d) {h : Vec d → Vec d}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hsupp : tsupport h ⊆ euclideanBall 0 R₀) :
    ∃ M : ℝ, ∀ R : ℝ, max 1 (2 * R₀) ≤ R →
      |∫ x, cutoff R x * newtonPotential h x *
        vecDot (classicalGradient (newtonPotential h) x) (classicalGradient (cutoff R) x)| ≤
        M / R := by
  obtain ⟨Cu, Cg, hCu, hCg, hdec⟩ := exists_decay_newtonPotential hd hh hhc hR₀ hsupp
  set V : ℝ := (volume (euclideanBall (0 : Vec d) 1)).toReal with hV
  have hV0 : 0 < V := volume_euclideanBall_toReal_pos (0 : Vec d) one_pos
  refine ⟨Cu * Cg * 32 * 2 ^ d * V, fun R hRge => ?_⟩
  have hR1 : 1 ≤ R := (le_max_left _ _).trans hRge
  have hR2 : 2 * R₀ ≤ R := (le_max_right _ _).trans hRge
  have hR : 0 < R := by linarith
  set f : Vec d → ℝ := fun x => cutoff R x * newtonPotential h x *
    vecDot (classicalGradient (newtonPotential h) x) (classicalGradient (cutoff R) x) with hf
  set s : Set (Vec d) := euclideanBall 0 (2 * R) with hs
  have hsm : MeasurableSet s := measurableSet_euclideanBall _ _
  have hvol : volume s ≠ ⊤ := volume_euclideanBall_ne_top _ (by linarith)
  have hzero : ∀ x ∈ sᶜ, f x = 0 := by
    intro x hx
    have hx' : 2 * R ≤ vecEuclideanNorm x := by
      by_contra hlt
      push Not at hlt
      apply hx
      rw [hs, mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith), sub_zero]
      exact hlt
    simp [hf, cutoff_eq_zero hR hx']
  set p : ℝ := R ^ d with hp
  have hp0 : 0 < p := by positivity
  have hpR : R ≤ p := by
    simpa using le_self_pow₀ hR1 (Nat.one_le_iff_ne_zero.mp hd)
  have hr1 : R ^ ((1 : ℝ) - d) = R / p := by
    rw [Real.rpow_sub hR, Real.rpow_one, Real.rpow_natCast]
  have hr2 : R ^ (-(d : ℝ)) = p⁻¹ := by
    rw [Real.rpow_neg hR.le, Real.rpow_natCast]
  set B : ℝ := Cu * (R / p) * (Cg * p⁻¹) * (32 / R) with hB
  have hB0 : 0 ≤ B := by positivity
  have hbound : ∀ x ∈ s, ‖f x‖ ≤ B := by
    intro x hx
    rw [Real.norm_eq_abs]
    have hxs : vecEuclideanNorm x < 2 * R := by
      have := (mem_euclideanBall_iff_vecEuclideanNorm_lt (show 0 < 2 * R by linarith)).mp hx
      rwa [sub_zero] at this
    by_cases hxR : vecEuclideanNorm x < R
    · have : f x = 0 := by
        have hz := classicalGradient_cutoff_eq_zero hR hxR
        simp only [hf, hz]
        simp [vecDot]
      rw [this, abs_zero]; exact hB0
    · push Not at hxR
      obtain ⟨hu, hg⟩ := hdec x (by linarith)
      have hxpos : 0 < vecEuclideanNorm x := by linarith
      have e1 : (1 : ℝ) - d ≤ 0 := by
        have : (1 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
      have hu' : |newtonPotential h x| ≤ Cu * (R / p) := by
        rw [← hr1]
        exact hu.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hR hxR e1) hCu)
      have hg' : vecEuclideanNorm (classicalGradient (newtonPotential h) x) ≤ Cg * p⁻¹ := by
        rw [← hr2]
        exact hg.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hR hxR (by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)])) hCg)
      have hc := vecEuclideanNorm_classicalGradient_cutoff_le hR (d := d) x
      have hdot := abs_vecDot_le_vecEuclideanNorm_mul (classicalGradient (newtonPotential h) x)
        (classicalGradient (cutoff R) x)
      have hχ0 := cutoff_nonneg R x
      have hχ1 := cutoff_le_one R x
      have hn1 := vecEuclideanNorm_nonneg (classicalGradient (newtonPotential h) x)
      have hn2 := vecEuclideanNorm_nonneg (classicalGradient (cutoff R) x)
      have hdot' : |vecDot (classicalGradient (newtonPotential h) x) (classicalGradient (cutoff R) x)|
          ≤ Cg * p⁻¹ * (32 / R) :=
        hdot.trans (mul_le_mul hg' hc hn2 (by positivity))
      calc |f x| = cutoff R x * |newtonPotential h x| *
            |vecDot (classicalGradient (newtonPotential h) x) (classicalGradient (cutoff R) x)| := by
            simp only [hf, abs_mul, abs_of_nonneg hχ0]
        _ ≤ 1 * (Cu * (R / p)) * (Cg * p⁻¹ * (32 / R)) := by
            gcongr
        _ = B := by rw [hB]; ring
  have hint : ∫ x, f x = ∫ x in s, f x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  have hnorm := norm_setIntegral_le_of_norm_le_const (μ := volume) (lt_top_iff_ne_top.mpr hvol)
    hbound
  have hvr : volume.real s = (2 * R) ^ d * V := by
    simp only [Measure.real, hs, hV]
    exact volume_euclideanBall_toReal_eq_unit_mul_of_pos _ (by linarith)
  rw [hint]
  refine (Real.norm_eq_abs _ ▸ hnorm).trans ?_
  rw [hvr, hB, mul_pow]
  have hRp : R / p * p⁻¹ * (32 / R) * (2 ^ d * p) = 32 * 2 ^ d / p := by
    field_simp
  calc Cu * (R / p) * (Cg * p⁻¹) * (32 / R) * (2 ^ d * p * V)
      = Cu * Cg * V * (R / p * p⁻¹ * (32 / R) * (2 ^ d * p)) := by ring
    _ = Cu * Cg * 32 * 2 ^ d * V / p := by rw [hRp]; ring
    _ ≤ Cu * Cg * 32 * 2 ^ d * V / R := by
        gcongr

end

end PDE.NewtonWeakType
