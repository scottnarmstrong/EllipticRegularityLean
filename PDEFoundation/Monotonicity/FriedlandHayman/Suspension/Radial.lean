module

public import PDEFoundation.Monotonicity.FriedlandHayman.Suspension.Defs
public import PDEFoundation.Monotonicity.Poon.GaussianDeriv
public import PDEFoundation.Geometry.EuclideanBall.Topology
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Friedland--Hayman: radial lifts

For `g : ℝ → ℝ` and `f : Vec n → ℝ` the radial lift is `Φ(y) = g(|y|) f(y/|y|)`.  We prove that it is
`C¹` when `g` vanishes near `0` and is `C¹` on `(0, ∞)`, and compute its gradient away from the origin.
-/

@[expose] public section

namespace PDE.FHLane

noncomputable section

namespace Susp

/-- The radial lift `Φ(y) = g(|y|) f(y/|y|)`. -/
def radialLift {n : ℕ} (g : ℝ → ℝ) (f : Vec n → ℝ) (y : Vec n) : ℝ :=
  g (vecEuclideanNorm y) * f ((vecEuclideanNorm y)⁻¹ • y)

theorem vecEuclideanNorm_pos_of_ne {n : ℕ} {y : Vec n} (hy : y ≠ 0) : 0 < vecEuclideanNorm y :=
  vecEuclideanNorm_pos_iff.2 hy

theorem contDiffAt_vecEuclideanNorm {n : ℕ} {y : Vec n} (hy : y ≠ 0) :
    ContDiffAt ℝ 1 (fun y : Vec n => vecEuclideanNorm y) y := by
  have hne : vecNormSq y ≠ 0 := vecNormSq_eq_zero_iff.not.mpr hy
  have h := (contDiff_vecNormSq (d := n)).contDiffAt (x := y) |>.sqrt hne
  exact h.of_le (by exact_mod_cast le_top)

theorem contDiff_radialLift {n : ℕ} {g : ℝ → ℝ} {f : Vec n → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hg0 : ∀ t, t ≤ ε → g t = 0) (hg : ∀ t, 0 < t → ContDiffAt ℝ 1 g t)
    (hf : ContDiff ℝ 1 f) : ContDiff ℝ 1 (radialLift g f) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : vecEuclideanNorm y < ε
  · have hev : radialLift g f =ᶠ[nhds y] fun _ => (0 : ℝ) := by
      have : ∀ᶠ z in nhds y, vecEuclideanNorm z < ε :=
        (continuous_vecEuclideanNorm.continuousAt).eventually (Iio_mem_nhds hy)
      filter_upwards [this] with z hz
      simp [radialLift, hg0 _ hz.le]
    exact (contDiffAt_const).congr_of_eventuallyEq hev
  · push Not at hy
    have hr : 0 < vecEuclideanNorm y := lt_of_lt_of_le hε hy
    have hy0 : y ≠ 0 := by
      intro h; rw [h] at hr; simp [vecEuclideanNorm, vecNormSq, vecDot] at hr
    have hn := contDiffAt_vecEuclideanNorm hy0
    have h1 : ContDiffAt ℝ 1 (fun z : Vec n => g (vecEuclideanNorm z)) y :=
      (hg _ hr).comp y hn
    have h2 : ContDiffAt ℝ 1 (fun z : Vec n => (vecEuclideanNorm z)⁻¹ • z) y :=
      (hn.inv hr.ne').smul contDiffAt_id
    exact h1.mul ((hf.contDiffAt).comp y h2)

theorem exists_hasFDerivAt_norm {n : ℕ} {y : Vec n} (hy : y ≠ 0) :
    ∃ L : Vec n →L[ℝ] ℝ, HasFDerivAt (fun y : Vec n => vecEuclideanNorm y) L y ∧
      ∀ i, L (basisVec i) = y i / vecEuclideanNorm y := by
  have hne : vecNormSq y ≠ 0 := vecNormSq_eq_zero_iff.not.mpr hy
  have h := (hasFDerivAt_vecNormSq y).sqrt hne
  refine ⟨_, h, fun i => ?_⟩
  have hr : 0 < Real.sqrt (vecNormSq y) := Real.sqrt_pos.2 (lt_of_le_of_ne (vecNormSq_nonneg y)
    (Ne.symm hne))
  simp only [smul_apply, vecNormSqFDeriv_basisVec, smul_eq_mul, vecEuclideanNorm]
  field_simp

theorem exists_hasFDerivAt_dir {n : ℕ} {y : Vec n} (hy : y ≠ 0) :
    ∃ M : Vec n →L[ℝ] Vec n,
      HasFDerivAt (fun z : Vec n => (vecEuclideanNorm z)⁻¹ • z) M y ∧
      ∀ i, M (basisVec i) = (vecEuclideanNorm y)⁻¹ •
        (basisVec i - ((vecEuclideanNorm y)⁻¹ * y i) • ((vecEuclideanNorm y)⁻¹ • y)) := by
  obtain ⟨L, hL, hLi⟩ := exists_hasFDerivAt_norm hy
  have hr : 0 < vecEuclideanNorm y := vecEuclideanNorm_pos_of_ne hy
  have hinv := (hasDerivAt_inv hr.ne').comp_hasFDerivAt y hL
  have h := hinv.smul (hasFDerivAt_id y)
  refine ⟨_, h, fun i => ?_⟩
  ext j
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_id', id_eq, hLi,
    Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, basisVec_apply]
  field_simp
  ring

theorem vecDot_smul_right {n : ℕ} (c : ℝ) (p w : Vec n) : vecDot p (c • w) = c * vecDot p w := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The gradient of a radial lift away from the origin. -/
theorem classicalGradient_radialLift {n : ℕ} {g : ℝ → ℝ} {g' : ℝ} {f : Vec n → ℝ}
    (hf : ContDiff ℝ 1 f) {y : Vec n} (hy : y ≠ 0)
    (hg : HasDerivAt g g' (vecEuclideanNorm y)) :
    classicalGradient (radialLift g f) y = fun i =>
      g' * f ((vecEuclideanNorm y)⁻¹ • y) * ((vecEuclideanNorm y)⁻¹ * y i) +
        g (vecEuclideanNorm y) * (vecEuclideanNorm y)⁻¹ *
          (classicalGradient f ((vecEuclideanNorm y)⁻¹ • y) i -
            vecDot (classicalGradient f ((vecEuclideanNorm y)⁻¹ • y)) ((vecEuclideanNorm y)⁻¹ • y) *
              ((vecEuclideanNorm y)⁻¹ * y i)) := by
  obtain ⟨L, hL, hLi⟩ := exists_hasFDerivAt_norm hy
  obtain ⟨M, hM, hMi⟩ := exists_hasFDerivAt_dir hy
  have h1 : HasFDerivAt (g ∘ fun z : Vec n => vecEuclideanNorm z) (g' • L) y :=
    hg.comp_hasFDerivAt y hL
  have h2 : HasFDerivAt (f ∘ fun z : Vec n => (vecEuclideanNorm z)⁻¹ • z)
      ((fderiv ℝ f ((vecEuclideanNorm y)⁻¹ • y)).comp M) y :=
    (hf.differentiable (by simp) _).hasFDerivAt.comp y hM
  have h3 := h1.mul h2
  ext i
  rw [classicalGradient_apply]
  have h4 : HasFDerivAt (radialLift g f) _ y := h3
  rw [h4.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply, hLi,
    hMi, smul_eq_mul, map_smul, map_sub]
  rw [← classicalGradient_apply, fderiv_apply_eq_vecDot_classicalGradient]
  rw [vecDot_smul_right]
  ring

end Susp

end

end PDE.FHLane
