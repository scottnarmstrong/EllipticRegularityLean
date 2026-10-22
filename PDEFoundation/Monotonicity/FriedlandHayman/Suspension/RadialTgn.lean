module

public import PDEFoundation.Monotonicity.FriedlandHayman.Suspension.Radial

/-!
# Friedland--Hayman: the tangential gradient of a radial lift

For `y = r w` with `|w| = 1` the quantity `|∇Φ|² - (y·∇Φ)²` of the radial lift `Φ = g(|y|) f(y/|y|)` equals
`(1 - r²) g'(r)² f(w)² + (g(r)/r)² |∇_T f(w)|²`.
-/

@[expose] public section

namespace PDE.FHLane

noncomputable section

namespace Susp

theorem vecNormSq_tangentSplit {n : ℕ} (w p : Vec n) (hw : vecNormSq w = 1) {s : ℝ}
    (hs : vecDot p w = s) (A B : ℝ) :
    vecNormSq (fun i => A * w i + B * (p i - s * w i)) = A ^ 2 + B ^ 2 * (vecNormSq p - s ^ 2) := by
  have h1 : ∑ i, w i ^ 2 = 1 := by rw [← vecNormSq_eq_sum_sq, hw]
  have h2 : ∑ i, w i * p i = s := by rw [← hs, vecDot_comm]; rfl
  have h3 : ∑ i, p i ^ 2 = vecNormSq p := (vecNormSq_eq_sum_sq p).symm
  rw [vecNormSq_eq_sum_sq]
  have h4 : ∀ i, (A * w i + B * (p i - s * w i)) ^ 2 =
      (A - B * s) ^ 2 * w i ^ 2 + 2 * (A - B * s) * B * (w i * p i) + B ^ 2 * p i ^ 2 := by
    intro i; ring
  simp_rw [h4, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2, h3]
  ring

theorem vecDot_tangentSplit {n : ℕ} (w p : Vec n) (hw : vecNormSq w = 1) {s : ℝ}
    (hs : vecDot p w = s) (A B : ℝ) :
    vecDot (fun i => A * w i + B * (p i - s * w i)) w = A := by
  have h1 : ∑ i, w i * w i = 1 := by
    have := vecNormSq_eq_sum_sq w
    rw [hw] at this
    simpa [pow_two] using this.symm
  have h2 : ∑ i, p i * w i = s := hs
  have h4 : ∀ i, (A * w i + B * (p i - s * w i)) * w i =
      (A - B * s) * (w i * w i) + B * (p i * w i) := by
    intro i; ring
  unfold vecDot
  simp_rw [h4, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2]
  ring

theorem vecNormSq_inv_smul {n : ℕ} {y : Vec n} (hy : y ≠ 0) :
    vecNormSq ((vecEuclideanNorm y)⁻¹ • y) = 1 := by
  have hr : 0 < vecEuclideanNorm y := vecEuclideanNorm_pos_of_ne hy
  rw [vecNormSq_smul, ← vecEuclideanNorm_sq]
  field_simp

/-- The tangential gradient quantity of a radial lift. -/
theorem tgn_radialLift {n : ℕ} {g : ℝ → ℝ} {g' : ℝ} {f : Vec n → ℝ}
    (hf : ContDiff ℝ 1 f) {y : Vec n} (hy : y ≠ 0)
    (hg : HasDerivAt g g' (vecEuclideanNorm y)) :
    vecNormSq (classicalGradient (radialLift g f) y) -
        vecDot (classicalGradient (radialLift g f) y) y ^ 2 =
      (1 - vecEuclideanNorm y ^ 2) * (g' ^ 2 * f ((vecEuclideanNorm y)⁻¹ • y) ^ 2) +
        (g (vecEuclideanNorm y) / vecEuclideanNorm y) ^ 2 *
          tangentialGradientNormSq f ((vecEuclideanNorm y)⁻¹ • y) := by
  have hr : 0 < vecEuclideanNorm y := vecEuclideanNorm_pos_of_ne hy
  have hw := vecNormSq_inv_smul hy
  rw [classicalGradient_radialLift hf hy hg]
  set r := vecEuclideanNorm y with hr_def
  set w := r⁻¹ • y with hw_def
  set p := classicalGradient f w with hp
  have hyw : y = r • w := by rw [hw_def, smul_inv_smul₀ hr.ne']
  have hcomp : ∀ i, r⁻¹ * y i = w i := by
    intro i; rw [hw_def]; simp
  have hu : (fun i => g' * f w * (r⁻¹ * y i) + g r * r⁻¹ * (p i - vecDot p w * (r⁻¹ * y i))) =
      fun i => (g' * f w) * w i + (g r / r) * (p i - vecDot p w * w i) := by
    funext i; rw [hcomp i, div_eq_mul_inv]
  have hkey : vecDot (fun i => (g' * f w) * w i + (g r / r) * (p i - vecDot p w * w i)) y =
      r * (g' * f w) := by
    calc _ = vecDot (fun i => (g' * f w) * w i + (g r / r) * (p i - vecDot p w * w i)) (r • w) := by
          rw [← hyw]
      _ = r * vecDot (fun i => (g' * f w) * w i + (g r / r) * (p i - vecDot p w * w i)) w :=
          vecDot_smul_right _ _ _
      _ = r * (g' * f w) := by rw [vecDot_tangentSplit w p hw rfl]
  rw [hu, vecNormSq_tangentSplit w p hw rfl, hkey]
  unfold tangentialGradientNormSq
  rw [← hp]
  ring

end Susp

end

end PDE.FHLane
