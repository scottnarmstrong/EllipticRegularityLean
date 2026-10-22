module

public import PDEFoundation.Analysis.Inequalities.Nash.Cube
public import PDEFoundation.Analysis.Inequalities.Nash.Tiling
public import PDEFoundation.Analysis.Inequalities.Nash.Optimize
public import PDEFoundation.Sobolev.H1.VectorL2Bounds

/-!
# The Nash inequality

Proposition 1.22.  The proof tiles `ℝ^d` by open cubes of side `ℓ`, applies the
one-cube estimate `∫_R u² ≤ c ℓ² ∫_R |∇u|² + ℓ^{-d} (∫_R |u|)²` (Poincaré on the cube plus the
squared mean) on every tile, sums over the tiles, and optimizes over `ℓ`.  No density argument
is needed because the cube Poincaré inequality is available directly for `H¹` functions.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Nash

open MeasureTheory

/-- The tiled inequality `∫ u² ≤ c ℓ² ∫ |∇u|² + ℓ^{-d} (∫ |u|)²`, `c = 4^d d`. -/
theorem integral_sq_le_tiled {d : ℕ} (u : H1Function (Set.univ : Set (Vec d)))
    (hu1 : Integrable u.toFun volume) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∫ x, u x ^ 2 ≤ (4 : ℝ) ^ d * d * ℓ ^ 2 * (∫ x, vecEuclideanNorm (u.grad x) ^ 2) +
      (ℓ ^ d)⁻¹ * (∫ x, |u x|) ^ 2 := by
  have hu2 : MemLp u.toFun 2 volume := by
    have h := u.memL2
    unfold MemL2On MemLpOn volumeOn at h
    rwa [Measure.restrict_univ] at h
  have hg2 : MemLp (fun x => vecEuclideanNorm (u.grad x)) 2 volume := by
    have h := u.gradMemL2.memLp_vecEuclideanNorm
    unfold volumeOn at h
    rwa [Measure.restrict_univ] at h
  have hXs := hasSum_setIntegral_tileCube hℓ (hu2.integrable_sq)
  have hSs := hasSum_setIntegral_tileCube hℓ (hg2.integrable_sq)
  have hBs := hasSum_setIntegral_tileCube hℓ hu1.abs
  set B := ∫ x, |u x| with hB
  have hF0 : ∀ k : Fin d → ℤ, 0 ≤ ∫ x in tileCube ℓ k, |u x| := fun k =>
    setIntegral_nonneg (isOpen_axisCube _ _).measurableSet (fun x _ => abs_nonneg _)
  have hFle : ∀ k : Fin d → ℤ, ∫ x in tileCube ℓ k, |u x| ≤ B := fun k =>
    le_hasSum hBs k (fun j _ => hF0 j)
  have hcube : ∀ k : Fin d → ℤ, ∫ x in tileCube ℓ k, u x ^ 2 ≤
      (4 : ℝ) ^ d * d * ℓ ^ 2 * (∫ x in tileCube ℓ k, vecEuclideanNorm (u.grad x) ^ 2) +
        (ℓ ^ d)⁻¹ * B * (∫ x in tileCube ℓ k, |u x|) := by
    intro k
    unfold tileCube
    have h := cube_estimate u (fun i => ℓ * (k i : ℝ)) hℓ
    have hc : ((2 : ℝ) ^ d * (Real.sqrt d * ℓ)) ^ 2 = (4 : ℝ) ^ d * d * ℓ ^ 2 := by
      have h4 : (4 : ℝ) ^ d = ((2 : ℝ) ^ d) ^ 2 := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d), h4]
      ring
    rw [hc] at h
    simp only [vecEuclideanNorm_sq]
    have hsq : (∫ x in axisCube (fun i => ℓ * (k i : ℝ)) ℓ, |u x|) ^ 2 ≤
        B * (∫ x in axisCube (fun i => ℓ * (k i : ℝ)) ℓ, |u x|) := by
      rw [sq]; exact mul_le_mul_of_nonneg_right (hFle k) (hF0 k)
    have hinv : 0 ≤ (ℓ ^ d)⁻¹ := inv_nonneg.mpr (pow_pos hℓ d).le
    calc _ ≤ _ := h
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hsq hinv
        rw [← mul_assoc] at this
        linarith
  have hR : HasSum (fun k : Fin d → ℤ =>
      (4 : ℝ) ^ d * d * ℓ ^ 2 * (∫ x in tileCube ℓ k, vecEuclideanNorm (u.grad x) ^ 2) +
        (ℓ ^ d)⁻¹ * B * (∫ x in tileCube ℓ k, |u x|))
      ((4 : ℝ) ^ d * d * ℓ ^ 2 * (∫ x, vecEuclideanNorm (u.grad x) ^ 2) +
        (ℓ ^ d)⁻¹ * B * B) :=
    (hSs.mul_left _).add (hBs.mul_left _)
  have := hasSum_le hcube hXs hR
  calc _ ≤ _ := this
    _ = _ := by rw [hB]; ring

/-- The Nash inequality (Proposition 1.22), with `C = 2 · 4^d · d`. -/
theorem exists_nash_constant_full (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : H1Function (Set.univ : Set (Vec d)),
      Integrable u.toFun volume →
      ∫ x, u.toFun x ^ 2 ≤
        C * (∫ x, vecEuclideanNorm (u.grad x) ^ 2) ^ ((d : ℝ) / (d + 2)) *
          (∫ x, |u.toFun x|) ^ ((4 : ℝ) / (d + 2)) := by
  have hc1 : (1 : ℝ) ≤ (4 : ℝ) ^ d * d := by
    have h1 : (1 : ℝ) ≤ (4 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  refine ⟨2 * ((4 : ℝ) ^ d * d), by positivity, fun u hu1 => ?_⟩
  have h := le_rpow_of_forall_le hd hc1
    (X := ∫ x, u x ^ 2) (S := ∫ x, vecEuclideanNorm (u.grad x) ^ 2) (B := ∫ x, |u x|)
    (integral_nonneg fun x => sq_nonneg _) (integral_nonneg fun x => sq_nonneg _)
    (integral_nonneg fun x => abs_nonneg _)
    (fun ℓ hℓ => by
      have := integral_sq_le_tiled u hu1 hℓ
      linarith)
  exact h

end PDE.Nash
