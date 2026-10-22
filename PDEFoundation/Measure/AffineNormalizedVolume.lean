module

public import PDEFoundation.Measure.DilationLp
public import PDEFoundation.Measure.BallVolume

/-! # Affine transport of normalized restricted volume -/

@[expose] public section

open scoped Pointwise

namespace PDE

open MeasureTheory

/-- Translation by `z` pushes normalized restricted volume on `U` to
normalized restricted volume on `z + U`. -/
theorem measurePreserving_addRight_normalizedVolumeOn_translateSet
    {d : ℕ} (z : Vec d) (U : Set (Vec d)) :
    MeasurePreserving (fun x : Vec d => x + z)
      (normalizedVolumeOn U) (normalizedVolumeOn (translateSet z U)) := by
  refine ⟨(measurePreserving_addRight_restrict_translateSet z U).measurable, ?_⟩
  rw [normalizedVolumeOn, normalizedVolumeOn, Measure.map_smul _
      (measurePreserving_addRight_restrict_translateSet z U).measurable.aemeasurable,
    (measurePreserving_addRight_restrict_translateSet z U).map_eq,
    volume_translateSet_eq]

/-- Positive dilation pushes normalized restricted volume on `U` to normalized
restricted volume on `r • U`. -/
theorem measurePreserving_smul_normalizedVolumeOn_smul_set
    {d : ℕ} {r : ℝ} (hr : 0 < r) (U : Set (Vec d)) :
    MeasurePreserving (fun x : Vec d => r • x)
      (normalizedVolumeOn U) (normalizedVolumeOn (r • U)) := by
  have hrInv : 0 < r⁻¹ := inv_pos.mpr hr
  have h := measurePreserving_inv_smul_normalizedVolumeOn_smul_set
    hrInv (r • U)
  have hset : r⁻¹ • (r • U) = U := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Set.mem_smul_set.1 hx
      obtain ⟨u, hu, huy⟩ := Set.mem_smul_set.1 hy
      rw [← hyx, ← huy, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
      exact hu
    · intro hx
      apply Set.mem_smul_set.2
      refine ⟨r • x, Set.mem_smul_set.2 ⟨x, hx, rfl⟩, ?_⟩
      simp only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  convert h using 1
  · funext x
    rw [inv_inv]
  · congr 2
    exact hset.symm

/-- Positive dilation followed by translation preserves normalized restricted
volume, with the affine image set displayed literally. -/
theorem measurePreserving_smul_addRight_normalizedVolumeOn
    {d : ℕ} {r : ℝ} (hr : 0 < r) (z : Vec d) (U : Set (Vec d)) :
    MeasurePreserving (fun x : Vec d => r • x + z)
      (normalizedVolumeOn U)
      (normalizedVolumeOn (translateSet z (r • U))) := by
  exact (measurePreserving_addRight_normalizedVolumeOn_translateSet z (r • U)).comp
    (measurePreserving_smul_normalizedVolumeOn_smul_set hr U)

/-- The affine parametrization of a round ball pushes normalized unit-ball
volume to normalized volume on that ball. -/
theorem measurePreserving_smul_addRight_normalizedVolumeOn_euclideanBall
    {d : ℕ} {R : ℝ} (hR : 0 < R) (z : Vec d) :
    MeasurePreserving (fun x : Vec d => R • x + z)
      (normalizedVolumeOn (euclideanBall (0 : Vec d) 1))
      (normalizedVolumeOn (euclideanBall z R)) := by
  rw [euclideanBall_eq_translateSet_smul_unit_of_pos z hR]
  exact measurePreserving_smul_addRight_normalizedVolumeOn hR z _

/-- The inverse affine parametrization of a round ball pushes its normalized
volume back to normalized unit-ball volume. -/
theorem measurePreserving_inv_smul_subRight_normalizedVolumeOn_euclideanBall
    {d : ℕ} {R : ℝ} (hR : 0 < R) (z : Vec d) :
    MeasurePreserving (fun x : Vec d => R⁻¹ • (x - z))
      (normalizedVolumeOn (euclideanBall z R))
      (normalizedVolumeOn (euclideanBall (0 : Vec d) 1)) := by
  rw [euclideanBall_eq_translateSet_smul_unit_of_pos z hR]
  exact (measurePreserving_inv_smul_normalizedVolumeOn_smul_set hR
    (euclideanBall (0 : Vec d) 1)).comp
      (measurePreserving_subRight_normalizedVolumeOn_translateSet z
        (R • euclideanBall (0 : Vec d) 1))

end PDE
