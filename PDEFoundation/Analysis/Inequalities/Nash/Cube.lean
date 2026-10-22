module

public import PDEFoundation.Sobolev.Inequalities.ConvexPoincareL2
public import PDEFoundation.Measure.CubeVolume
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# One-cube estimate for the Nash inequality

For an `H¹` function `u` and an open axis cube `V` of side `ℓ`, the `L²` mass of `u`
on `V` is bounded by a Poincaré term plus a squared `L¹` term:
`∫_V u² ≤ (2^d √d ℓ)² ∫_V |∇u|² + ℓ^{-d} (∫_V |u|)²`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Nash

open MeasureTheory

/-- Variance decomposition `∫_V u² = ∫_V (u - ū)² + |V| ū²` on a finite-measure set. -/
theorem integral_sq_eq_centered_add {d : ℕ} {V : Set (Vec d)} {f : Vec d → ℝ}
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (hf2 : MemLp f 2 (volume.restrict V)) :
    ∫ x in V, f x ^ 2 =
      (∫ x in V, (f x - integralAverage V f) ^ 2) +
        (volume V).toReal * integralAverage V f ^ 2 := by
  have : IsFiniteMeasure (volume.restrict V) := hV.isFiniteMeasure_volumeOn
  have hf1 : Integrable f (volume.restrict V) := hf2.integrable (by norm_num)
  have hfs : Integrable (fun x => f x ^ 2) (volume.restrict V) := hf2.integrable_sq
  set m := integralAverage V f with hm
  set I := ∫ x in V, f x with hI
  have hexp : ∀ x, (f x - m) ^ 2 = f x ^ 2 - (2 * m) * f x + m ^ 2 := fun x => by ring
  have h1 : ∫ x in V, (f x - m) ^ 2 =
      (∫ x in V, f x ^ 2) - (2 * m) * I + m ^ 2 * (volume V).toReal := by
    simp only [hexp]
    have hA : Integrable (fun x => f x ^ 2 - (2 * m) * f x) (volume.restrict V) :=
      hfs.sub (hf1.const_mul _)
    rw [integral_add hA (integrable_const _), integral_sub hfs (hf1.const_mul _),
      integral_const_mul]
    simp [Measure.real, mul_comm, hI]
  have hpos : (volume V).toReal ≠ 0 := (hV.volume_toReal_pos hne).ne'
  have hmI : I = (volume V).toReal * m := by
    rw [hm, integralAverage]; field_simp; rfl
  rw [h1, hmI]
  ring

/-- The one-cube estimate: Poincaré on the cube plus the squared mean. -/
theorem cube_estimate {d : ℕ} (u : H1Function (Set.univ : Set (Vec d))) (z : Vec d)
    {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∫ x in axisCube z ℓ, u x ^ 2 ≤
      ((2 : ℝ) ^ d * (Real.sqrt d * ℓ)) ^ 2 * (∫ x in axisCube z ℓ, vecNormSq (u.grad x)) +
        (ℓ ^ d)⁻¹ * (∫ x in axisCube z ℓ, |u x|) ^ 2 := by
  have hV := isOpenBoundedConvexDomain_axisCube z ℓ
  have hne := axisCube_nonempty z hℓ
  have hu2 : MemLp u.toFun 2 (volume.restrict (axisCube z ℓ)) := by
    have h := u.memL2
    unfold MemL2On MemLpOn at h
    exact h.mono_measure (Measure.restrict_mono (Set.subset_univ _) le_rfl)
  have hvol : (volume (axisCube z ℓ)).toReal = ℓ ^ d := volume_axisCube_toReal z hℓ.le
  have hP := centeredPoincare_sq_on_boundedConvexSubdomain u hV (Set.subset_univ _)
    (hasEuclideanDiameterLE_axisCube z hℓ.le)
    (mul_nonneg (Real.sqrt_nonneg _) hℓ.le) hne
  have hdec := integral_sq_eq_centered_add hV hne hu2
  have hℓd : 0 < ℓ ^ d := pow_pos hℓ d
  have : IsFiniteMeasure (volume.restrict (axisCube z ℓ)) := hV.isFiniteMeasure_volumeOn
  have hu1 : Integrable u.toFun (volume.restrict (axisCube z ℓ)) := hu2.integrable (by norm_num)
  have hmean : (volume (axisCube z ℓ)).toReal * integralAverage (axisCube z ℓ) u.toFun ^ 2 ≤
      (ℓ ^ d)⁻¹ * (∫ x in axisCube z ℓ, |u x|) ^ 2 := by
    rw [hvol, integralAverage, hvol, mul_pow]
    have habs : |∫ x in axisCube z ℓ, u x| ≤ ∫ x in axisCube z ℓ, |u x| := by
      simpa using abs_integral_le_integral_abs (μ := volume.restrict (axisCube z ℓ))
        (f := u.toFun)
    have hsq : (∫ x in axisCube z ℓ, u x) ^ 2 ≤ (∫ x in axisCube z ℓ, |u x|) ^ 2 := by
      rw [← sq_abs (∫ x in axisCube z ℓ, u x)]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    have : ℓ ^ d * (((ℓ ^ d)⁻¹) ^ 2 * (∫ x in axisCube z ℓ, u x) ^ 2) =
        (ℓ ^ d)⁻¹ * (∫ x in axisCube z ℓ, u x) ^ 2 := by field_simp
    rw [inv_pow, ← inv_pow] at *
    rw [this]
    exact mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr hℓd.le)
  linarith

end PDE.Nash
