module

public import PDEFoundation.Ambient.RadialEllipticity
public import PDEFoundation.Ambient.MatAppendEllipticity

/-! # Ellipticity of a planar radial coefficient with unused identity directions -/

@[expose] public section

namespace PDE

private theorem isEllipticMatrix_one (n : ℕ) :
    IsEllipticMatrix 1 1 (1 : Mat n) := by
  simpa only [sub_zero, add_zero, zero_smul, add_zero] using
    isEllipticMatrix_one_add_radialReflectionMatrix
      (delta := (0 : ℝ)) (by norm_num) (by norm_num) (0 : Vec n)

/-- The identity in the unused variables lies between the two planar
ellipticity bounds, so adjoining it preserves those bounds. -/
theorem isEllipticMatrix_matAppend_one_add_planarRadialReflectionMatrix
    (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1) (x : Vec 2) :
    IsEllipticMatrix (1 - δ) (1 + δ)
      (matAppend ((1 : Mat 2) + δ • radialReflectionMatrix x) (1 : Mat n)) := by
  have hI : IsEllipticMatrix (1 - δ) (1 + δ) (1 : Mat n) :=
    (isEllipticMatrix_one n).mono (by linarith) (by linarith) (by linarith)
  exact (isEllipticMatrix_one_add_radialReflectionMatrix hδ hδ1 x).matAppend hI

/-- Normalize the planar block to lower ellipticity one and keep the identity
in the unused directions. The whole matrix has the exact same allowed ratio. -/
theorem isEllipticMatrix_matAppend_normalized_planarRadialReflectionMatrix
    (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1) (x : Vec 2) :
    IsEllipticMatrix 1 ((1 + δ) / (1 - δ))
      (matAppend ((1 - δ)⁻¹ • ((1 : Mat 2) + δ • radialReflectionMatrix x))
        (1 : Mat n)) := by
  have hratio : 1 ≤ (1 + δ) / (1 - δ) :=
    (le_div_iff₀ (by linarith : 0 < 1 - δ)).2 (by linarith)
  have hI : IsEllipticMatrix 1 ((1 + δ) / (1 - δ)) (1 : Mat n) :=
    (isEllipticMatrix_one n).mono (by norm_num) le_rfl hratio
  exact (isEllipticMatrix_normalized_radialReflectionMatrix hδ hδ1 x).matAppend hI

end PDE
