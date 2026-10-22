module

public import PDEFoundation.Geometry.PlanarBlockRotation
public import PDEFoundation.Ambient.PlanarRadialProjection

@[expose] public section

namespace PDE

/-- A quarter turn changes the sign of the planar radial reflection away
from the origin. -/
theorem radialReflectionMatrix_planarQuarterTurn
    (x : Vec 2) (hx : x ≠ 0) :
    radialReflectionMatrix (planarQuarterTurn x) = -radialReflectionMatrix x := by
  have hq : vecNormSq x ≠ 0 := vecNormSq_eq_zero_iff.not.mpr hx
  ext i j
  simp only [radialReflectionMatrix, two_smul, Matrix.add_apply, Matrix.sub_apply,
    Matrix.neg_apply, radialProjectionMatrix_apply, vecNormSq_planarQuarterTurn]
  fin_cases i <;> fin_cases j <;>
    simp <;> field_simp [hq] <;>
    simp [vecNormSq, vecDot, Fin.sum_univ_two] <;> ring

end PDE
