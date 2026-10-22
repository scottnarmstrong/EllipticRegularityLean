module

public import PDEFoundation.Measure.LinearAverage
public import PDEFoundation.Sobolev.H1.VectorMeanOscillation

/-!
# Vector means and centered oscillation under linear coordinates
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Pullback by the inverse of a continuous linear equivalence preserves
coordinatewise native vector `L²` membership on the image domain. -/
theorem memVectorL2On_comp_symm_linearEquiv
    (e : Vec d ≃L[ℝ] Vec d) {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : MemVectorL2On U g) :
    MemVectorL2On (e '' U) (fun y => g (e.symm y)) := by
  intro i
  have hi := memLpOn_comp_linearEquiv (e := e.symm) (U := e '' U)
    (f := fun x => g x i) (by simpa using hg i)
  simpa using hi

/-- The coordinatewise vector integral average is exactly invariant under
pullback to a linear image domain. -/
theorem vectorIntegralAverage_comp_symm_linearEquiv
    (e : Vec d ≃L[ℝ] Vec d) {U : Set (Vec d)}
    (hUpos : 0 < volume U) (hUtop : volume U < ∞)
    (g : Vec d → Vec d) :
    vectorIntegralAverage (e '' U) (fun y => g (e.symm y)) =
      vectorIntegralAverage U g := by
  funext i
  have h := integralAverage_comp_linearEquiv e hUpos hUtop
    (fun y => g (e.symm y) i)
  simpa only [vectorIntegralAverage_apply, e.symm_apply_apply] using h.symm

/-- Centered native-vector mean `L²` oscillation is exactly invariant under
pullback to a linear image domain; the Jacobian cancels in normalization. -/
theorem centeredVectorMeanL2_comp_symm_linearEquiv
    (e : Vec d ≃L[ℝ] Vec d) {U : Set (Vec d)}
    (hUpos : 0 < volume U) (hUtop : volume U < ∞)
    (g : Vec d → Vec d) :
    centeredVectorMeanL2 (e '' U) (fun y => g (e.symm y)) =
      centeredVectorMeanL2 U g := by
  have hmean := vectorIntegralAverage_comp_symm_linearEquiv
    e hUpos hUtop g
  unfold centeredVectorMeanL2
  rw [hmean]
  have h := integralAverage_comp_linearEquiv e hUpos hUtop
    (fun y => vecNormSq (g (e.symm y) - vectorIntegralAverage U g))
  congr 1
  simpa only [e.symm_apply_apply] using h.symm

end

end PDE
