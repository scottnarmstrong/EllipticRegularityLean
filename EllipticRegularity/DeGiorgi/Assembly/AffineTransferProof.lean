module

public import EllipticRegularity.DeGiorgi.Assembly.Statements
public import PDEFoundation.PDE.DGNM.Scaling
public import PDEFoundation.PDE.DGNM.ClassAlgebra
public import PDEFoundation.Measure.BallVolume

/-!
# The affine transfer interfaces from the class-stability toolbox

The two scaling hypotheses `SuperAffineTransfer` and `SolAffineTransfer` of the assembly
theorems follow from the toolbox `PDE.DGNM` (blow-up, negation, constants).
-/

@[expose] public section

namespace PDE.DGNMAssembly

open MeasureTheory

theorem coeff_blowUp_eq {d : ℕ} (a : CoeffField d) (x₀ : Vec d) (r : ℝ) :
    DGNM.blowUpCoeff a x₀ r = fun y => a (x₀ + r • y) := by
  funext y
  rw [DGNM.blowUpCoeff_apply, add_comm]

theorem superAffineTransfer (d : ℕ) : SuperAffineTransfer d := by
  intro Λ a _ _ x₀ r hr hball u hu
  refine ⟨DGNM.blowUp u x₀ hr hball, fun y => ?_, ?_⟩
  · rw [DGNM.blowUp_toFun, add_comm]
  · rw [← coeff_blowUp_eq]
    exact DGNM.superharmonicOn_blowUp (isOpen_euclideanBall _ _) hu x₀ hr hball

theorem solAffineTransfer (d : ℕ) : SolAffineTransfer d := by
  intro Λ a _ _ x₀ r hr hball u hu s c
  have : IsFiniteMeasure (volumeOn (euclideanBall (0 : Vec d) 1)) :=
    isFiniteMeasure_volumeOn_euclideanBall _ zero_le_one
  have h1 := DGNM.solutionOn_blowUp (isOpen_euclideanBall _ _) hu x₀ hr hball
  refine ⟨((s • DGNM.blowUp u x₀ hr hball).addConst c), fun y => ?_, ?_⟩
  · simp only [H1Function.addConst_apply, H1Function.smul_toFun, DGNM.blowUp_toFun]
    rw [add_comm x₀, add_comm]
  · rw [← coeff_blowUp_eq]
    exact DGNM.solutionOn_addConst (DGNM.solutionOn_smul h1 s) c

end PDE.DGNMAssembly
