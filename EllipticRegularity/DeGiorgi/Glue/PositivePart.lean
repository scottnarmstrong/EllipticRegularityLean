module

public import EllipticRegularity.DeGiorgi.MoserIter.Hypotheses
public import PDEFoundation.PDE.DGNM.PositivePart

/-!
# Glue: the positive part of a subsolution

Discharges the interface hypothesis `PositivePartSubsolutionHyp` of the Moser iteration from
the toolbox lemma `subharmonicOn_positivePartSubConst`.
-/

@[expose] public section

namespace PDE.DGNMGlue

theorem positivePartSubsolution (d : ℕ) : PDE.DGNMMoser.PositivePartSubsolutionHyp d :=
  fun _ _ ha hEll _ hsub =>
    PDE.DGNM.subharmonicOn_positivePartSubConst
      (isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) one_pos) ha hEll hsub 0

end PDE.DGNMGlue
