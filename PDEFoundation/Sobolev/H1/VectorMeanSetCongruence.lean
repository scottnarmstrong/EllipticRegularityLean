module

public import PDEFoundation.Sobolev.H1.VectorMeanRestriction

@[expose] public section

namespace PDE
open MeasureTheory

/-- Centered mean oscillation depends only on the domain modulo volume-null sets. -/
theorem centeredVectorMeanL2_congr_set_ae
    {d : ℕ} {U V : Set (Vec d)} (hUV : U =ᵐ[volume] V)
    (g : Vec d → Vec d) :
    centeredVectorMeanL2 U g = centeredVectorMeanL2 V g := by
  have hmeasure := Measure.restrict_congr_set hUV
  have hvolume : volume U = volume V := measure_congr hUV
  have hmean : vectorIntegralAverage U g = vectorIntegralAverage V g := by
    ext i
    simp only [vectorIntegralAverage_apply, integralAverage, hvolume, hmeasure]
  simp only [centeredVectorMeanL2, hmean, integralAverage, hvolume, hmeasure]

/-- Coordinate L2 membership transports across domains equal almost everywhere. -/
theorem memVectorL2On_congr_set_ae
    {d : ℕ} {U V : Set (Vec d)} (hUV : U =ᵐ[volume] V)
    (g : Vec d → Vec d) :
    MemVectorL2On U g ↔ MemVectorL2On V g := by
  simp only [MemVectorL2On, GradMemL2On, GradMemLpOn, MemLpOn, volumeOn,
    Measure.restrict_congr_set hUV]

end PDE
