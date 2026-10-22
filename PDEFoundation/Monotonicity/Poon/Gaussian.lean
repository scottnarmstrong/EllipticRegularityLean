module

public import PDEFoundation.Monotonicity.Poon.GaussianDeriv
public import PDEFoundation.Monotonicity.Poon.GaussianIntegrable

/-!
# Heat kernel Gaussian facts for Poon's monotonicity formula (facade)

Re-exports `GaussianDeriv` (derivatives, `∂_s Φ = ΔΦ`, smoothness) and `GaussianIntegrable`
(positivity, Gaussian integrability, locally uniform domination bundle).
-/

@[expose] public section
