module

public import PDEFoundation.Euler.MollifyCommute
public import PDEFoundation.Euler.MollifyCurl
public import PDEFoundation.Euler.MollifyLp
public import PDEFoundation.Euler.MollifyL2ST
public import PDEFoundation.Euler.MollifyBundle

/-!
# Periodic spatial mollification (facade)

Slice level: `mollifyVec`, `mollify_contDiff`, `mollify_periodic`, `abs_mollify_le`, `torusDiv_mollifyVec`,
`torusCurl_mollifyVec`, `tendsto_eLpNorm_mollify_cube`.  Space-time level: `mollifyVecST`,
`aestronglyMeasurable_mollifyST`, `tendsto_lintegral_sq_mollifyST`.  Space-time weak formulation to
slices: `ae_slice_div`, `ae_slice_curl`; bundles `ae_mollify_slice_div`, `ae_mollify_slice_curl`.
-/

@[expose] public section
