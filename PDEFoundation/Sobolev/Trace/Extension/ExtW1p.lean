module

public import PDEFoundation.Sobolev.Trace.Extension.ExtExists
public import PDEFoundation.Sobolev.Trace.Extension.ExtBesov
public import PDEFoundation.Sobolev.Trace.Extension.ExtLinear
public import PDEFoundation.Sobolev.Trace.Extension.ExtC1
public import PDEFoundation.Sobolev.Trace.Extension.ExtBound
public import PDEFoundation.Sobolev.Trace.Extension.ExtW1pDef
public import PDEFoundation.Sobolev.Trace.Extension.ExtW1pAlg

/-!
# The extension operator as a bounded linear map into `W^{1,p}(Ω)` (facade)

* `exists_extData`: every trace atlas carries extension data (`ExtExists`),
* `IsBesov.add`, `IsBesov.smul`: the Besov class is a vector space (`ExtBesov`),
* `ExtData.ext_add`, `ExtData.ext_smul`: linearity on the Besov class (`ExtLinear`),
* `ExtData.ext_contDiffOn`: `E g ∈ C¹(Ω)` (`ExtC1`),
* `ExtData.ext_bound`: `‖E g‖_{W^{1,p}(Ω)} ≤ C ‖g‖_{B}` (`ExtBound`),
* `ExtData.extW1p` and its `toFun`, `grad`, `bound` (`ExtW1pDef`), `add`, `smul` (`ExtW1pAlg`).
-/

@[expose] public section
