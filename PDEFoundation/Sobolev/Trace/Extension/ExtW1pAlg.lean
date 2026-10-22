module

public import PDEFoundation.Sobolev.Trace.Extension.ExtW1pDef
import PDEFoundation.Sobolev.Trace.Chart.Surface

/-!
# Linearity of `ExtData.extW1p`

On the Besov class the map `g ↦ extW1p g` is additive and homogeneous as a map into the module
`W^{1,p}(Ω)`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))} {p : ℝ}

theorem ExtData.differentiableAt_ext (D : ExtData Ω) (hΩo : IsOpen Ω) (hp : 1 < p)
    {g : Vec (n + 1) → ℝ} (hg : IsBesov Ω (1 - 1 / p) p g) {x : Vec (n + 1)} (hx : x ∈ Ω) :
    DifferentiableAt ℝ (D.ext g) x :=
  ((D.ext_contDiffOn hp hg).differentiableOn one_ne_zero).differentiableAt (hΩo.mem_nhds hx)

theorem ExtData.extW1p_add [Fact (1 ≤ ENNReal.ofReal p)] (D : ExtData Ω) (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (hp : 1 < p) {g h : Vec (n + 1) → ℝ}
    (hg : IsBesov Ω (1 - 1 / p) p g) (hh : IsBesov Ω (1 - 1 / p) p h) :
    D.extW1p hΩo hΩb hp (g + h) = D.extW1p hΩo hΩb hp g + D.extW1p hΩo hΩb hp h := by
  have := boundarySurfaceMeasure_isFiniteMeasure D.A hΩb
  have hgh : IsBesov Ω (1 - 1 / p) p (g + h) := IsBesov.add hp hg hh
  refine W1pFunction.ext ?_ ?_
  · funext x
    rw [D.extW1p_toFun hΩo hΩb hp hgh, D.ext_add hp hg hh, W1pFunction.add_toFun]
    simp only [Pi.add_apply]
    rw [show (D.extW1p hΩo hΩb hp g) x = (D.extW1p hΩo hΩb hp g).toFun x from rfl,
      show (D.extW1p hΩo hΩb hp h) x = (D.extW1p hΩo hΩb hp h).toFun x from rfl,
      D.extW1p_toFun hΩo hΩb hp hg, D.extW1p_toFun hΩo hΩb hp hh]
  · funext x
    rw [W1pFunction.add_grad]
    beta_reduce
    by_cases hx : x ∈ Ω
    · rw [D.extW1p_grad hΩo hΩb hp hgh hx, D.extW1p_grad hΩo hΩb hp hg hx,
        D.extW1p_grad hΩo hΩb hp hh hx, D.ext_add hp hg hh]
      funext i
      simp [classicalGradient, fderiv_add (D.differentiableAt_ext hΩo hp hg hx)
        (D.differentiableAt_ext hΩo hp hh hx)]
    · rw [D.extW1p_grad_eq hΩo hΩb hp hgh, D.extW1p_grad_eq hΩo hΩb hp hg,
        D.extW1p_grad_eq hΩo hΩb hp hh, D.extGrad_of_notMem _ hx, D.extGrad_of_notMem _ hx,
        D.extGrad_of_notMem _ hx]
      simp

theorem ExtData.extW1p_smul (D : ExtData Ω) (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hp : 1 < p) (a : ℝ) {g : Vec (n + 1) → ℝ} (hg : IsBesov Ω (1 - 1 / p) p g) :
    D.extW1p hΩo hΩb hp (a • g) = a • D.extW1p hΩo hΩb hp g := by
  have := boundarySurfaceMeasure_isFiniteMeasure D.A hΩb
  have hag : IsBesov Ω (1 - 1 / p) p (a • g) := IsBesov.smul hp a hg
  refine W1pFunction.ext ?_ ?_
  · funext x
    rw [D.extW1p_toFun hΩo hΩb hp hag, D.ext_smul, W1pFunction.smul_toFun]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (D.extW1p hΩo hΩb hp g) x = (D.extW1p hΩo hΩb hp g).toFun x from rfl,
      D.extW1p_toFun hΩo hΩb hp hg]
  · funext x
    rw [W1pFunction.smul_grad]
    beta_reduce
    by_cases hx : x ∈ Ω
    · rw [D.extW1p_grad hΩo hΩb hp hag hx, D.extW1p_grad hΩo hΩb hp hg hx, D.ext_smul]
      funext i
      simp [classicalGradient, fderiv_const_smul (D.differentiableAt_ext hΩo hp hg hx)]
    · rw [D.extW1p_grad_eq hΩo hΩb hp hag, D.extW1p_grad_eq hΩo hΩb hp hg,
        D.extGrad_of_notMem _ hx, D.extGrad_of_notMem _ hx]
      simp

end PDE.TraceLane
