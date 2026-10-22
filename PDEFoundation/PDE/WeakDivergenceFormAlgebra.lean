module

public import PDEFoundation.PDE.WeakDivergenceForm
public import PDEFoundation.Sobolev.H1.Algebra

/-! # Algebra of safe weak divergence-form equations -/

@[expose] public section

namespace PDE

open MeasureTheory

/-- Subtracting two actual weak equations with the same coefficient field
preserves all smooth-test integrability data. -/
theorem IsWeakDivergenceFormSolutionOn.sub_same_coeff
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {u v : H1Function U} {f g : Vec d → ℝ} {F G : Vec d → Vec d}
    (hu : IsWeakDivergenceFormSolutionOn a U u f F)
    (hv : IsWeakDivergenceFormSolutionOn a U v g G) :
    IsWeakDivergenceFormSolutionOn a U (u - v) (f - g) (F - G) := by
  intro φ
  have hut := hu φ
  have hvt := hv φ
  have hflux : (fun x =>
        vecDot (matVecMul (a x) ((u - v).grad x)) (φ.grad x)) =
      fun x => vecDot (matVecMul (a x) (u.grad x)) (φ.grad x) -
        vecDot (matVecMul (a x) (v.grad x)) (φ.grad x) := by
    funext x
    rw [H1Function.sub_grad]
    change vecDot ((a x).mulVec (u.grad x - v.grad x)) (φ.grad x) = _
    rw [Matrix.mulVec_sub]
    simp only [matVecMul, Matrix.mulVec, dotProduct, vecDot, Pi.sub_apply,
      sub_mul, Finset.sum_sub_distrib]
  have hsource : (fun x => (f - g) x * φ x) =
      fun x => f x * φ x - g x * φ x := by
    funext x
    simp only [Pi.sub_apply, sub_mul]
  have hforcing : (fun x => vecDot ((F - G) x) (φ.grad x)) =
      fun x => vecDot (F x) (φ.grad x) - vecDot (G x) (φ.grad x) := by
    funext x
    simp only [Pi.sub_apply, vecDot, sub_mul, Finset.sum_sub_distrib]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hflux]
    exact hut.1.flux_integrable.sub hvt.1.flux_integrable
  · rw [hsource]
    exact hut.1.source_integrable.sub hvt.1.source_integrable
  · rw [hforcing]
    exact hut.1.forcing_integrable.sub hvt.1.forcing_integrable
  · rw [hflux, hsource, hforcing,
      integral_sub hut.1.flux_integrable hvt.1.flux_integrable,
      integral_sub hut.1.source_integrable hvt.1.source_integrable,
      integral_sub hut.1.forcing_integrable hvt.1.forcing_integrable,
      hut.2, hvt.2]
    ring

/-- The difference of two solutions with the same coefficient and forcing is
an actual homogeneous weak solution. -/
theorem IsWeakDivergenceFormSolutionOn.sub_isHarmonic_same_forcing
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {u v : H1Function U} {F : Vec d → Vec d}
    (hu : IsWeakDivergenceFormSolutionOn a U u 0 F)
    (hv : IsWeakDivergenceFormSolutionOn a U v 0 F) :
    IsWeakDivergenceFormSolutionOn a U (u - v) 0 0 := by
  simpa using hu.sub_same_coeff hv

end PDE
