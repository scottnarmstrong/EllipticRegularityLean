module

public import PDEFoundation.Ambient.Basis
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Fubini on the unit cube, peeling one coordinate

`setIntegral_cube_peel`: for `g` integrable on `[0,1]^(n+1)`, the integral over the cube is the
iterated integral with coordinate `i` innermost over `[0,1]`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

/-- Peeling a coordinate off the unit cube. -/
theorem setIntegral_cube_peel {n : ℕ} (i : Fin (n + 1)) {g : Vec (n + 1) → ℝ}
    (hg : IntegrableOn g (Icc (0 : Vec (n + 1)) 1)) :
    ∫ x in Icc (0 : Vec (n + 1)) 1, g x =
      ∫ z in Icc (0 : Vec n) 1, ∫ t in Icc (0 : ℝ) 1, g (i.insertNth t z) := by
  classical
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hmp : MeasurePreserving e.symm
      ((volume : Measure ℝ).prod (volume : Measure (Vec n))) (volume : Measure (Vec (n + 1))) :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  have hset : e.symm ⁻¹' Icc (0 : Vec (n + 1)) 1 = Icc (0 : ℝ) 1 ×ˢ Icc (0 : Vec n) 1 := by
    ext ⟨t, z⟩
    simp only [mem_preimage, mem_prod, mem_Icc, Pi.le_def, Pi.zero_apply, Pi.one_apply]
    rw [Fin.forall_iff_succAbove i, Fin.forall_iff_succAbove i]
    have h1 : e.symm (t, z) i = t := by simp [e]
    have h2 : ∀ k, e.symm (t, z) (i.succAbove k) = z k := by simp [e]
    simp only [h1, h2]
    tauto
  have hint : IntegrableOn (fun p => g (e.symm p)) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : Vec n) 1)
      ((volume : Measure ℝ).prod (volume : Measure (Vec n))) := by
    rw [← hset]
    exact (hmp.integrableOn_comp_preimage e.symm.measurableEmbedding).2 hg
  rw [← hmp.setIntegral_preimage_emb e.symm.measurableEmbedding g, hset]
  rw [← Measure.prod_restrict] 
  have hint' : Integrable (fun p => g (e.symm p))
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : Vec n) 1))) := by
    rw [Measure.prod_restrict]; exact hint
  rw [integral_prod_symm _ hint']
  rfl

end PDE
