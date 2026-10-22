module

public import PDEFoundation.Euler.TorusBasic
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Cube-translation invariance on the torus

For a `ℤ²`-periodic `f`, `∫_{torusCube} f (x + a) dx = ∫_{torusCube} f` for every `a`, with no
integrability hypothesis (both sides are junk-valued simultaneously). The proof compares the
fundamental domains `torusCube` and its translate for the lattice `ℤ²`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

/-- The lattice `ℤ² ⊂ Vec 2` of integer translations. -/
def torusLattice : AddSubgroup (Vec 2) :=
  (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))).toAddSubgroup

instance : Countable torusLattice :=
  inferInstanceAs (Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))))

theorem IsTorusPeriodic.add_of_mem_lattice {β : Type*} {f : Vec 2 → β} (hf : IsTorusPeriodic f)
    {γ : Vec 2} (hγ : γ ∈ torusLattice) (x : Vec 2) : f (γ + x) = f x := by
  rw [torusLattice, Submodule.span_int_eq_addSubgroupClosure] at hγ
  induction hγ using AddSubgroup.closure_induction generalizing x with
  | mem γ h =>
    obtain ⟨i, rfl⟩ := h
    rw [Pi.basisFun_apply]
    show f (basisVec i + x) = f x
    rw [add_comm]; exact hf i x
  | zero => simp
  | add a b _ _ ha hb => rw [add_assoc, ha, hb]
  | neg a _ ha =>
    have := ha (-a + x)
    rw [add_neg_cancel_left] at this
    exact this.symm

theorem torusCube_ae_eq_fundamentalDomain :
    ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 2)) =ᵐ[volume] torusCube := by
  have := ZSpan.fundamentalDomain_ae_parallelepiped (Pi.basisFun ℝ (Fin 2)) (volume : Measure (Vec 2))
  have h2 : parallelepiped (Pi.basisFun ℝ (Fin 2)) = torusCube := by
    have := congrArg (fun K : TopologicalSpace.PositiveCompacts (Fin 2 → ℝ) => (K : Set (Fin 2 → ℝ)))
      (Module.Basis.parallelepiped_basisFun (Fin 2))
    refine this.trans ?_
    show (Set.pi Set.univ fun _ : Fin 2 => Icc (0 : ℝ) 1) = torusCube
    rw [Set.pi_univ_Icc]; rfl
  rwa [h2] at this

/-- **Cube-translation invariance.** -/
theorem IsTorusPeriodic.setIntegral_cube_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Vec 2 → E} (hf : IsTorusPeriodic f) (a : Vec 2) :
    ∫ x in torusCube, f (x + a) = ∫ x in torusCube, f x := by
  set D := ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 2)) with hDdef
  have hD : IsAddFundamentalDomain torusLattice D volume :=
    ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin 2)) volume
  have hmp := measurePreserving_add_right (volume : Measure (Vec 2)) a
  have ht : IsAddFundamentalDomain torusLattice ((fun x => x + a) ⁻¹' D) volume :=
    hD.preimage_of_equiv (e := id) hmp.quasiMeasurePreserving Function.bijective_id
      (fun g x => by
        show (g : Vec 2) + x + a = (g : Vec 2) + (x + a)
        rw [add_assoc])
  have hinv : ∀ (g : torusLattice) (x : Vec 2), f ((g +ᵥ x) + a) = f (x + a) := fun g x => by
    show f (((g : Vec 2) + x) + a) = f (x + a)

    rw [add_assoc]
    exact hf.add_of_mem_lattice g.2 _
  have hinvf : ∀ (g : torusLattice) (x : Vec 2), f (g +ᵥ x) = f x := fun g x =>
    hf.add_of_mem_lattice g.2 x
  calc ∫ x in torusCube, f (x + a) = ∫ x in D, f (x + a) :=
        (setIntegral_congr_set torusCube_ae_eq_fundamentalDomain).symm
    _ = ∫ x in (fun x => x + a) ⁻¹' D, f (x + a) := hD.setIntegral_eq ht hinv
    _ = ∫ x in D, f x :=
        hmp.setIntegral_preimage_emb (measurableEmbedding_addRight a) f D
    _ = ∫ x in torusCube, f x := setIntegral_congr_set torusCube_ae_eq_fundamentalDomain

end PDE
