module

public import PDEFoundation.Sobolev.Ch4.Local
public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.WeakDerivative.Congruence

/-!
# Extension by zero of a compactly supported `H¹` function

If an `H¹(U)` function vanishes outside a compact subset `K` of the open set `U`, its literal
zero extension to the whole space has the same coordinate weak gradient (also extended by zero)
on `ℝ^d`.  The proof is by locality (`hasWeakPartialDerivOn_of_local`): on `U` nothing changes,
and on the open set `Kᶜ` both the function and its gradient vanish a.e.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Ch4Infra

variable {d : ℕ} {U : Set (Vec d)}

theorem hasWeakPartialDerivOn_of_zero {V : Set (Vec d)} (i : Fin d) {f g : Vec d → ℝ}
    (hf : ∀ x ∈ V, f x = 0) (hg : ∀ᵐ x ∂(volume.restrict V), g x = 0) :
    HasWeakPartialDerivOn V i f g := by
  intro φ _ _ _
  have h1 : ∫ x in V, f x * (fderiv ℝ φ x) (basisVec i) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun x hx => by simp [hf x hx]
  have h2 : ∫ x in V, g x * φ x = 0 :=
    integral_eq_zero_of_ae (hg.mono fun x hx => by simp [hx])
  rw [h1, h2, neg_zero]

/-- A weak gradient of a function vanishing on an open set vanishes a.e. there. -/
theorem grad_ae_zero_of_zero {V : Set (Vec d)} (hV : IsOpen V) (i : Fin d) {f g : Vec d → ℝ}
    (hf : ∀ x ∈ V, f x = 0) (hg : LocallyIntegrableOn g V volume)
    (h : HasWeakPartialDerivOn V i f g) : ∀ᵐ x ∂(volume.restrict V), g x = 0 := by
  have h0 : HasWeakPartialDerivOn V i f (fun _ => (0 : ℝ)) :=
    hasWeakPartialDerivOn_of_zero i hf (Filter.Eventually.of_forall fun _ => rfl)
  exact HasWeakPartialDerivOn.ae_eq hV hg (locallyIntegrableOn_const _) h h0

/-- **Zero extension of a compactly supported `H¹` function.** -/
theorem hasWeakPartialDerivOn_univ_zeroExtend (hU : IsOpen U) (f : H1Function U)
    {K : Set (Vec d)} (hKU : K ⊆ U) (hK : IsCompact K)
    (hf0 : ∀ x ∈ U, x ∉ K → f.toFun x = 0) (i : Fin d) :
    HasWeakPartialDerivOn Set.univ i (U.indicator f.toFun)
      (U.indicator (fun x => f.grad x i)) := by
  have hf2 : MemLp (U.indicator f.toFun) 2 volume :=
    (memLp_indicator_iff_restrict hU.measurableSet).2 f.memL2
  have hg2 : MemLp (U.indicator (fun x => f.grad x i)) 2 volume :=
    (memLp_indicator_iff_restrict hU.measurableSet).2 (f.gradMemL2 i)
  refine hasWeakPartialDerivOn_of_local isOpen_univ
    ((hf2.locallyIntegrable (by norm_num)).locallyIntegrableOn _)
    ((hg2.locallyIntegrable (by norm_num)).locallyIntegrableOn _) ?_
  intro x _
  by_cases hxU : x ∈ U
  · refine ⟨U, hU, hxU, subset_univ _, ?_⟩
    intro φ hφ hφc hφU
    have h := f.hasWeakPartialDerivOn i φ hφ hφc hφU
    rw [setIntegral_congr_fun hU.measurableSet (g := fun x => f.toFun x * (fderiv ℝ φ x) (basisVec i))
        (fun y hy => by simp [Set.indicator_of_mem hy]),
      h]
    congr 1
    exact setIntegral_congr_fun hU.measurableSet (fun y hy => by simp [Set.indicator_of_mem hy])
  · have hxK : x ∉ K := fun h => hxU (hKU h)
    refine ⟨Kᶜ, hK.isClosed.isOpen_compl, hxK, subset_univ _, ?_⟩
    have hW : IsOpen (U ∩ Kᶜ) := hU.inter hK.isClosed.isOpen_compl
    have hgrad : ∀ᵐ y ∂(volume.restrict (U ∩ Kᶜ)), f.grad y i = 0 := by
      refine grad_ae_zero_of_zero hW i (fun y hy => hf0 y hy.1 hy.2)
        (locallyIntegrableOn_of_locallyIntegrable_restrict
          ((f.gradMemL2 i).locallyIntegrable (by norm_num)) |>.mono_set inter_subset_left)
        ((f.hasWeakPartialDerivOn i).restrict hW inter_subset_left)
    apply hasWeakPartialDerivOn_of_zero
    · intro y hy
      by_cases hyU : y ∈ U
      · simp [Set.indicator_of_mem hyU, hf0 y hyU hy]
      · simp [Set.indicator_of_notMem hyU]
    · rw [ae_restrict_iff' hK.isClosed.isOpen_compl.measurableSet]
      have := (ae_restrict_iff' hW.measurableSet).1 hgrad
      filter_upwards [this] with y hy hyK
      by_cases hyU : y ∈ U
      · simp [Set.indicator_of_mem hyU, hy ⟨hyU, hyK⟩]
      · simp [Set.indicator_of_notMem hyU]

end PDE.Ch4Infra
