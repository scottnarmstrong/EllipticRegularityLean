module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-! # Hahn--Banach through an injective linear map with its induced norm -/

@[expose] public section

namespace PDE
noncomputable section

/-- Equip a module with the norm pulled back by an injective linear map.
Every continuous scalar functional then has an extension to the target with
exactly the same norm. The range transfer and Hahn--Banach extension are
constructed internally; neither extension nor a norm bound is assumed. -/
theorem exists_extension_through_injective_linearMap
    {E V : Type*} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : E →ₗ[ℝ] V) (hA : Function.Injective A) :
    letI : NormedAddCommGroup E := NormedAddCommGroup.induced E V A hA
    letI : NormedSpace ℝ E := NormedSpace.induced ℝ E V A
    ∀ L : E →L[ℝ] ℝ, ∃ J : V →L[ℝ] ℝ,
      (∀ u : E, J (A u) = L u) ∧ ‖J‖ = ‖L‖ := by
  let : NormedAddCommGroup E := NormedAddCommGroup.induced E V A hA
  let : NormedSpace ℝ E := NormedSpace.induced ℝ E V A
  intro L
  let e : E ≃ₗᵢ[ℝ] LinearMap.range A :=
    { LinearEquiv.ofInjective A hA with norm_map' := fun _ => rfl }
  let Lrange : LinearMap.range A →L[ℝ] ℝ :=
    L.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  rcases exists_extension_norm_eq (LinearMap.range A) Lrange with ⟨J, hRep, hNorm⟩
  refine ⟨J, ?_, ?_⟩
  · intro u
    have h := hRep (e u)
    change J (↑(e u)) = L (e.symm (e u)) at h
    rw [e.symm_apply_apply] at h
    exact h
  · rw [hNorm]
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
      intro v
      change ‖L (e.symm v)‖ ≤ ‖L‖ * ‖v‖
      rw [← e.symm.norm_map v]
      exact L.le_opNorm _
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Lrange)
      intro u
      have h := Lrange.le_opNorm (e u)
      change ‖L (e.symm (e u))‖ ≤ ‖Lrange‖ * ‖e u‖ at h
      rw [e.symm_apply_apply, e.norm_map] at h
      exact h

end

end PDE
