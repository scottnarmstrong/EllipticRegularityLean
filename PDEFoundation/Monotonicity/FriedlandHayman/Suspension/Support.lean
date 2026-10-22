module

public import PDEFoundation.Monotonicity.FriedlandHayman.Suspension.Lift
public import PDEFoundation.Monotonicity.FriedlandHayman.Suspension.RadialTgn

/-!
# Friedland--Hayman: sphere support of the lifted radial functions

If `g` vanishes on `(-∞, ε]` and the sphere support of `f` has closure inside `Ω`, then the sphere
support of `x ↦ g(|x'|) f(x'/|x'|)` has closure inside the suspension of `Ω`.
-/

@[expose] public section

open Set

namespace PDE.FHLane

noncomputable section

namespace Susp

theorem isClosed_support_aux {n N : ℕ} {ε : ℝ} (hε : 0 < ε) {K : Set (Vec n)} (hK : IsClosed K) :
    IsClosed {x : Vec (n + N) | x ∈ euclideanSphere (0 : Vec (n + N)) 1 ∧
      ε ≤ vecEuclideanNorm (projFst x) ∧ (vecEuclideanNorm (projFst x))⁻¹ • projFst x ∈ K} := by
  have hS : IsClosed (euclideanSphere (0 : Vec (n + N)) 1) := isClosed_euclideanSphere _ _
  have hnorm : Continuous fun x : Vec (n + N) => vecEuclideanNorm (projFst x) :=
    continuous_vecEuclideanNorm.comp (projL n N).continuous
  have hC : IsClosed {x : Vec (n + N) | ε ≤ vecEuclideanNorm (projFst x)} :=
    isClosed_le continuous_const hnorm
  have hcont : ContinuousOn (fun x : Vec (n + N) => (vecEuclideanNorm (projFst x))⁻¹ • projFst x)
      {x : Vec (n + N) | ε ≤ vecEuclideanNorm (projFst x)} := by
    refine ContinuousOn.smul (hnorm.continuousOn.inv₀ fun x hx => ?_) (projL n N).continuous.continuousOn
    exact (lt_of_lt_of_le hε hx).ne'
  have := hcont.preimage_isClosed_of_isClosed hC hK
  have h2 := hS.inter this
  exact h2

theorem closure_support_subset_suspension {n N : ℕ} {Ω : Set (Vec n)} {f : Vec n → ℝ} {g : ℝ → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hg0 : ∀ t, t ≤ ε → g t = 0)
    (hfΩ : closure {x | x ∈ euclideanSphere (0 : Vec n) 1 ∧ f x ≠ 0} ⊆ Ω) :
    closure {x | x ∈ euclideanSphere (0 : Vec (n + N)) 1 ∧
        radialLift g f (projFst x) ≠ 0} ⊆ suspension n N Ω := by
  set K : Set (Vec n) := closure {x | x ∈ euclideanSphere (0 : Vec n) 1 ∧ f x ≠ 0} with hK
  have hZ := isClosed_support_aux (N := N) hε (isClosed_closure (s := {x | x ∈ euclideanSphere
    (0 : Vec n) 1 ∧ f x ≠ 0}))
  have hsub : {x | x ∈ euclideanSphere (0 : Vec (n + N)) 1 ∧ radialLift g f (projFst x) ≠ 0} ⊆
      {x : Vec (n + N) | x ∈ euclideanSphere (0 : Vec (n + N)) 1 ∧
        ε ≤ vecEuclideanNorm (projFst x) ∧ (vecEuclideanNorm (projFst x))⁻¹ • projFst x ∈ K} := by
    rintro x ⟨hxS, hx⟩
    have hle : ε ≤ vecEuclideanNorm (projFst x) := by
      by_contra h
      push Not at h
      apply hx
      unfold radialLift
      rw [hg0 _ h.le, zero_mul]
    have hne : projFst x ≠ 0 := by
      intro h0
      rw [h0] at hle
      have : vecEuclideanNorm (0 : Vec n) = 0 := vecEuclideanNorm_eq_zero_iff.2 rfl
      linarith
    refine ⟨hxS, hle, subset_closure ⟨mem_euclideanSphere_iff.2 (vecNormSq_inv_smul hne), ?_⟩⟩
    intro h0
    apply hx
    unfold radialLift
    rw [h0, mul_zero]
  have hZsub : {x : Vec (n + N) | x ∈ euclideanSphere (0 : Vec (n + N)) 1 ∧
        ε ≤ vecEuclideanNorm (projFst x) ∧ (vecEuclideanNorm (projFst x))⁻¹ • projFst x ∈ K} ⊆
      suspension n N Ω := by
    rintro x ⟨hxS, hle, hxK⟩
    have hne : projFst x ≠ 0 := by
      intro h0
      rw [h0] at hle
      have : vecEuclideanNorm (0 : Vec n) = 0 := vecEuclideanNorm_eq_zero_iff.2 rfl
      linarith
    exact ⟨hxS, hne, hfΩ hxK⟩
  exact (closure_minimal hsub hZ).trans hZsub

end Susp

end

end PDE.FHLane
