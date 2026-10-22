module

public import EllipticRegularity.Euler.WeakGradient
public import PDEFoundation.Euler.Mollify

/-!
# The weak gradient of `v₂(·,t)` for a.e. `t`

`IsTorusWeakGradient v G` says that `G = (∂ⱼvᵢ)` is the weak periodic gradient of `v` on the cube.

* `exists_torus_weak_gradient`: slice level.  If the periodic mollifications `v^{aₙ}` (`aₙ → 0`) are smooth,
  periodic, divergence free, with `curl v^{aₙ} = ω^{aₙ}` and `|ω^{aₙ}| ≤ M`, and `v, ω ∈ L²(cube)` are periodic,
  then `v` has a weak gradient `G`, `∇v^{aₙ} → G` in `L²(cube)` and `‖G‖_{L^p(cube)} ≤ K p M` for all `p ≥ 2`.
* `ae_exists_weak_gradient`: the same for a.e. time slice of a bounded weak Euler solution with bounded
  vorticity `ω` (the hypotheses are those of the bundles `ae_mollify_slice_div`, `ae_mollify_slice_curl`),
  with `ω(·,t)` replaced by its periodic extension.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE

/-- `G = (∂ⱼvᵢ)ᵢⱼ` is the weak gradient of the periodic field `v` on the torus:
`∫_{cube} vᵢ ∂ⱼψ = -∫_{cube} Gᵢⱼ ψ` for all smooth periodic `ψ`. -/
def IsTorusWeakGradient (v : Vec 2 → Vec 2) (G : Vec 2 → Fin 2 → Fin 2 → ℝ) : Prop :=
  ∀ (i j : Fin 2) (ψ : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → IsTorusPeriodic ψ →
    ∫ x in torusCube, v x i * pd j ψ x = -∫ x in torusCube, G x i j * ψ x

/-- Slice-level periodic `W^{1,p}` regularity from a mollification family; `K` is absolute. -/
theorem exists_torus_weak_gradient :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (v : Vec 2 → Vec 2) (ω : Vec 2 → ℝ) (M : ℝ) (a : ℕ → ℝ),
      IsTorusPeriodic v → (∀ i, MemLp (fun x => v x i) 2 (volume.restrict torusCube)) →
      IsTorusPeriodic ω → MemLp ω 2 (volume.restrict torusCube) →
      (∀ n, 0 < a n) → (∀ n, a n ≤ 1) → Tendsto a atTop (𝓝 0) →
      (∀ n, (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => mollifyVec (a n) v x i)) ∧
        IsTorusPeriodic (mollifyVec (a n) v) ∧ ∀ x, torusDiv (mollifyVec (a n) v) x = 0) →
      (∀ n, (∀ x, torusCurl (mollifyVec (a n) v) x = mollify (a n) ω x) ∧
        ∀ x, |mollify (a n) ω x| ≤ M) →
      ∃ G : Vec 2 → Fin 2 → Fin 2 → ℝ,
        (∀ i j, MemLp (fun x => G x i j) 2 (volume.restrict torusCube)) ∧
        Tendsto (fun n => eLpNorm (fun x => gradMat (mollifyVec (a n) v) x - G x) 2
          (volume.restrict torusCube)) atTop (𝓝 0) ∧
        IsTorusWeakGradient v G ∧
        ∀ p : ℝ, 2 ≤ p →
          MemLp (fun x => matFrobNorm (G x)) (ENNReal.ofReal p) (volume.restrict torusCube) ∧
          eLpNorm (fun x => matFrobNorm (G x)) (ENNReal.ofReal p) (volume.restrict torusCube) ≤
            ENNReal.ofReal (K * p * M) := by
  obtain ⟨K, hK, hmain⟩ := exists_weak_gradient_of_smooth_seq
  refine ⟨K, hK, ?_⟩
  intro v ω M a hvp hvL2 hωp hωL2 ha ha1 ha0 hsm hcm
  refine hmain (fun n => mollifyVec (a n) v) v ω M (fun n => (hsm n).1) (fun n => (hsm n).2.1)
    (fun n => (hsm n).2.2) (fun n x => by rw [(hcm n).1 x]; exact (hcm n).2 x) ?_ hvL2 ?_
  · have h := tendsto_eLpNorm_mollify_cube hωp hωL2 ha ha1 ha0
    refine h.congr fun n => ?_
    congr 1
    funext x
    rw [(hcm n).1 x]
  · intro i
    exact tendsto_eLpNorm_mollify_cube (hvp.comp (fun w => w i)) (hvL2 i) ha ha1 ha0

end PDE
