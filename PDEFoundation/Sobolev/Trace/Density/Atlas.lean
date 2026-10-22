module

public import PDEFoundation.Sobolev.Trace.Density.Pieces
public import PDEFoundation.Sobolev.W1p.Product

/-!
# Density of smooth functions in `W^{1,p}(Ω)` via a trace atlas

Evans §5.3.3: with the partition `ζ₀ = 1 - ∑ ζⱼ`, `ζⱼ` of a trace atlas, write
`u = (u - ∑ⱼ ζⱼ u) + ∑ⱼ ζⱼ u`.  The first summand vanishes on `V`, the others vanish off the chart
cylinders; each is approximable by `Pieces.lean`, and `ApproxW1p` is closed under sums.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Filter Set Topology
open scoped ENNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

theorem w1pFunction_sum_toFun_apply {p : ENNReal} [Fact (1 ≤ p)] {ι : Type*} (s : Finset ι)
    (v : ι → W1pFunction Ω p) (x : Vec (n + 1)) :
    (∑ j ∈ s, v j).toFun x = ∑ j ∈ s, (v j).toFun x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl

theorem w1pFunction_sum_grad_apply {p : ENNReal} [Fact (1 ≤ p)] {ι : Type*} (s : Finset ι)
    (v : ι → W1pFunction Ω p) (x : Vec (n + 1)) :
    (∑ j ∈ s, v j).grad x = ∑ j ∈ s, (v j).grad x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl

theorem TraceAtlas.sum_classicalGradient_eq_zero (A : TraceAtlas Ω) {x : Vec (n + 1)}
    (hx : x ∈ A.V) : ∑ j, classicalGradient (A.ζ j) x = 0 := by
  have hev : (fun y => ∑ j, A.ζ j y) =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
    Filter.eventually_of_mem (A.V_open.mem_nhds hx) fun y hy => A.sum_eq_one y hy
  have h1 := hev.fderiv_eq (𝕜 := ℝ)
  have hd : ∀ j ∈ (Finset.univ : Finset (Fin A.N)), DifferentiableAt ℝ (A.ζ j) x :=
    fun j _ => ((A.ζ_smooth j).differentiable (by simp)) x
  rw [fderiv_fun_sum hd] at h1
  funext i
  have h2 := congrArg (fun L => L (basisVec i)) h1
  simp only [fderiv_fun_const, Pi.zero_apply, zero_apply,
    sum_apply] at h2
  simpa [classicalGradient] using h2

/-- **Density of smooth functions in `W^{1,p}(Ω)`.** -/
theorem exists_approxW1p (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (A : TraceAtlas Ω)
    {p : ℝ} (hp : 1 ≤ p) (u : W1pFunction Ω (ENNReal.ofReal p)) : ApproxW1p Ω p u := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  let uj : Fin A.N → W1pFunction Ω (ENNReal.ofReal p) := fun j =>
    u.mulContDiffHasCompactSupport (A.ζ_smooth j) (A.ζ_compact j)
  have hS : ApproxW1p Ω p (∑ j, uj j) := by
    refine ApproxW1p.sum hp _ _ fun j _ => ?_
    refine approxW1p_of_vanishing_chart hΩo hΩb A hp j (uj j) (fun x _ hx => ?_)
      (fun x _ hx => ?_)
    · simp [uj, image_eq_zero_of_notMem_tsupport hx]
    · funext i
      have h0 : fderiv ℝ (A.ζ j) x (basisVec i) = 0 := fderiv_eq_zero_of_notMem_tsupport hx i
      simp [uj, image_eq_zero_of_notMem_tsupport hx, h0]
  have h0 : ApproxW1p Ω p (u - ∑ j, uj j) := by
    refine approxW1p_of_vanishing_interior hΩo hΩb A hp _ (fun x _ hx => ?_) (fun x _ hx => ?_)
    · have h1 : ∑ j, A.ζ j x = 1 := A.sum_eq_one x hx
      have h2 : (u - ∑ j, uj j).toFun x = u.toFun x - ∑ j, A.ζ j x * u.toFun x := by
        change u.toFun x - (∑ j, uj j).toFun x = _
        rw [w1pFunction_sum_toFun_apply]
        simp [uj]
      rw [h2, ← Finset.sum_mul, h1]; ring
    · have h1 : ∑ j, A.ζ j x = 1 := A.sum_eq_one x hx
      have h2 : (u - ∑ j, uj j).grad x = u.grad x - ∑ j, (A.ζ j x • u.grad x +
          u.toFun x • classicalGradient (A.ζ j) x) := by
        change u.grad x - (∑ j, uj j).grad x = _
        rw [w1pFunction_sum_grad_apply]
        simp [uj]
      rw [h2, Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.smul_sum, h1,
        A.sum_classicalGradient_eq_zero hx]
      simp
  have := h0.add hp hS
  rwa [sub_add_cancel] at this

/-- **Density of smooth functions in `W^{1,p}(Ω)`** for a bounded open set with a trace atlas. -/
theorem densityProp (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (A : TraceAtlas Ω) {p : ℝ}
    (hp : 1 < p) : DensityProp Ω p := by
  intro u
  have happrox := exists_approxW1p hΩo hΩb A hp.le u
  have hεpos : ∀ k : ℕ, 0 < ((k : ℝ≥0∞))⁻¹ := fun k => ENNReal.inv_pos.2 (ENNReal.natCast_ne_top k)
  choose φ hφ hlt using fun k : ℕ => happrox _ (hεpos k)
  refine ⟨φ, fun k => (hφ k).of_le (by exact_mod_cast le_top), ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ENNReal.tendsto_inv_nat_nhds_zero (fun _ => bot_le) fun k => (hlt k).le

end PDE.TraceLane
