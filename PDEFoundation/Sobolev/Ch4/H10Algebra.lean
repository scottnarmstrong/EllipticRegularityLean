module

public import PDEFoundation.Sobolev.Ch4.H10Truncation
public import PDEFoundation.Sobolev.H1.Algebra

/-!
# Differences in `H¹₀`

`h10Sub u v` is the difference of two `H¹₀(U)` functions, carrying the difference of the
supported smooth approximations.  Consequently `min(u, t) = u - (u - t)₊` is in `H¹₀(U)` for
`t ≥ 0`.
-/

@[expose] public section

open scoped ENNReal Topology
open MeasureTheory Set Filter

namespace PDE.Ch4Infra

variable {d : ℕ} {U : Set (Vec d)}

/-- The difference of two `H¹₀(U)` functions. -/
noncomputable def h10Sub (u v : H10Function U) : H10Function U where
  toH1Function := u.toH1Function - v.toH1Function
  approx := fun n x => u.approx n x - v.approx n x
  approx_smooth := fun n => (u.approx_smooth n).sub (v.approx_smooth n)
  approx_hasCompactSupport := fun n => by
    exact (u.approx_hasCompactSupport n).sub (v.approx_hasCompactSupport n)
  approx_support_subset := fun n => by
    refine (closure_mono (Function.support_sub _ _)).trans ?_
    rw [closure_union]
    exact union_subset (u.approx_support_subset n) (v.approx_support_subset n)
  tendsto_approx := by
    have h1 := u.tendsto_approx
    have h2 := v.tendsto_approx
    have hs := h1.add h2
    rw [add_zero] at hs
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun n => bot_le)
      (fun n => ?_)
    have : (fun x => (u.approx n x - v.approx n x) - (u.toH1Function - v.toH1Function).toFun x) =
        (fun x => u.approx n x - u.toH1Function.toFun x) -
          fun x => v.approx n x - v.toH1Function.toFun x := by
      funext x; simp [H1Function.sub_toFun]; ring
    rw [this]
    exact eLpNorm_sub_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  tendsto_approx_grad := fun i => by
    have h1 := u.tendsto_approx_grad i
    have h2 := v.tendsto_approx_grad i
    have hs := h1.add h2
    rw [add_zero] at hs
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun n => bot_le)
      (fun n => ?_)
    have : (fun x => (fderiv ℝ (fun x => u.approx n x - v.approx n x) x) (basisVec i) -
        (u.toH1Function - v.toH1Function).grad x i) =
        (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i) -
          fun x => (fderiv ℝ (v.approx n) x) (basisVec i) - v.toH1Function.grad x i := by
      funext x
      rw [fderiv_fun_sub ((u.approx_smooth n).differentiable (by simp) x)
        ((v.approx_smooth n).differentiable (by simp) x)]
      simp [H1Function.sub_grad]; ring
    rw [this]
    exact eLpNorm_sub_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)

@[simp] theorem h10Sub_toH1Function (u v : H10Function U) :
    (h10Sub u v).toH1Function = u.toH1Function - v.toH1Function := rfl

/-- **`min(u, t) ∈ H¹₀`** for `u ∈ H¹₀(U)` on a bounded open set and `t ≥ 0`: the difference
`u - (u - t)₊`, with value `min (u x) t` and gradient `1_{u ≤ t} ∇u`. -/
noncomputable def minH10 (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H10Function U)
    {t : ℝ} (ht : 0 ≤ t) : H10Function U :=
  h10Sub u (positivePartH10 hU hfin u ht)

theorem minH10_toFun (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H10Function U)
    {t : ℝ} (ht : 0 ≤ t) :
    (minH10 hU hfin u ht).toH1Function.toFun = fun x => min (u.toH1Function.toFun x) t := by
  funext x
  change u.toH1Function.toFun x - max (u.toH1Function.toFun x - t) 0 = _
  rcases le_total (u.toH1Function.toFun x) t with h | h
  · rw [max_eq_right (by linarith), min_eq_left h]; ring
  · rw [max_eq_left (by linarith), min_eq_right h]; ring

theorem minH10_grad (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H10Function U)
    {t : ℝ} (ht : 0 ≤ t) :
    (minH10 hU hfin u ht).toH1Function.grad =
      fun x => {y | u.toH1Function.toFun y ≤ t}.indicator u.toH1Function.grad x := by
  funext x
  change u.toH1Function.grad x - posPartGrad u.toH1Function t x = _
  by_cases h : t < u.toH1Function.toFun x
  · simp [posPartGrad, h, not_le.2 h]
  · simp [posPartGrad, h, not_lt.1 h]

end PDE.Ch4Infra
