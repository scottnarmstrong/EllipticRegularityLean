module

public import PDEFoundation
public import EllipticRegularity.Guerra.Weak.Example

/-!
# Proof of `PDE.guerra_harnack_sharp` (Corollary 4.32)

Proof of the statement `PDE.guerra_harnack_sharp`: for `Λ ≥ 6400` take `γ = √Λ/80 ≥ 1`,
so that `Λ = (80γ)²`, and use the example `PDE.Guerra.sharp_example` with
`w = 1 + u`, `M = 1 + 2^{-α}`, `m = 1 - 2^{-α} > 0`.
-/

@[expose] public section

open MeasureTheory

namespace PDE.GuerraHarnackSharpProof

open PDE.Guerra

theorem result (d : ℕ) (hd : 3 ≤ d) (Λ : ℝ) (hΛ : 6400 ≤ Λ) :
    ∃ a : CoeffField d,
      (∀ i j : Fin d, Measurable (fun x => a x i j)) ∧
      (∀ x : Vec d, ∀ i j : Fin d, a x i j = a x j i) ∧
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) ∧
      ∃ w : H1Function (euclideanBall (0 : Vec d) 1),
        ContinuousOn w.toFun (euclideanBall (0 : Vec d) 1) ∧
        (∀ x ∈ euclideanBall (0 : Vec d) 1, 0 < w.toFun x) ∧
        IsWeakDivergenceFormH10SolutionOn a (euclideanBall (0 : Vec d) 1) w
          (0 : Vec d → ℝ) 0 ∧
        ∃ M m : ℝ, IsLUB (w.toFun '' euclideanBall (0 : Vec d) (1 / 2)) M ∧
          IsGLB (w.toFun '' euclideanBall (0 : Vec d) (1 / 2)) m ∧ 0 < m ∧
          Real.exp (Real.sqrt Λ / 40) * m ≤ M := by
  set γ : ℝ := Real.sqrt Λ / 80 with hγdef
  have hsq : (80 : ℝ) ≤ Real.sqrt Λ := by
    rw [show (80 : ℝ) = Real.sqrt (80 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have hγ : 1 ≤ γ := by rw [hγdef]; linarith
  have hΛγ : Λ = (80 * γ) ^ 2 := by
    rw [hγdef, show 80 * (Real.sqrt Λ / 80) = Real.sqrt Λ by ring,
      Real.sq_sqrt (by linarith)]
  obtain ⟨a, hmeas, hsymm, hell, ⟨hα0, _⟩, ⟨hcont, _, _, _⟩, _, _,
      ⟨w, hwf, hpos, hsol, hlub, hglb, hratio⟩⟩ :=
    sharp_example d hd γ hγ Λ hΛγ (alpha d γ) rfl
      (uProf ⟨d - 1, by omega⟩ γ (alpha d γ)) rfl
  refine ⟨a, hmeas, hsymm, hell, w, ?_, hpos, hsol, _, _, hlub, hglb, ?_, hratio⟩
  · rw [hwf]
    exact continuousOn_const.add hcont
  · have : (1 / 2 : ℝ) ^ alpha d γ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα0
    linarith

end PDE.GuerraHarnackSharpProof
