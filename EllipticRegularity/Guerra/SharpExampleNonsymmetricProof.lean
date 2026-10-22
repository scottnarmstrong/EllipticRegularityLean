module

public import PDEFoundation
public import EllipticRegularity.Guerra.Weak.Solution
public import EllipticRegularity.Guerra.Scalar.Extrema

/-!
# Proof of `PDE.guerra_sharp_example_nonsymmetric` (Corollary 4.32)

Proof of the statement `PDE.guerra_sharp_example_nonsymmetric`. The coefficient field is
the nonsymmetric `a = 2B`, elliptic with `Λ = (40γ)²`, and `a ∇u = 2J` off the origin. The scalar
conclusions come from `Guerra/Scalar/`, the PDE conclusions from `Guerra/Weak/`.
-/

@[expose] public section

open MeasureTheory

namespace PDE.GuerraSharpExampleNonsymmetricProof

open PDE.Guerra

theorem result (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : 1 ≤ γ) (Λ : ℝ)
    (hΛ : Λ = (40 * γ) ^ 2) (α : ℝ)
    (hα : α = (1 / 2) * (Real.sqrt (((d : ℝ) - 2) ^ 2 +
        4 * (2 * ((d : ℝ) - 1) * γ / Real.sinh (2 * γ)) / (400 * γ ^ 2)) - ((d : ℝ) - 2)))
    (u : Vec d → ℝ)
    (hu : u = fun x => if x = 0 then 0 else
      vecEuclideanNorm x ^ α * (Real.tanh (γ * x ⟨d - 1, by omega⟩ / vecEuclideanNorm x) /
        Real.tanh γ)) :
    ∃ a : CoeffField d,
      (∀ i j : Fin d, Measurable (fun x => a x i j)) ∧
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) ∧
      (0 < α ∧ α ≤ Real.exp (-(Real.sqrt Λ / 20))) ∧
      (ContinuousOn u (euclideanBall (0 : Vec d) 1) ∧
        (∀ x ∈ euclideanBall (0 : Vec d) 1, |u x| ≤ vecEuclideanNorm x ^ α) ∧
        (∀ s : ℝ, 0 < s → s < 1 → u (s • Pi.single ⟨d - 1, by omega⟩ 1) = s ^ α) ∧
        EuclideanHolderSeminormLE (euclideanBall (0 : Vec d) 1) u α (5 * γ)) ∧
      (∃ v : H1Function (euclideanBall (0 : Vec d) 1), v.toFun = u ∧
        IsWeakDivergenceFormH10SolutionOn a (euclideanBall (0 : Vec d) 1) v
          (0 : Vec d → ℝ) 0) ∧
      (∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∀ α' : ℝ, α < α' →
        ¬ ∃ (v : Vec d → ℝ) (M : ℝ), v =ᵐ[volumeOn (euclideanBall (0 : Vec d) ρ)] u ∧
          EuclideanHolderSeminormLE (euclideanBall (0 : Vec d) ρ) v α' M) ∧
      (∃ w : H1Function (euclideanBall (0 : Vec d) 1), w.toFun = (fun x => 1 + u x) ∧
        (∀ x ∈ euclideanBall (0 : Vec d) 1, 0 < w.toFun x) ∧
        IsWeakDivergenceFormH10SolutionOn a (euclideanBall (0 : Vec d) 1) w
          (0 : Vec d → ℝ) 0 ∧
        IsLUB (w.toFun '' euclideanBall (0 : Vec d) (1 / 2)) (1 + (1 / 2 : ℝ) ^ α) ∧
        IsGLB (w.toFun '' euclideanBall (0 : Vec d) (1 / 2)) (1 - (1 / 2 : ℝ) ^ α) ∧
        Real.exp (Real.sqrt Λ / 20) * (1 - (1 / 2 : ℝ) ^ α) ≤ 1 + (1 / 2 : ℝ) ^ α) := by
  obtain rfl : α = alpha d γ := hα
  obtain rfl : u = uProf ⟨d - 1, by omega⟩ γ (alpha d γ) := hu
  set j : Fin d := ⟨d - 1, by omega⟩ with hj
  have hP := profileData_guerra hd hγ
  have hα0 := alpha_pos hd hγ
  have hα1 := alpha_lt_one hd hγ
  have hαΛ := alpha_le_exp_sqrt_40 hd hγ hΛ
  set a : CoeffField d := nonsymField γ (hcorr d γ) j with ha
  have hEll : IsEllipticFieldOn 1 Λ (ball1 d) a := by
    rw [hΛ]; exact isEllipticFieldOn_nonsymField hd hγ j
  obtain ⟨hv, hw⟩ := weak_solutions_of_flux hd hγ j hEll (c := 2)
    (fun x hx => matVecMul_nonsymField_gradU hP j hx)
  obtain ⟨w, hwf, hwsol⟩ := hw
  refine ⟨a, measurable_nonsymField_apply (measurable_hcorr d γ) j, hEll.2, ⟨hα0, hαΛ⟩,
    ⟨(continuous_uProf j hγ hα0).continuousOn, fun x _ => abs_uProf_le j hγ hα0 x,
      fun s hs _ => uProf_ray j hγ _ hs, uProf_holder j hγ hα0 hα1.le _⟩,
    hv, fun ρ hρ _ α' hα' => uProf_not_holder j hγ hα0 hρ hα', ⟨w, hwf, ?_, hwsol, ?_, ?_,
      harnack_ratio_arith hα0 hαΛ⟩⟩
  · intro x hx
    rw [hwf]
    exact one_add_uProf_pos j hγ hα0 hx
  · rw [hwf]
    exact uProf_isLUB j hγ hα0
  · rw [hwf]
    exact uProf_isGLB j hγ hα0

end PDE.GuerraSharpExampleNonsymmetricProof
