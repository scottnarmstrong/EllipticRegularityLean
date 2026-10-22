module

public import EllipticRegularity.Guerra.Weak.Solution
public import EllipticRegularity.Guerra.Scalar.Extrema
public import EllipticRegularity.Guerra.Symmetrize.Result

/-!
# Guerra's explicit example: the full statement  (Proposition 4.30)

The statement of the `PDE.guerra_sharp_example`, proved here so that other Guerra modules
can use it. The coefficient field
is `a = 80γ S(B/(20γ), ∇u)` off the origin (`a(0) = 2·1`), with the symmetrizer `S` of
`PDE.GuerraSymmetrizeProof.symmetrizer_exists` at `k = 40γ`; then `a ∇u = 4 B ∇u = 4 J` off the
origin. The scalar conclusions come from `Guerra/Scalar/`, the PDE conclusions from `Guerra/Weak/`.
-/

@[expose] public section

open MeasureTheory

namespace PDE.Guerra

theorem sharp_example (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : 1 ≤ γ) (Λ : ℝ)
    (hΛ : Λ = (80 * γ) ^ 2) (α : ℝ)
    (hα : α = (1 / 2) * (Real.sqrt (((d : ℝ) - 2) ^ 2 +
        4 * (2 * ((d : ℝ) - 1) * γ / Real.sinh (2 * γ)) / (400 * γ ^ 2)) - ((d : ℝ) - 2)))
    (u : Vec d → ℝ)
    (hu : u = fun x => if x = 0 then 0 else
      vecEuclideanNorm x ^ α * (Real.tanh (γ * x ⟨d - 1, by omega⟩ / vecEuclideanNorm x) /
        Real.tanh γ)) :
    ∃ a : CoeffField d,
      (∀ i j : Fin d, Measurable (fun x => a x i j)) ∧
      (∀ x : Vec d, ∀ i j : Fin d, a x i j = a x j i) ∧
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) ∧
      (0 < α ∧ α ≤ Real.exp (-(Real.sqrt Λ / 40))) ∧
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
        Real.exp (Real.sqrt Λ / 40) * (1 - (1 / 2 : ℝ) ^ α) ≤ 1 + (1 / 2 : ℝ) ^ α) := by
  obtain rfl : α = alpha d γ := hα
  obtain rfl : u = uProf ⟨d - 1, by omega⟩ γ (alpha d γ) := hu
  set j : Fin d := ⟨d - 1, by omega⟩ with hj
  have hP := profileData_guerra hd hγ
  have hα0 := alpha_pos hd hγ
  have hα1 := alpha_lt_one hd hγ
  have hh : ∀ t, |t| ≤ 1 → |hcorr d γ t| ≤ 10 * γ := fun _ ht => abs_hcorr_le hd hγ ht
  have hαΛ := alpha_le_exp_sqrt_80 hd hγ hΛ
  -- the symmetrizer at `k = 40γ`
  obtain ⟨S, hSmeas, hS⟩ :=
    PDE.GuerraSymmetrizeProof.symmetrizer_exists d (40 * γ) (by linarith)
  have hS' : IsSymmetrizer (40 * γ) S := hS
  set G := gradU (alpha d γ) (phi γ) j with hG
  set a : CoeffField d := symField γ (hcorr d γ) j S G with ha
  have hmeas : ∀ i k : Fin d, Measurable (fun x => a x i k) := fun i k =>
    measurable_symField_apply (measurable_hcorr d γ) j hSmeas
      (measurable_gradU (continuous_phi γ hγ) j) i k
  have hell : ∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x) := by
    intro x _
    rw [hΛ]
    exact isEllipticMatrix_symField hγ j hh hS' G x
  have hEll : IsEllipticFieldOn 1 Λ (ball1 d) a :=
    isEllipticFieldOn_of_measurable (measurableSet_euclideanBall 0 1) hmeas hell
  obtain ⟨hv, hw⟩ := weak_solutions_of_flux hd hγ j hEll (c := 4)
    (fun x hx => matVecMul_symField_gradU hP j hS' hx)
  obtain ⟨w, hwf, hwsol⟩ := hw
  refine ⟨a, hmeas, symField_symm hγ j hh hS' G, hell, ⟨hα0, hαΛ⟩,
    ⟨(continuous_uProf j hγ hα0).continuousOn, fun x _ => abs_uProf_le j hγ hα0 x,
      fun s hs _ => uProf_ray j hγ _ hs, uProf_holder j hγ hα0 hα1.le _⟩,
    hv, fun ρ hρ _ α' hα' => uProf_not_holder j hγ hα0 hρ hα', ⟨w, hwf, ?_, hwsol, ?_, ?_,
      harnack_ratio_arith_sqrt hα0 hαΛ⟩⟩
  · intro x hx
    rw [hwf]
    exact one_add_uProf_pos j hγ hα0 hx
  · rw [hwf]
    exact uProf_isLUB j hγ hα0
  · rw [hwf]
    exact uProf_isGLB j hγ hα0

end PDE.Guerra
