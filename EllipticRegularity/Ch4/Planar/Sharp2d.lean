module

public import EllipticRegularity.Ch4.Planar.Sharp2dGrowth
public import EllipticRegularity.Ch4.Planar.Morrey

/-!
# Sharp Hölder exponent in the plane (Proposition 4.27 (i))

The Piccinini--Spagnolo monotonicity formula (interface hypothesis `hSpag`) gives the energy
growth `∫_{B_r(x₀)} |∇u|² ≤ Λ (2r)^{2 Λ^{-1/2}} ∫_{B_1} |∇u|²`, and Morrey's Dirichlet growth
theorem with `α = Λ^{-1/2}` gives the Hölder representative.
-/

@[expose] public section

namespace PDE.Ch4Planar

open MeasureTheory

/-- Sharp Hölder exponent in `d = 2` (Proposition 4.27(i)), in the exact form of the
statement `exists_sharp2d_holder_constant`, given the Piccinini--Spagnolo monotonicity
formula `hSpag` (the statement `piccinini_spagnolo_monotonicity`). -/
theorem exists_sharp2d_holder_constant_full
    (hSpag : ∀ (Λ : ℝ) (a : CoeffField 2),
      (∀ i j : Fin 2, AEMeasurable (fun x => a x i j)
        (volumeOn (euclideanBall (0 : Vec 2) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec 2) 1, ∀ i j : Fin 2, a x i j = a x j i) →
      (∀ x ∈ euclideanBall (0 : Vec 2) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ (u : H1Function (euclideanBall (0 : Vec 2) 1)),
        IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec 2) 1) u
          (0 : Vec 2 → ℝ) 0 →
      MonotoneOn
        (fun r : ℝ => r ^ (-(2 / Real.sqrt Λ)) *
          ∫ x in euclideanBall (0 : Vec 2) r,
            vecDot (u.grad x) (matVecMul (a x) (u.grad x)))
        (Set.Ioo 0 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField 2),
      (∀ i j : Fin 2, AEMeasurable (fun x => a x i j)
        (volumeOn (euclideanBall (0 : Vec 2) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec 2) 1, ∀ i j : Fin 2, a x i j = a x j i) →
      (∀ x ∈ euclideanBall (0 : Vec 2) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec 2) 1),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec 2) 1) u (0 : Vec 2 → ℝ) 0 →
        (∀ x₀ ∈ euclideanBall (0 : Vec 2) (1 / 2), ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
          ∫ y in euclideanBall x₀ r, vecNormSq (u.grad y) ≤
            Λ * (2 * r) ^ (2 * Λ ^ (-(1 / 2 : ℝ))) *
              ∫ y in euclideanBall (0 : Vec 2) 1, vecNormSq (u.grad y)) ∧
        ∃ (v : Vec 2 → ℝ) (M : ℝ), v =ᵐ[volumeOn (euclideanBall (0 : Vec 2) (1 / 2))] u.toFun ∧
          0 ≤ M ∧
          EuclideanHolderSeminormLE (euclideanBall (0 : Vec 2) (1 / 2)) v
            (Λ ^ (-(1 / 2 : ℝ))) M ∧
          M ≤ C * Λ * Real.sqrt (∫ y in euclideanBall (0 : Vec 2) 1, vecNormSq (u.grad y)) := by
  obtain ⟨CM, hCM, hM⟩ := exists_morrey_growth_constant_full 2 le_rfl
  refine ⟨2 * CM, by positivity, ?_⟩
  intro Λ a hmeas hsymm hell u hsol
  have hUmeas : MeasurableSet (euclideanBall (0 : Vec 2) 1) := measurableSet_euclideanBall _ _
  have hΛ1 : 1 ≤ Λ := (hell 0 (center_mem_euclideanBall 0 (by norm_num))).lam_le_Lam
  have hΛ : 0 < Λ := by linarith
  set E := ∫ y in euclideanBall (0 : Vec 2) 1, vecNormSq (u.grad y) with hE
  have hE0 : 0 ≤ E := setIntegral_nonneg hUmeas fun x _ => by
    unfold vecNormSq vecDot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  set α : ℝ := Λ ^ (-(1 / 2 : ℝ)) with hα
  have hαpos : 0 < α := by positivity
  have hα1 : α ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hΛ1 (by norm_num)
  have hgrowth : ∀ x₀ ∈ euclideanBall (0 : Vec 2) (1 / 2), ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
      ∫ y in euclideanBall x₀ r, vecNormSq (u.grad y) ≤
        Λ * (2 * r) ^ (2 * α) * E := by
    intro x₀ hx₀ r hr hr2
    have hball := euclideanBall_half_subset_unit_of_center_mem_half hx₀
    have hsub : euclideanBall x₀ r ⊆ euclideanBall (0 : Vec 2) 1 :=
      (euclideanBall_mono hr.le hr2).trans hball
    -- pointwise comparison with the energy density
    have h1 : ∫ y in euclideanBall x₀ r, vecNormSq (u.grad y) ≤
        ∫ y in euclideanBall x₀ r, vecDot (u.grad y) (matVecMul (a y) (u.grad y)) := by
      refine setIntegral_mono_on ((integrableOn_gradSq u).mono_set hsub)
        ((integrableOn_energyDensity hUmeas hmeas hell u).mono_set hsub)
        (measurableSet_euclideanBall _ _) fun x hx => ?_
      exact DGNM.vecNormSq_le_vecDot_matVecMul (hell x (hsub hx)) _
    have h2 := sharp2d_energy_growth hSpag Λ a hmeas hsymm hell u hsol x₀ hx₀ r hr hr2
    have h3 : ∫ y in euclideanBall (0 : Vec 2) 1,
        vecDot (u.grad y) (matVecMul (a y) (u.grad y)) ≤ Λ * E := by
      rw [hE, ← integral_const_mul]
      refine setIntegral_mono_on (integrableOn_energyDensity hUmeas hmeas hell u)
        ((integrableOn_gradSq u).const_mul Λ) hUmeas fun x hx => ?_
      exact vecDot_matVecMul_le (hell x hx) _
    have h2r : 0 ≤ (2 * r) ^ (2 * α) := Real.rpow_nonneg (by linarith) _
    calc _ ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ (2 * r) ^ (2 * α) * (Λ * E) := mul_le_mul_of_nonneg_left h3 h2r
      _ = Λ * (2 * r) ^ (2 * α) * E := by ring
  refine ⟨hgrowth, ?_⟩
  -- Morrey's theorem with `K = 4 Λ E`
  have hK : 0 ≤ 4 * Λ * E := by positivity
  have hgrowth' : ∀ x ∈ euclideanBall (0 : Vec 2) (1 / 2), ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
      ∫ y in euclideanBall x r, vecNormSq (u.grad y) ≤
        (4 * Λ * E) * r ^ (((2 : ℕ) : ℝ) - 2 + 2 * α) := by
    intro x hx r hr hr2
    refine (hgrowth x hx r hr hr2).trans ?_
    have h4 : (2 : ℝ) ^ (2 * α) ≤ 4 := by
      calc (2 : ℝ) ^ (2 * α) ≤ (2 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 4 := by norm_num
    have hexp : ((2 : ℕ) : ℝ) - 2 + 2 * α = 2 * α := by push_cast; ring
    rw [hexp, Real.mul_rpow (by norm_num) hr.le]
    have hr' : 0 ≤ r ^ (2 * α) := Real.rpow_nonneg hr.le _
    have : Λ * (2 ^ (2 * α) * r ^ (2 * α)) * E ≤ Λ * (4 * r ^ (2 * α)) * E := by
      apply mul_le_mul_of_nonneg_right _ hE0
      apply mul_le_mul_of_nonneg_left _ hΛ.le
      exact mul_le_mul_of_nonneg_right h4 hr'
    calc _ ≤ _ := this
      _ = _ := by ring
  obtain ⟨v, M, hv, hM0, hMH, hMle⟩ := hM α (4 * Λ * E) hαpos hα1 hK u hgrowth'
  refine ⟨v, M, hv, hM0, hMH, ?_⟩
  -- `α⁻¹ = √Λ`, `√(4ΛE) = 2 √Λ √E`
  have hαinv : α⁻¹ = Real.sqrt Λ := by
    rw [hα, Real.rpow_neg hΛ.le, inv_inv, Real.sqrt_eq_rpow]
  have hsq : Real.sqrt (4 * Λ * E) = 2 * Real.sqrt Λ * Real.sqrt E := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)]
    have : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    rw [this]
  have hΛsq : Real.sqrt Λ * Real.sqrt Λ = Λ := Real.mul_self_sqrt hΛ.le
  calc M ≤ CM * α⁻¹ * Real.sqrt (4 * Λ * E) := hMle
    _ = 2 * CM * (Real.sqrt Λ * Real.sqrt Λ) * Real.sqrt E := by
      rw [hαinv, hsq]; ring
    _ = 2 * CM * Λ * Real.sqrt E := by rw [hΛsq]

end PDE.Ch4Planar
