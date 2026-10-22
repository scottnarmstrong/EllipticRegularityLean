module

public import EllipticRegularity.Ch4.Meyers.ExamSolution

/-!
# Proposition 4.26 (Meyers' example)

The theorem `meyers_example_full` has exactly the type of the statement `meyers_example`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4Meyers

open MeasureTheory Set Filter
open scoped Topology

variable {d : ℕ}

/-- Meyers' example as an `H¹` function on the unit ball. -/
noncomputable def examV (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ) : H1Function (euclideanBall (0 : Vec d) 1) :=
  profH1 (w := fun _ => (1 : ℝ)) (fun _ => Or.inr rfl) (i0 := ⟨0, by omega⟩) (i1 := ⟨1, by omega⟩)
    (by simp [Fin.ext_iff]) rfl rfl (k := ⟨0, by omega⟩) rfl
    (γ := (examα d Λ - 1) / 2)
    (by have := examα_pos hd hΛ; linarith) (by have := examα_le_one hd hΛ; linarith)

theorem examV_toFun (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    (examV hd hΛ).toFun = prof (fun _ => (1 : ℝ)) ((examα d Λ - 1) / 2) ⟨0, by omega⟩ := rfl

theorem examV_grad (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    (examV hd hΛ).grad = profGrad (fun _ => (1 : ℝ)) ((examα d Λ - 1) / 2) ⟨0, by omega⟩ := rfl

theorem exam_solution (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    IsWeakDivergenceFormSolutionOn (meyersCoeff (fun _ => (1 : ℝ)) Λ) (euclideanBall (0 : Vec d) 1)
      (examV hd hΛ) (0 : Vec d → ℝ) 0 := by
  have hflux : ∀ᵐ x ∂(volume.restrict (euclideanBall (0 : Vec d) 1)),
      matVecMul (meyersCoeff (fun _ => (1 : ℝ)) Λ x) ((examV hd hΛ).grad x) =
        profFlux (fun _ => (1 : ℝ)) Λ ((examα d Λ - 1) / 2) (⟨0, by omega⟩ : Fin d) x := by
    filter_upwards [ae_axisSq_pos (w := fun _ : Fin d => (1 : ℝ)) (fun _ => Or.inr rfl)
      (i0 := (⟨0, by omega⟩ : Fin d)) rfl (euclideanBall (0 : Vec d) 1)] with x hx
    exact meyersCoeff_matVecMul_profGrad (fun _ => Or.inr rfl) hx Λ _ rfl
  refine IsWeakDivergenceFormL2SolutionOn.toIsWeakDivergenceFormSolutionOn
    { flux_memL2 := fun i => (memLp_exam_flux hd hΛ i).ae_eq (by
        filter_upwards [hflux] with x hx
        exact (congrFun hx i).symm)
      source_memL2 := MemLp.zero
      forcing_memL2 := fun i => by simp
      identity := ?_ }
  intro φ
  simp only [Pi.zero_apply, zero_mul, integral_zero, vecDot, zero_sub,
    Finset.sum_const_zero, neg_zero, WeakTestFunction.grad_apply]
  have hae : ∀ᵐ x ∂(volume.restrict (euclideanBall (0 : Vec d) 1)),
      ∑ j, matVecMul (meyersCoeff (fun _ => (1 : ℝ)) Λ x) ((examV hd hΛ).grad x) j *
        φ.partialDeriv j x =
      vecDot (profFlux (fun _ => (1 : ℝ)) Λ ((examα d Λ - 1) / 2) (⟨0, by omega⟩ : Fin d) x)
        (classicalGradient φ.toFun x) := by
    filter_upwards [hflux] with x hx
    rw [hx]
    rfl
  rw [integral_congr_ae hae]
  exact exam_flux_integral_zero hd hΛ φ

/-- The `ha` of `meyers_example` makes `a 0` the all-ones matrix (its `then` branch `1` is
elaborated at type `Fin d → Fin d → ℝ`), which is not elliptic; hence the ellipticity conclusion
of the statement is false at `x = 0`. -/
theorem meyers_example_ii_false (hd : 2 ≤ d) (Λ : ℝ)
    (a : CoeffField d)
    (ha : a = fun x => if x = 0 then 1 else
      fun i j => (if i = j then (1 : ℝ) else 0) + (Λ - 1) * x i * x j / vecNormSq x) :
    ¬ (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) := by
  intro h
  have h0 : (0 : Vec d) ∈ euclideanBall (0 : Vec d) 1 := by
    change euclideanSqDist 0 0 < 1 ^ 2
    simp
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  have hi : i0 ≠ i1 := by
    intro h; have := congrArg Fin.val h; simp [i0, i1] at this
  have hell := (h 0 h0).coercive (fun j => if j = i0 then 1 else if j = i1 then -1 else 0)
  have ha0 : a 0 = fun _ _ => 1 := by rw [ha]; simp; funext i j; rfl
  rw [ha0] at hell
  have hsum : ∑ j : Fin d, (if j = i0 then (1 : ℝ) else if j = i1 then -1 else 0) = 0 := by
    rw [Finset.sum_eq_add i0 i1 hi]
    · simp [hi.symm]
    · intro c _ hc; simp [hc.1, hc.2]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h
  have hnorm : vecNormSq (fun j : Fin d => if j = i0 then (1 : ℝ) else if j = i1 then -1 else 0) = 2 := by
    rw [vecNormSq_eq_sum_sq, Finset.sum_eq_add i0 i1 hi]
    · simp [hi.symm]; norm_num
    · intro c _ hc; simp [hc.1, hc.2]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h
  have hdot : vecDot (fun j : Fin d => if j = i0 then (1 : ℝ) else if j = i1 then -1 else 0)
      (matVecMul (fun _ _ => (1 : ℝ)) (fun j : Fin d => if j = i0 then (1 : ℝ) else if j = i1 then -1 else 0)) = 0 := by
    simp only [vecDot, matVecMul, one_mul]
    simp [hsum]
  rw [hnorm, hdot] at hell
  norm_num at hell

/-- Meyers' example (Proposition 4.26).  This is the statement `meyers_example` with the
single change `1` to `(1 : Mat d)` in the hypothesis `ha`: in the text the `1` of the
`then` branch is elaborated at type `Fin d → Fin d → ℝ` (the all-ones matrix), see
`meyers_example_ii_false`. -/
theorem meyers_example_full (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (α : ℝ)
    (hα : α = (1 / 2) * (-((d : ℝ) - 2) + Real.sqrt (((d : ℝ) - 2) ^ 2 + 4 * ((d : ℝ) - 1) / Λ)))
    (a : CoeffField d)
    (ha : a = fun x => if x = 0 then (1 : Mat d) else
      fun i j => (if i = j then (1 : ℝ) else 0) + (Λ - 1) * x i * x j / vecNormSq x)
    (u : Vec d → ℝ)
    (hu : u = fun x => if x = 0 then 0 else vecEuclideanNorm x ^ (α - 1) * x ⟨0, by omega⟩) :
    (0 < α ∧ α ≤ 1 ∧ (α = 1 ↔ Λ = 1) ∧ (d = 2 → α = Λ ^ (-(1 / 2 : ℝ)))) ∧
    ((∀ i j : Fin d, Measurable (fun x => a x i j)) ∧
      (∀ x : Vec d, ∀ i j : Fin d, a x i j = a x j i) ∧
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x))) ∧
    (ContinuousOn u (euclideanBall (0 : Vec d) 1) ∧
      ∃ v : H1Function (euclideanBall (0 : Vec d) 1), v.toFun = u ∧
        (∀ x ∈ euclideanBall (0 : Vec d) 1, x ≠ 0 →
          ∀ i : Fin d, v.grad x i = fderiv ℝ u x (Pi.single i 1)) ∧
        IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) v
          (0 : Vec d → ℝ) 0) ∧
    ((∀ t : ℝ, 0 < t → t < 1 → u (t • Pi.single ⟨0, by omega⟩ 1) = t ^ α) ∧
      ∀ α' : ℝ, α < α' → ∀ M : ℝ, ∃ t : ℝ, 0 < t ∧ t < 1 / 2 ∧
        M * t ^ α' < |u (t • Pi.single ⟨0, by omega⟩ 1) - u 0|)
:= by
  have hαe : α = examα d Λ := hα
  have ha' : a = meyersCoeff (fun _ => (1 : ℝ)) Λ := ha.trans (exam_coeff_eq Λ)
  have hu' : u = prof (fun _ => (1 : ℝ)) ((α - 1) / 2) ⟨0, by omega⟩ := hu.trans (exam_u_eq _ α)
  have hw : ∀ j : Fin d, (fun _ : Fin d => (1 : ℝ)) j = 0 ∨ (fun _ : Fin d => (1 : ℝ)) j = 1 :=
    fun _ => Or.inr rfl
  have hα0 := examα_pos hd hΛ
  have hα1 := examα_le_one hd hΛ
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [hαe]; exact hα0
  · rw [hαe]; exact hα1
  · rw [hαe]; exact examα_eq_one_iff hd hΛ
  · intro h2; rw [hαe]; exact examα_two hd hΛ h2
  · intro i j; rw [ha']; exact measurable_meyersCoeff_apply _ Λ i j
  · intro x i j; rw [ha']; exact meyersCoeff_symm _ Λ x i j
  · intro x _; rw [ha']; exact isEllipticMatrix_meyersCoeff hw hΛ x
  · rw [hu']
    exact (continuous_prof hw (k := ⟨0, by omega⟩) rfl (by linarith)).continuousOn
  · refine ⟨examV hd hΛ, ?_, ?_, ?_⟩
    · rw [hu', hαe]; rfl
    · intro x _ hx i
      have hs := axisSq_one_pos hx
      have := classicalGradient_prof hw hs ((α - 1) / 2) (⟨0, by omega⟩ : Fin d)
      rw [hu', hαe]
      have h2 := congrFun this i
      rw [classicalGradient_apply] at h2
      rw [hαe] at h2
      exact h2.symm
    · rw [ha']; exact exam_solution hd hΛ
  · intro t ht0 ht1
    have hn : vecEuclideanNorm (t • (Pi.single (⟨0, by omega⟩ : Fin d) (1 : ℝ))) = t := by
      have : vecNormSq (t • (Pi.single (⟨0, by omega⟩ : Fin d) (1 : ℝ))) = t ^ 2 := by
        rw [vecNormSq_eq_sum_sq]
        simp [Pi.single_apply]
      rw [vecEuclideanNorm, this, Real.sqrt_sq ht0.le]
    have hne : t • (Pi.single (⟨0, by omega⟩ : Fin d) (1 : ℝ)) ≠ 0 := by
      intro h
      have := congrFun h ⟨0, by omega⟩
      simp at this
      linarith
    rw [hu]
    simp only [hne, ↓reduceIte, hn]
    have hc : (t • (Pi.single (⟨0, by omega⟩ : Fin d) (1 : ℝ))) ⟨0, by omega⟩ = t := by simp
    rw [hc, Real.rpow_sub_one ht0.ne']
    field_simp
  · intro α' hαα' M
    have hε : 0 < α' - α := by linarith
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ^ (α' - α) < 1 / (|M| + 1) := by
      have hlim : Tendsto (fun t : ℝ => t ^ (α' - α)) (𝓝 0) (𝓝 0) := by
        have := (Real.continuousAt_rpow_const (0 : ℝ) (α' - α) (Or.inr hε.le)).tendsto
        rwa [Real.zero_rpow hε.ne'] at this
      exact (tendsto_order.1 (hlim.mono_left nhdsWithin_le_nhds)).2 _ (by positivity)
    have hev2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 / 2 := by
      exact (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))) (Iio_mem_nhds (by norm_num))
    obtain ⟨t, ht1, ht2, ht3⟩ := (hev.and (hev2.and self_mem_nhdsWithin)).exists
    refine ⟨t, ht3, ht2, ?_⟩
    have ht0 : 0 < t := ht3
    have hn : vecEuclideanNorm (t • (Pi.single (⟨0, by omega⟩ : Fin d) (1 : ℝ))) = t := by
      have : vecNormSq (t • (Pi.single (⟨0, by omega⟩ : Fin d) (1 : ℝ))) = t ^ 2 := by
        rw [vecNormSq_eq_sum_sq]
        simp [Pi.single_apply]
      rw [vecEuclideanNorm, this, Real.sqrt_sq ht0.le]
    have hne : t • (Pi.single (⟨0, by omega⟩ : Fin d) (1 : ℝ)) ≠ 0 := by
      intro h
      have := congrFun h ⟨0, by omega⟩
      simp at this
      linarith
    have hval : u (t • (Pi.single (⟨0, by omega⟩ : Fin d) (1 : ℝ))) = t ^ α := by
      rw [hu]
      simp only [hne, ↓reduceIte, hn]
      have hc : (t • (Pi.single (⟨0, by omega⟩ : Fin d) (1 : ℝ))) ⟨0, by omega⟩ = t := by simp
      rw [hc, Real.rpow_sub_one ht0.ne']
      field_simp
    have hu0 : u 0 = 0 := by rw [hu]; simp
    rw [hval, hu0, sub_zero, abs_of_pos (Real.rpow_pos_of_pos ht0 α)]
    have hsplit : t ^ α' = t ^ (α' - α) * t ^ α := by
      rw [← Real.rpow_add ht0]; congr 1; ring
    rw [hsplit]
    have hpos : 0 < t ^ α := Real.rpow_pos_of_pos ht0 α
    have h1 : |M| * t ^ (α' - α) < 1 := by
      have := mul_lt_mul_of_pos_left ht1 (by positivity : 0 < |M| + 1)
      have h2 : (|M| + 1) * (1 / (|M| + 1)) = 1 := by field_simp
      nlinarith [abs_nonneg M, Real.rpow_pos_of_pos ht0 (α' - α)]
    calc M * (t ^ (α' - α) * t ^ α) ≤ |M| * (t ^ (α' - α) * t ^ α) :=
          mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity)
      _ = (|M| * t ^ (α' - α)) * t ^ α := by ring
      _ < 1 * t ^ α := mul_lt_mul_of_pos_right h1 hpos
      _ = t ^ α := one_mul _

end PDE.Ch4Meyers
