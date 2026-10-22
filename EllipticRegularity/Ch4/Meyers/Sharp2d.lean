module

public import EllipticRegularity.Ch4.Meyers.Example

/-!
# Proposition 4.27(ii): the sharp Hölder exponent in `d = 2`

The theorem `sharp2d_not_holder_full` is the statement `sharp2d_not_holder` with the single change `1`
to `(1 : Mat 2)` in the hypothesis `ha` (see `sharp2d_not_holder_ellipticity_false`).
It is a corollary of `meyers_example_full` at `d = 2`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4Meyers

open MeasureTheory Set Filter
open scoped Topology

/-- A function with a Euclidean Hölder bound (positive exponent) on a set is continuous there. -/
theorem continuousOn_of_euclideanHolder {d : ℕ} {S : Set (Vec d)} {v : Vec d → ℝ}
    {α' M : ℝ} (hα : 0 < α') (hH : EuclideanHolderSeminormLE S v α' M) : ContinuousOn v S := by
  intro x hx
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun y : Vec d => M * vecEuclideanNorm (y - x) ^ α') (𝓝 x) (𝓝 0) := by
    have h1 : Continuous fun y : Vec d => vecEuclideanNorm (y - x) :=
      continuous_vecEuclideanNorm.comp (continuous_id.sub continuous_const)
    have h2 : Continuous fun y : Vec d => vecEuclideanNorm (y - x) ^ α' :=
      h1.rpow_const fun _ => Or.inr hα.le
    have h3 := (h2.mul_const M).continuousAt (x := x) |>.tendsto
    have h4 : vecEuclideanNorm (x - x) ^ α' * M = 0 := by
      simp [vecEuclideanNorm, vecNormSq, vecDot, hα.ne']
    simp only [h4] at h3
    simpa [mul_comm] using h3
  refine squeeze_zero_norm' ?_ (hlim.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [norm_norm, Real.norm_eq_abs]
  exact hH y hy x hx

/-- The `ha` of `sharp2d_not_holder` makes `a 0` the all-ones matrix, which is not elliptic
(so its ellipticity conclusion at `x = 0` is false). -/
theorem sharp2d_not_holder_ellipticity_false (Λ : ℝ) (_hΛ : 1 < Λ)
    (a : CoeffField 2)
    (ha : a = fun x => if x = 0 then 1 else
      fun i j => (if i = j then (1 : ℝ) else 0) + (Λ - 1) * x i * x j / vecNormSq x) :
    ¬ (∀ x ∈ euclideanBall (0 : Vec 2) 1, IsEllipticMatrix 1 Λ (a x)) := by
  intro h
  have h0 : (0 : Vec 2) ∈ euclideanBall (0 : Vec 2) 1 := by
    change euclideanSqDist 0 0 < 1 ^ 2
    simp
  have hell := (h 0 h0).coercive (fun j => if j = 0 then 1 else -1)
  have ha0 : a 0 = fun _ _ => 1 := by rw [ha]; simp; funext i j; rfl
  rw [ha0] at hell
  simp [vecNormSq, vecDot, matVecMul, Fin.sum_univ_two] at hell
  norm_num at hell

/-- Sharp Hölder exponent in `d = 2` (Proposition 4.27(ii)). -/
theorem sharp2d_not_holder_full (Λ : ℝ) (hΛ : 1 < Λ) (α' : ℝ)
    (hα1 : Λ ^ (-(1 / 2 : ℝ)) < α') (_hα2 : α' ≤ 1)
    (a : CoeffField 2)
    (ha : a = fun x => if x = 0 then (1 : Mat 2) else
      fun i j => (if i = j then (1 : ℝ) else 0) + (Λ - 1) * x i * x j / vecNormSq x)
    (u : Vec 2 → ℝ)
    (hu : u = fun x => if x = 0 then 0 else
      vecEuclideanNorm x ^ (Λ ^ (-(1 / 2 : ℝ)) - 1) * x 0) :
    ((∀ i j : Fin 2, AEMeasurable (fun x => a x i j)
        (volumeOn (euclideanBall (0 : Vec 2) 1))) ∧
      (∀ x ∈ euclideanBall (0 : Vec 2) 1, ∀ i j : Fin 2, a x i j = a x j i) ∧
      (∀ x ∈ euclideanBall (0 : Vec 2) 1, IsEllipticMatrix 1 Λ (a x)) ∧
      ∃ v : H1Function (euclideanBall (0 : Vec 2) 1), v.toFun = u ∧
        IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec 2) 1) v
          (0 : Vec 2 → ℝ) 0) ∧
    ¬ ∃ (v : Vec 2 → ℝ) (M : ℝ), v =ᵐ[volumeOn (euclideanBall (0 : Vec 2) (1 / 2))] u ∧
        EuclideanHolderSeminormLE (euclideanBall (0 : Vec 2) (1 / 2)) v α' M
:= by
  have hα : Λ ^ (-(1 / 2 : ℝ)) = (1 / 2) * (-(((2 : ℕ) : ℝ) - 2) +
      Real.sqrt ((((2 : ℕ) : ℝ) - 2) ^ 2 + 4 * (((2 : ℕ) : ℝ) - 1) / Λ)) := by
    have := examα_two (d := 2) (Λ := Λ) le_rfl hΛ.le rfl
    exact this.symm
  obtain ⟨-, ⟨hm, hs, he⟩, ⟨hcont, v0, hv0, -, hsol⟩, ⟨-, hiv⟩⟩ :=
    meyers_example_full 2 le_rfl Λ hΛ.le (Λ ^ (-(1 / 2 : ℝ))) hα a ha u hu
  refine ⟨⟨fun i j => (hm i j).aemeasurable, fun x _ i j => hs x i j, he, v0, hv0, hsol⟩, ?_⟩
  rintro ⟨v, M, hae, hH⟩
  have hα'0 : 0 < α' := lt_trans (Real.rpow_pos_of_pos (by linarith) _) hα1
  have hsub : euclideanBall (0 : Vec 2) (1 / 2) ⊆ euclideanBall (0 : Vec 2) 1 :=
    euclideanBall_mono (by norm_num) (by norm_num)
  have hvc : ContinuousOn v (euclideanBall (0 : Vec 2) (1 / 2)) :=
    continuousOn_of_euclideanHolder hα'0 hH
  have hequ : EqOn v u (euclideanBall (0 : Vec 2) (1 / 2)) :=
    Measure.eqOn_open_of_ae_eq hae (isOpen_euclideanBall _ _) hvc (hcont.mono hsub)
  obtain ⟨t, ht0, ht1, hlt⟩ := hiv α' hα1 M
  have hn : vecEuclideanNorm (t • Pi.single (⟨0, by omega⟩ : Fin 2) (1 : ℝ) - 0) = t := by
    have : vecNormSq (t • Pi.single (⟨0, by omega⟩ : Fin 2) (1 : ℝ) - 0) = t ^ 2 := by
      rw [vecNormSq_eq_sum_sq]
      simp [Pi.single_apply]
    rw [vecEuclideanNorm, this, Real.sqrt_sq ht0.le]
  have hmem : t • Pi.single (⟨0, by omega⟩ : Fin 2) (1 : ℝ) ∈ euclideanBall (0 : Vec 2) (1 / 2) := by
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num), hn]
    exact ht1
  have h0mem : (0 : Vec 2) ∈ euclideanBall (0 : Vec 2) (1 / 2) := by
    change euclideanSqDist 0 0 < (1 / 2) ^ 2
    simp
  have hbound := hH _ hmem 0 h0mem
  rw [hequ hmem, hequ h0mem] at hbound
  rw [hn] at hbound
  linarith

end PDE.Ch4Meyers
