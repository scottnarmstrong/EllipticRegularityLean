module

public import EllipticRegularity.Ch4.Meyers.ExamAlpha

/-!
# Meyers' example as the profile `s^γ x_0` with `s = |x|²`
-/

@[expose] public section

namespace PDE.Ch4Meyers

open MeasureTheory Set Filter
open scoped Topology

variable {d : ℕ} {w : Fin d → ℝ}

theorem abs_prof_le_rpow (hw : ∀ i, w i = 0 ∨ w i = 1) {k : Fin d} (hk : w k = 1) {γ : ℝ}
    (hγ : -1 / 2 < γ) (x : Vec d) : |prof w γ k x| ≤ axisSq w x ^ (γ + 1 / 2) := by
  rcases (axisSq_nonneg hw x).eq_or_lt with hs | hs
  · have : x k ^ 2 = 0 := le_antisymm (hs ▸ sq_le_axisSq hw x hk) (sq_nonneg _)
    have hxk : x k = 0 := pow_eq_zero_iff two_ne_zero |>.mp this
    rw [← hs, Real.zero_rpow (by linarith)]
    simp [prof, hxk]
  · unfold prof
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hs.le _), Real.rpow_add hs]
    gcongr
    rw [← Real.sqrt_eq_rpow]
    exact abs_coord_le_sqrt hw hk x

theorem continuous_prof (hw : ∀ i, w i = 0 ∨ w i = 1) {k : Fin d} (hk : w k = 1) {γ : ℝ}
    (hγ : -1 / 2 < γ) : Continuous (prof w γ k) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases (axisSq_nonneg hw x).eq_or_lt with hs | hs
  · have hxk : x k = 0 := by
      have : x k ^ 2 = 0 := le_antisymm (hs ▸ sq_le_axisSq hw x hk) (sq_nonneg _)
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    have hpx : prof w γ k x = 0 := by simp [prof, hxk]
    have hcont : Continuous fun y : Vec d => axisSq w y ^ (γ + 1 / 2) :=
      (contDiff_axisSq w).continuous.rpow_const fun _ => Or.inr (by linarith)
    have hval : axisSq w x ^ (γ + 1 / 2) = 0 := by
      rw [← hs]; exact Real.zero_rpow (by linarith)
    have htend : Tendsto (fun y : Vec d => axisSq w y ^ (γ + 1 / 2)) (𝓝 x) (𝓝 0) := by
      rw [← hval]; exact hcont.continuousAt.tendsto
    rw [ContinuousAt, hpx]
    exact squeeze_zero_norm (fun y => by
      rw [Real.norm_eq_abs]; exact abs_prof_le_rpow hw hk hγ y) htend
  · exact (contDiffAt_prof hs γ k 0).continuousAt

theorem axisSq_one_eq (x : Vec d) : axisSq (fun _ => (1 : ℝ)) x = vecNormSq x := by
  simp [axisSq, vecNormSq_eq_sum_sq]

theorem exam_coeff_eq (Λ : ℝ) :
    (fun x : Vec d => if x = 0 then (1 : Mat d) else
      fun i j => (if i = j then (1 : ℝ) else 0) + (Λ - 1) * x i * x j / vecNormSq x) =
      meyersCoeff (fun _ => (1 : ℝ)) Λ := by
  funext x
  by_cases hx : x = 0
  · subst hx
    simp only [↓reduceIte]
    rw [meyersCoeff_of_axisSq_eq_zero]
    simp [axisSq]
  · simp only [hx, ↓reduceIte]
    funext i j
    simp only [meyersCoeff, axisSq_one_eq, one_mul]

theorem exam_u_eq (i0 : Fin d) (α : ℝ) :
    (fun x : Vec d => if x = 0 then (0 : ℝ) else vecEuclideanNorm x ^ (α - 1) * x i0) =
      prof (fun _ => (1 : ℝ)) ((α - 1) / 2) i0 := by
  funext x
  by_cases hx : x = 0
  · subst hx
    simp [prof, axisSq]
  · simp only [hx, ↓reduceIte]
    unfold prof
    rw [axisSq_one_eq, vecEuclideanNorm, Real.sqrt_eq_rpow, ← Real.rpow_mul (vecNormSq_nonneg x)]
    congr 2
    ring

end PDE.Ch4Meyers
