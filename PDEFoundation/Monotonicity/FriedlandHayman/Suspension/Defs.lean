module

public import PDEFoundation.Monotonicity.FriedlandHayman.Basic
public import PDEFoundation.Monotonicity.FriedlandHayman.Sphere.Proj

/-!
# Friedland--Hayman: the suspension of a spherical domain

The suspension `Ω_N = {x ∈ S^{n+N-1} : x' ≠ 0, x'/|x'| ∈ Ω}` and elementary facts about points of
the unit sphere used throughout the suspension construction.
-/

@[expose] public section

open MeasureTheory

namespace PDE.FHLane

noncomputable section

/-- The suspension `Ω_N = {x ∈ S^{n+N-1} : x' ≠ 0, x'/|x'| ∈ Ω}`. -/
def suspension (n N : ℕ) (Ω : Set (Vec n)) : Set (Vec (n + N)) :=
  {x | x ∈ euclideanSphere (0 : Vec (n + N)) 1 ∧ projFst x ≠ 0 ∧
    (vecEuclideanNorm (projFst x))⁻¹ • projFst x ∈ Ω}

namespace Susp

theorem mem_euclideanSphere_iff {d : ℕ} {x : Vec d} :
    x ∈ euclideanSphere (0 : Vec d) 1 ↔ vecNormSq x = 1 := by
  simp [euclideanSphere, euclideanSqDist]

theorem vecNormSq_toVec_sphere {d : ℕ} (ω : Metric.sphere (0 : HilbertVec d) 1) :
    vecNormSq (ω : HilbertVec d).toVec = 1 := by
  have hn : ‖(ω : HilbertVec d)‖ = 1 := by simp
  rw [HilbertVec.norm_eq_vecEuclideanNorm] at hn
  have hsq := vecEuclideanNorm_sq (ω : HilbertVec d).toVec
  rw [hn] at hsq
  linarith

theorem toVec_mem_sphere {d : ℕ} (ω : Metric.sphere (0 : HilbertVec d) 1) :
    (ω : HilbertVec d).toVec ∈ euclideanSphere (0 : Vec d) 1 :=
  mem_euclideanSphere_iff.2 (vecNormSq_toVec_sphere ω)

theorem sphereIntegral_congr_sphere {d : ℕ} {f g : Vec d → ℝ}
    (h : ∀ x ∈ euclideanSphere (0 : Vec d) 1, f x = g x) :
    sphereIntegral (0 : Vec d) 1 f = sphereIntegral (0 : Vec d) 1 g := by
  unfold sphereIntegral
  congr 1
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp only [zero_add, one_smul]
  exact h _ (toVec_mem_sphere ω)

theorem vecNormSq_append {n N : ℕ} (x : Vec (n + N)) :
    vecNormSq x = vecNormSq (projFst x) + ∑ i : Fin N, x (Fin.natAdd n i) ^ 2 := by
  rw [vecNormSq_eq_sum_sq, vecNormSq_eq_sum_sq, Fin.sum_univ_add]
  rfl

theorem vecNormSq_projFst_le {n N : ℕ} (x : Vec (n + N)) :
    vecNormSq (projFst x) ≤ vecNormSq x := by
  rw [vecNormSq_append x]
  have : 0 ≤ ∑ i : Fin N, x (Fin.natAdd n i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

theorem vecEuclideanNorm_projFst_le_one {n N : ℕ} {x : Vec (n + N)}
    (hx : x ∈ euclideanSphere (0 : Vec (n + N)) 1) : vecEuclideanNorm (projFst x) ≤ 1 := by
  have h := vecNormSq_projFst_le x
  rw [mem_euclideanSphere_iff.1 hx] at h
  unfold vecEuclideanNorm
  calc Real.sqrt (vecNormSq (projFst x)) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h
    _ = 1 := Real.sqrt_one

end Susp

end

end PDE.FHLane
