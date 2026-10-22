module

public import PDEFoundation.Analysis.Newtonian.Matrix.MatPotentialLinear
public import PDEFoundation.Analysis.Newtonian.NewtonPotentialSmoothProof

/-!
# Smoothness and derivative formula for the matrix Newton potential

With `S Sᵀ = M` and `T = S⁻¹`, `newtonPotentialMat M F = newtonPotential G ∘ T` for the smooth
compactly supported field `G z = T F(S z)`.  Smoothness follows by composition, and the derivative
formula by the chain rule, the Laplacian-kernel formula and `∑_j T_{jk} S_{mj} = δ_{mk}`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace PDE

namespace MatChange

variable {d : ℕ}

/-- The transformed field `z ↦ S⁻¹ F(S z)`. -/
theorem contDiff_transformField {S : Mat d} {F : Vec d → Vec d}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) fun z => matVecMul S⁻¹ (F (matVecMul S z)) :=
  (contDiff_matVecMul _).comp (hF.comp (contDiff_matVecMul _))

theorem newtonPotentialMat_eq_comp {M S : Mat d} (hS : S * Sᵀ = M) (hdet : S.det ≠ 0)
    (F : Vec d → Vec d) :
    newtonPotentialMat M F =
      fun x => newtonPotential (fun z => matVecMul S⁻¹ (F (matVecMul S z))) (matVecMul S⁻¹ x) :=
  funext fun x => (newtonPotential_transform hS hdet F x).symm

theorem contDiff_newtonPotentialMat (hd : 0 < d) {M S : Mat d} (hS : S * Sᵀ = M)
    (hdet : S.det ≠ 0) {F : Vec d → Vec d} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) : ContDiff ℝ (⊤ : ℕ∞) (newtonPotentialMat M F) := by
  rw [newtonPotentialMat_eq_comp hS hdet]
  exact (NewtonPotentialSmoothProof.result d hd _ (contDiff_transformField hF)
    (hasCompactSupport_matVecMul_comp hdet hFc)).1.comp (contDiff_matVecMul _)

theorem coordDeriv_transformField {S : Mat d} {F : Vec d → Vec d}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (j : Fin d) (w : Vec d) (i : Fin d) :
    euclideanCoordDeriv j (fun z => matVecMul S⁻¹ (F (matVecMul S z)) i) w =
      ∑ m, S m j * matVecMul S⁻¹ (fun l => euclideanCoordDeriv m (fun z => F z l) (matVecMul S w)) i
        := by
  have hFl : ∀ l, ContDiff ℝ (⊤ : ℕ∞) fun z => F z l := fun l => contDiff_pi.1 hF l
  have hg : ∀ l, ContDiff ℝ (⊤ : ℕ∞) fun z => F (matVecMul S z) l := fun l =>
    (hFl l).comp (contDiff_matVecMul _)
  simp only [matVecMul_apply]
  rw [euclideanCoordDeriv_sum_mul (g := fun l z => F (matVecMul S z) l) _ hg]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [euclideanCoordDeriv_comp_matVecMul S w ((hFl m).differentiable (by simp) _) j,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- The coordinate-derivative field of a smooth compactly supported field. -/
theorem hasCompactSupport_coordDerivField {F : Vec d → Vec d} (hFc : HasCompactSupport F)
    (m : Fin d) :
    HasCompactSupport fun y i => euclideanCoordDeriv m (fun z => F z i) y := by
  refine hFc.mono' fun x hx => ?_
  obtain ⟨i, hi⟩ : ∃ i, euclideanCoordDeriv m (fun z => F z i) x ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have h1 := support_euclideanCoordDeriv_subset_tsupport m (fun z => F z i) hi
  refine closure_mono ?_ h1
  intro z hz hz0
  exact hz (congrFun hz0 i)

theorem contDiff_coordDerivField {F : Vec d → Vec d} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (m : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) fun y i => euclideanCoordDeriv m (fun z => F z i) y :=
  contDiff_pi.2 fun i => contDiff_euclideanCoordDeriv (contDiff_pi.1 hF i) m

theorem coordDeriv_newtonPotentialMat (hd : 0 < d) {M S : Mat d} (hS : S * Sᵀ = M)
    (hdet : S.det ≠ 0) {F : Vec d → Vec d} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (k : Fin d) (x : Vec d) :
    euclideanCoordDeriv k (newtonPotentialMat M F) x =
      newtonPotentialMat M (fun y i => euclideanCoordDeriv k (fun z => F z i) y) x := by
  set G : Vec d → Vec d := fun z => matVecMul S⁻¹ (F (matVecMul S z)) with hG
  have hGs : ContDiff ℝ (⊤ : ℕ∞) G := contDiff_transformField hF
  have hGc : HasCompactSupport G := hasCompactSupport_matVecMul_comp hdet hFc
  have hD := NewtonPotentialSmoothProof.result d hd G hGs hGc
  set Gm : Fin d → Vec d → Vec d := fun m z =>
    matVecMul S⁻¹ ((fun y i => euclideanCoordDeriv m (fun z => F z i) y) (matVecMul S z)) with hGm
  have hGm_s : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (Gm m) := fun m =>
    contDiff_transformField (contDiff_coordDerivField hF m)
  have hGm_c : ∀ m, HasCompactSupport (Gm m) := fun m =>
    hasCompactSupport_matVecMul_comp hdet (hasCompactSupport_coordDerivField hFc m)
  have hH : ∀ j : Fin d, (fun y i => euclideanCoordDeriv j (fun z => G z i) y) =
      ∑ m, S m j • Gm m := by
    intro j
    funext y i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact coordDeriv_transformField hF j y i
  have hu : DifferentiableAt ℝ (newtonPotential G) (matVecMul S⁻¹ x) :=
    (hD.1.differentiable (by simp)) _
  have e1 : euclideanCoordDeriv k (newtonPotentialMat M F) x =
      ∑ j, S⁻¹ j k * euclideanCoordDeriv j (newtonPotential G) (matVecMul S⁻¹ x) := by
    rw [newtonPotentialMat_eq_comp hS hdet F]
    exact euclideanCoordDeriv_comp_matVecMul S⁻¹ x hu k
  have e2 : ∀ j, euclideanCoordDeriv j (newtonPotential G) (matVecMul S⁻¹ x) =
      ∑ m, S m j * newtonPotential (Gm m) (matVecMul S⁻¹ x) := by
    intro j
    have hl := congrFun (newtonPotential_linearCombination (s := Finset.univ)
      (c := fun m => S m j) hd Gm (fun m _ => (hGm_s m).continuous) fun m _ => hGm_c m)
      (matVecMul S⁻¹ x)
    rw [hD.2 j]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hl
    rw [← hl, ← hH j]
    rfl
  rw [e1, ← newtonPotential_transform hS hdet (fun y i => euclideanCoordDeriv k (fun z => F z i) y) x]
  simp only [e2, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hST : ∀ m : Fin d, ∑ j, S⁻¹ j k * (S m j) = if m = k then 1 else 0 := by
    intro m
    have := congrFun (congrFun (mul_inv_self hdet : S * S⁻¹ = 1) m) k
    simp only [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have : ∀ m : Fin d, ∑ j, S⁻¹ j k * (S m j * newtonPotential (Gm m) (matVecMul S⁻¹ x)) =
      (if m = k then 1 else 0) * newtonPotential (Gm m) (matVecMul S⁻¹ x) := by
    intro m
    rw [← hST m, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rfl


end MatChange

end PDE
