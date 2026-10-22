module

public import PDEFoundation.Analysis.Newtonian.Defs
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Generic radial kernel `z ↦ k (|z|^d)⁻¹ z` and its derivative

For an arbitrary constant `k`, the kernel `kerField k` and the matrix `kerJac k` satisfy
`HasFDerivAt (kerField k) (toLin' (kerJac k z)) z` for `z ≠ 0`, and `kerField k` is smooth off `0`.
-/

@[expose] public section

namespace PDE

namespace NewtonKernelAux

/-- The radial profile `t ↦ ((√t)^d)⁻¹`. -/
noncomputable def kerProfile (d : ℕ) (t : ℝ) : ℝ := ((Real.sqrt t) ^ d)⁻¹

theorem kerProfile_hasDerivAt (d : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (kerProfile d)
      (-( (d : ℝ) * (Real.sqrt t ^ d)⁻¹ / (2 * t))) t := by
  have h1 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt t)) t := by
    exact Real.hasDerivAt_sqrt ht.ne'
  have h2 := (h1.fun_pow d)
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h3 := HasDerivAt.inv h2 (pow_ne_zero d hs.ne')
  unfold kerProfile
  convert h3 using 1
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  rcases d with _ | d
  · simp
  · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    generalize Real.sqrt t = r at *
    subst hsq
    field_simp
    ring

theorem vecNormSq_hasFDerivAt {d : ℕ} (z : Vec d) :
    HasFDerivAt (fun x : Vec d => vecNormSq x)
      (∑ i : Fin d, (2 * z i) • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)) z := by
  have : (fun x : Vec d => vecNormSq x) = fun x => ∑ i : Fin d, x i ^ 2 := by
    funext x; exact vecNormSq_eq_sum_sq x
  rw [this]
  apply HasFDerivAt.fun_sum
  intro i _
  have h : HasFDerivAt (fun x : Vec d => x i) (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ) z := hasFDerivAt_apply i z
  have := h.pow 2
  convert this using 1
  ext v
  simp [two_mul]
  

/-- The generic radial kernel `z ↦ (k (|z|^d)⁻¹) • z`. -/
noncomputable def kerField {d : ℕ} (k : ℝ) (z : Vec d) : Vec d :=
  (k * kerProfile d (vecNormSq z)) • z

/-- The Jacobian matrix of `kerField`. -/
noncomputable def kerJac {d : ℕ} (k : ℝ) (z : Vec d) : Mat d :=
  fun i j => ((if i = j then (1 : ℝ) else 0) - (d : ℝ) * (z i * z j) / vecNormSq z) *
    (k * kerProfile d (vecNormSq z))

theorem kerField_hasFDerivAt {d : ℕ} (k : ℝ) {z : Vec d} (hz : z ≠ 0) :
    HasFDerivAt (kerField (d := d) k)
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (kerJac k z))) z := by
  have hn : 0 < vecNormSq z := lt_of_le_of_ne (vecNormSq_nonneg z)
    (fun h => hz (vecNormSq_eq_zero h.symm))
  have h1 := (kerProfile_hasDerivAt d hn).comp_hasFDerivAt z (vecNormSq_hasFDerivAt z)
  have h2 := (h1.const_mul k)
  have h3 := h2.smul (hasFDerivAt_id z)
  refine (show HasFDerivAt (kerField (d := d) k) _ z from h3).congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro v
  funext i
  simp only [kerJac, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    add_apply, smul_apply, id,
    ContinuousLinearMap.smulRight_apply, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    ContinuousLinearMap.proj_apply, Function.comp, Pi.add_apply, Pi.smul_apply, smul_eq_mul, vecNormSq, vecDot]
  rw [ContinuousLinearMap.id_apply]
  have hS : ∑ c, 2 * z c * v c = 2 * ∑ c, z c * v c := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
  have hR : ∑ j, ((if i = j then (1 : ℝ) else 0) - (d : ℝ) * (z i * z j) / ∑ i, z i * z i) *
        (k * kerProfile d (∑ i, z i * z i)) * v j =
      k * kerProfile d (∑ i, z i * z i) * v i -
        (d : ℝ) * z i * (∑ j, z j * v j) / (∑ i, z i * z i) * (k * kerProfile d (∑ i, z i * z i)) := by
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    rw [Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hR, hS]
  have hn' : (∑ i, z i * z i) ≠ 0 := hn.ne'
  unfold kerProfile
  field_simp
  ring


theorem kerProfile_contDiffAt (d : ℕ) {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ (⊤ : ℕ∞) (kerProfile d) t := by
  unfold kerProfile
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) Real.sqrt t := Real.contDiffAt_sqrt ht.ne'
  refine (hs.pow d).inv ?_
  exact pow_ne_zero d (Real.sqrt_pos.mpr ht).ne'

theorem vecNormSq_contDiff {d : ℕ} : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => vecNormSq x) := by
  have : (fun x : Vec d => vecNormSq x) = fun x => ∑ i : Fin d, x i ^ 2 := by
    funext x; exact vecNormSq_eq_sum_sq x
  rw [this]
  fun_prop

theorem kerField_contDiffOn {d : ℕ} (k : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (kerField (d := d) k) {(0 : Vec d)}ᶜ := by
  intro z hz
  have hz' : z ≠ 0 := hz
  have hn : 0 < vecNormSq z := lt_of_le_of_ne (vecNormSq_nonneg z)
    (fun h => hz' (vecNormSq_eq_zero h.symm))
  refine ContDiffAt.contDiffWithinAt ?_
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : Vec d => kerProfile d (vecNormSq x)) z :=
    (kerProfile_contDiffAt d hn).comp z vecNormSq_contDiff.contDiffAt
  exact (h1.const_smul k |>.smul contDiffAt_id) 

end NewtonKernelAux

end PDE
