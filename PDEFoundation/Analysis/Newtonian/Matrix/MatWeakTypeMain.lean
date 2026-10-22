module

public import PDEFoundation.Analysis.Newtonian.Matrix.MatWeakTypeScaled
public import PDEFoundation.Analysis.Newtonian.Matrix.MatWeakTypeNorms

/-!
# Local weak-type (1,1) estimate for the constant-matrix potential from the Laplacian case

Given the Laplacian estimate (with constant `C₀`) as a hypothesis, the matrix potential satisfies
the same estimate with `C = C₀ Λ`: change variables by `S` with `S Sᵀ = M`, dilate by `√Λ` and
use `|S⁻¹ v| ≤ √Λ |v|`; the determinant of `S` cancels.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace PDE

namespace MatChange

variable {d : ℕ}

theorem weakType_mat {C₀ : ℝ} (hd : 0 < d)
    (hD3 : ∀ F : Vec d → Vec d, ContDiff ℝ (⊤ : ℕ∞) F →
        tsupport F ⊆ euclideanBall (0 : Vec d) 1 →
        ∀ lam : ℝ, 0 < lam →
          volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧
              lam < vecEuclideanNorm (classicalGradient (newtonPotential F) x)} ≤
            ENNReal.ofReal (C₀ / lam * ∫ x, vecEuclideanNorm (F x)))
    (hC₀ : 0 ≤ C₀) {Λ : ℝ} (hΛ : 0 < Λ) {M : Mat d} (hMs : M.IsSymm)
    (hM : ∀ ξ : Vec d,
          Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul M ξ) ∧
            vecDot ξ (matVecMul M ξ) ≤ Λ * vecNormSq ξ)
    {F : Vec d → Vec d} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFs : tsupport F ⊆ euclideanBall (0 : Vec d) 1) {lam : ℝ} (hlam : 0 < lam) :
    volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧
        lam < vecEuclideanNorm (classicalGradient (newtonPotentialMat M F) x)} ≤
      ENNReal.ofReal (C₀ * Λ / lam * ∫ x, vecEuclideanNorm (F x)) := by
  obtain ⟨S, hS, hdet⟩ := exists_factor (posDef_of_ellipticity hΛ hMs hM)
  have hM1 : ∀ ξ : Vec d, Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul M ξ) := fun ξ => (hM ξ).1
  set s := Real.sqrt Λ with hs
  have hspos : 0 < s := Real.sqrt_pos.2 hΛ
  have hs2 : s * s = Λ := Real.mul_self_sqrt hΛ.le
  have hn2 := vecEuclideanNorm_inv_le hΛ hS hdet hM1
  have hn1 := vecEuclideanNorm_inv_transpose_le hΛ hS hdet hM1
  set G : Vec d → Vec d := fun z => matVecMul S⁻¹ (F (matVecMul S z)) with hG
  have hFc : HasCompactSupport F :=
    (isCompact_euclideanClosedBall (0 : Vec d) zero_le_one).of_isClosed_subset (isClosed_tsupport F)
      (hFs.trans (euclideanBall_subset_euclideanClosedBall _ _))
  have hGs : ContDiff ℝ (⊤ : ℕ∞) G :=
    (contDiff_matVecMul S⁻¹).comp (hF.comp (contDiff_matVecMul S))
  have hGc : HasCompactSupport G := hasCompactSupport_matVecMul_comp hdet hFc
  have hGsupp : tsupport G ⊆ euclideanBall (0 : Vec d) s := by
    have hsub : tsupport G ⊆ (fun z => matVecMul S z) ⁻¹' tsupport F := by
      refine tsupport_subset_preimage (continuous_matVecMul S) (f := F) ?_
      intro z hz
      by_contra hz'
      apply hz
      have : F (matVecMul S z) = 0 := by simpa [Function.mem_support] using hz'
      simp only [hG, this]
      funext i
      simp [matVecMul]
    intro z hz
    have h1 := hFs (hsub hz)
    have h2 := (mem_euclideanBall_iff_vecEuclideanNorm_lt one_pos).1 h1
    rw [sub_zero] at h2
    refine (mem_euclideanBall_iff_vecEuclideanNorm_lt hspos).2 ?_
    rw [sub_zero]
    have hz' : z = matVecMul S⁻¹ (matVecMul S z) := by
      rw [matVecMul_matVecMul, inv_mul_self hdet, matVecMul_one]
    calc vecEuclideanNorm z = vecEuclideanNorm (matVecMul S⁻¹ (matVecMul S z)) := by rw [← hz']
      _ ≤ s * vecEuclideanNorm (matVecMul S z) := hn2 _
      _ < s * 1 := mul_lt_mul_of_pos_left h2 hspos
      _ = s := mul_one s
  have hu : ContDiff ℝ (⊤ : ℕ∞) (newtonPotential G) := contDiff_newtonPotential hd hGs hGc
  have hpot : newtonPotentialMat M F = fun x => newtonPotential G (matVecMul S⁻¹ x) :=
    funext fun x => (newtonPotential_transform hS hdet F x).symm
  have hscaled := weakType_dilated hd hD3 (R := s) hspos hGs hGc hGsupp
    (mu := lam / s) (div_pos hlam hspos)
  -- inclusion of the level set
  set A := {x | x ∈ euclideanBall (0 : Vec d) (2 * s) ∧
        lam / s < vecEuclideanNorm (classicalGradient (newtonPotential G) x)} with hA
  have hsub : {x | x ∈ euclideanBall (0 : Vec d) 2 ∧
        lam < vecEuclideanNorm (classicalGradient (newtonPotentialMat M F) x)} ⊆
      (fun y => matVecMul S y) '' A := by
    intro x hx
    refine ⟨matVecMul S⁻¹ x, ⟨?_, ?_⟩, ?_⟩
    · have h2 := (mem_euclideanBall_iff_vecEuclideanNorm_lt two_pos).1 hx.1
      rw [sub_zero] at h2
      refine (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2 ?_
      rw [sub_zero]
      calc vecEuclideanNorm (matVecMul S⁻¹ x) ≤ s * vecEuclideanNorm x := hn2 _
        _ < s * 2 := mul_lt_mul_of_pos_left h2 hspos
        _ = 2 * s := mul_comm _ _
    · have h2 := hx.2
      rw [hpot, classicalGradient_comp_matVecMul S⁻¹ hu] at h2
      have h3 := hn1 (classicalGradient (newtonPotential G) (matVecMul S⁻¹ x))
      rw [div_lt_iff₀ hspos]
      calc lam < _ := h2
        _ ≤ _ := h3
        _ = _ := mul_comm _ _
    · show matVecMul S (matVecMul S⁻¹ x) = x
      rw [matVecMul_matVecMul, mul_inv_self hdet, matVecMul_one]
  have hGint : ∫ z, vecEuclideanNorm (G z) ≤ s * (|S.det|⁻¹ * ∫ x, vecEuclideanNorm (F x)) := by
    have hc : Continuous fun v => vecEuclideanNorm (F v) :=
      continuous_vecEuclideanNorm.comp hF.continuous
    have e := integral_comp_matVecMul hdet (fun v => vecEuclideanNorm (F v))
    have hint1 : Integrable fun z => vecEuclideanNorm (G z) :=
      (continuous_vecEuclideanNorm.comp hGs.continuous).integrable_of_hasCompactSupport
        (hGc.comp_left (g := vecEuclideanNorm) (by simp [vecEuclideanNorm, vecNormSq, vecDot]))
    have hFS : HasCompactSupport fun z => vecEuclideanNorm (F (matVecMul S z)) := by
      have := hasCompactSupport_comp_matVecMul hdet
        (hFc.comp_left (g := vecEuclideanNorm) (by simp [vecEuclideanNorm, vecNormSq, vecDot]))
      exact this
    have hint2 : Integrable fun z => s * vecEuclideanNorm (F (matVecMul S z)) :=
      ((hc.comp (continuous_matVecMul S)).integrable_of_hasCompactSupport hFS).const_mul s
    calc ∫ z, vecEuclideanNorm (G z) ≤ ∫ z, s * vecEuclideanNorm (F (matVecMul S z)) :=
          integral_mono hint1 hint2 fun z => hn2 _
      _ = s * (|S.det|⁻¹ * ∫ x, vecEuclideanNorm (F x)) := by
          rw [integral_const_mul, e]
  have hdpos : 0 < |S.det| := abs_pos.2 hdet
  have hAvol : volume A ≤ ENNReal.ofReal (C₀ / (lam / s) * ∫ x, vecEuclideanNorm (G x)) := hscaled
  calc volume _ ≤ volume ((fun y => matVecMul S y) '' A) := measure_mono hsub
    _ = ENNReal.ofReal |S.det| * volume A := by rw [volume_image_matVecMul]
    _ ≤ ENNReal.ofReal |S.det| *
        ENNReal.ofReal (C₀ / (lam / s) * ∫ x, vecEuclideanNorm (G x)) := by gcongr
    _ = ENNReal.ofReal (|S.det| * (C₀ / (lam / s) * ∫ x, vecEuclideanNorm (G x))) :=
        (ENNReal.ofReal_mul hdpos.le).symm
    _ ≤ ENNReal.ofReal (C₀ * Λ / lam * ∫ x, vecEuclideanNorm (F x)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hk : 0 ≤ C₀ / (lam / s) := by positivity
        calc |S.det| * (C₀ / (lam / s) * ∫ x, vecEuclideanNorm (G x))
            ≤ |S.det| * (C₀ / (lam / s) * (s * (|S.det|⁻¹ * ∫ x, vecEuclideanNorm (F x)))) := by
              gcongr
          _ = C₀ * (s * s) / lam * ∫ x, vecEuclideanNorm (F x) := by
              field_simp
          _ = _ := by rw [hs2]

end MatChange

end PDE
