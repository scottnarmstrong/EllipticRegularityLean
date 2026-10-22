module

public import PDEFoundation.Geometry.ConvexNormalizationBall

/-!
# Affine normalization of convex domains

A nonempty bounded open convex set `V` with Euclidean diameter at most `D`
is mapped by an invertible affine map `x ↦ A x + b` between the Euclidean
unit ball and the Euclidean ball of radius `R_d = √d (1 + d + √d)`, with
`|A⁻¹ e| ≤ D / 2 · |e|`. All balls and norms are Euclidean.
-/

@[expose] public section

open Set

namespace PDE

/-- The radius `R_d = √d (1 + d + √d)` of the outer ball in the affine
normalization of convex domains. -/
noncomputable def convexNormalizationRadius (d : ℕ) : ℝ :=
  Real.sqrt d * (1 + d + Real.sqrt d)

/-- Affine normalization of convex domains. -/
theorem exists_affine_normalization {d : ℕ} (hd : 1 ≤ d) {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty) {D : ℝ}
    (hD : HasEuclideanDiameterLE V D) :
    ∃ (A : Vec d ≃L[ℝ] Vec d) (b : Vec d),
      euclideanBall (0 : Vec d) 1 ⊆ (fun x => A x + b) '' V ∧
      (fun x => A x + b) '' V ⊆ euclideanBall (0 : Vec d) (convexNormalizationRadius d) ∧
      ∀ e : Vec d, vecEuclideanNorm (A.symm e) ≤ D / 2 * vecEuclideanNorm e := by
  obtain ⟨v, hvK, hM, hmax⟩ := exists_maxSimplex hV.isOpen hV.isBoundedDomain hne
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set M := simplexMat v with hMdef
  set r : ℝ := (Real.sqrt d + d : ℝ)⁻¹ with hr
  have hrpos : 0 < r := by positivity
  have hrr : r * (Real.sqrt d + d) = 1 := inv_mul_cancel₀ (by positivity)
  set N : Mat d := r⁻¹ • M⁻¹ with hN
  have hNM : N * (r • M) = 1 := by
    rw [hN, smul_mul_assoc, Matrix.mul_smul, smul_smul, Matrix.nonsing_inv_mul _ hM.isUnit]
    simp [hrpos.ne']
  have hMN : (r • M) * N = 1 := by
    rw [hN, Matrix.mul_smul, smul_mul_assoc, smul_smul, Matrix.mul_nonsing_inv _ hM.isUnit]
    simp [hrpos.ne']
  let A : Vec d ≃L[ℝ] Vec d :=
    (LinearEquiv.ofLinearMap (Matrix.toLin' N) (Matrix.toLin' (r • M))
      (by rw [← Matrix.toLin'_mul, hNM, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, hMN, Matrix.toLin'_one])).toContinuousLinearEquiv
  have hA : ∀ x, A x = N.mulVec x := fun x => by
    simp [A, LinearEquiv.coe_ofLinearMap, Matrix.toLin'_apply]
  have hAsymm : ∀ e, A.symm e = r • M.mulVec e := fun e => by
    rw [ContinuousLinearEquiv.symm_apply_eq, hA, ← Matrix.smul_mulVec, Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
  let b : Vec d := -(N.mulVec (v 0)) - 1
  have hT : ∀ x, A x + b = r⁻¹ • M⁻¹.mulVec (x - v 0) - 1 := fun x => by
    rw [hA]
    simp only [b, hN, Matrix.smul_mulVec, Matrix.mulVec_sub, smul_sub]
    abel
  -- the normalized coordinates of `x`
  have hcoord : ∀ x ∈ V, ∀ i, |(M⁻¹.mulVec (x - v 0)) i| < 1 := fun x hx i =>
    abs_coord_lt_one_of_mem hV.isOpen hmax hx (simplexMat_mulVec_inv_mulVec hM _) i
  have hin : euclideanBall (0 : Vec d) 1 ⊆ (fun x => A x + b) '' V := by
    intro e he
    have hR : 0 < (1 : ℝ) := one_pos
    have he' : vecEuclideanNorm e < 1 := by
      simpa [(mem_euclideanBall_iff_vecEuclideanNorm_lt hR)] using he
    set x : Vec d := v 0 + M.mulVec (r • (e + 1)) with hx
    have hxv : x - v 0 = M.mulVec (r • (e + 1)) := by rw [hx]; abel
    have hy : M⁻¹.mulVec (x - v 0) = r • (e + 1) := by
      rw [hxv, simplexMat_inv_mulVec_mulVec hM]
    refine ⟨x, mem_of_barycentric_ball hd hV hne hvK hM ?_, ?_⟩
    · rw [hy]
      have : r • (e + 1) - r • (1 : Vec d) = r • e := by rw [smul_add]; abel
      rw [this, vecEuclideanNorm_smul, abs_of_pos hrpos]
      exact (mul_lt_iff_lt_one_right hrpos).2 he'
    · simp only [hT, hy, smul_smul, inv_mul_cancel₀ hrpos.ne', one_smul]
      abel
  refine ⟨A, b, hin, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hRpos : 0 < convexNormalizationRadius d := by
      unfold convexNormalizationRadius; positivity
    show A x + b ∈ euclideanBall (0 : Vec d) (convexNormalizationRadius d)
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hRpos, sub_zero, hT]
    set y := M⁻¹.mulVec (x - v 0) with hy
    have hyn : ‖y - r • (1 : Vec d)‖ < 1 + r := by
      have hy1 : ‖y‖ < 1 := by
        rw [pi_norm_lt_iff one_pos]
        intro i; simpa [Real.norm_eq_abs] using hcoord x hx i
      have hr1 : ‖r • (1 : Vec d)‖ ≤ r := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos]
        have : ‖(1 : Vec d)‖ ≤ 1 := by
          rw [pi_norm_le_iff_of_nonneg zero_le_one]; intro j; simp
        nlinarith
      calc ‖y - r • (1 : Vec d)‖ ≤ ‖y‖ + ‖r • (1 : Vec d)‖ := norm_sub_le _ _
        _ < 1 + r := by linarith
    have hz : r⁻¹ • y - 1 = r⁻¹ • (y - r • (1 : Vec d)) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hrpos.ne', one_smul]
    rw [hz, vecEuclideanNorm_smul, abs_of_pos (inv_pos.2 hrpos)]
    calc r⁻¹ * vecEuclideanNorm (y - r • (1 : Vec d))
        ≤ r⁻¹ * (Real.sqrt d * ‖y - r • (1 : Vec d)‖) :=
          mul_le_mul_of_nonneg_left (vecEuclideanNorm_le_sqrt_natCast_mul_norm _)
            (inv_pos.2 hrpos).le
      _ < r⁻¹ * (Real.sqrt d * (1 + r)) := by
          refine mul_lt_mul_of_pos_left ?_ (inv_pos.2 hrpos)
          exact mul_lt_mul_of_pos_left hyn hsd
      _ = convexNormalizationRadius d := by
          have : r⁻¹ = Real.sqrt d + d := by rw [hr, inv_inv]
          unfold convexNormalizationRadius
          rw [mul_comm, mul_assoc]
          rw [show (1 + r) * r⁻¹ = r⁻¹ + 1 by field_simp]
          rw [this]; ring
  · intro e
    by_cases he0 : e = 0
    · simp [he0, (vecEuclideanNorm_eq_zero_iff (d := d)).2 rfl]
    have hn : 0 < vecEuclideanNorm e := vecEuclideanNorm_pos_iff.2 he0
    have hD0 : 0 ≤ D := hD.nonneg hne
    set n := vecEuclideanNorm e with hndef
    set c := vecEuclideanNorm (A.symm e) with hcdef
    have hkey : ∀ t : ℝ, 0 < t → t < 1 → 2 * t * c ≤ D * n := by
      intro t ht0 ht1
      have hu : (t / n) • e ∈ euclideanBall (0 : Vec d) 1 := by
        rw [mem_euclideanBall_iff_vecEuclideanNorm_lt one_pos, sub_zero,
          vecEuclideanNorm_smul, abs_of_pos (div_pos ht0 hn), ← hndef,
          div_mul_cancel₀ _ hn.ne']
        exact ht1
      have hu' : -((t / n) • e) ∈ euclideanBall (0 : Vec d) 1 := by
        rw [mem_euclideanBall_iff_vecEuclideanNorm_lt one_pos, sub_zero, vecEuclideanNorm_neg]
        rw [mem_euclideanBall_iff_vecEuclideanNorm_lt one_pos, sub_zero] at hu
        exact hu
      obtain ⟨x₁, hx₁, hx₁'⟩ := hin hu
      obtain ⟨x₂, hx₂, hx₂'⟩ := hin hu'
      have hsub : x₁ - x₂ = ((2 * t) / n) • A.symm e := by
        have : A (x₁ - x₂) = ((2 * t) / n) • e := by
          rw [map_sub]
          have h1 : A x₁ = (t / n) • e - b := eq_sub_of_add_eq hx₁'
          have h2 : A x₂ = -((t / n) • e) - b := eq_sub_of_add_eq hx₂'
          rw [h1, h2]
          ext j
          simp only [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
          ring
        calc x₁ - x₂ = A.symm (A (x₁ - x₂)) := (A.symm_apply_apply _).symm
          _ = A.symm (((2 * t) / n) • e) := by rw [this]
          _ = ((2 * t) / n) • A.symm e := map_smul _ _ _
      have hdist := hD hx₁ hx₂
      rw [hsub, vecEuclideanNorm_smul, abs_of_pos (div_pos (by linarith) hn), ← hcdef] at hdist
      rw [div_mul_eq_mul_div, div_le_iff₀ hn] at hdist
      exact hdist
    by_contra hcon
    push Not at hcon
    have hcpos : 0 < c := by
      have : 0 ≤ D / 2 * n := by positivity
      linarith
    have := hkey ((D / 2 * n + c) / (2 * c)) (by positivity)
      (by rw [div_lt_one (by positivity)]; linarith)
    have h2 : 2 * ((D / 2 * n + c) / (2 * c)) * c = D / 2 * n + c := by
      field_simp
    linarith

end PDE
