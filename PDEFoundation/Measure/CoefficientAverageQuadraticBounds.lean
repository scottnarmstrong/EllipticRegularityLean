module

public import PDEFoundation.Ambient.EllipticNormalization
public import PDEFoundation.Measure.NormalizedLp
public import PDEFoundation.Sobolev.Mean

/-! # Quadratic bounds for averaged elliptic coefficients -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The literal coordinatewise average of an elliptic coefficient field has a
symmetric part between the identity and `Λ` in quadratic-form order. Entry
integrability is derived from ellipticity. -/
theorem integrableOn_and_quadratic_bounds_symmPart_coefficientAverage
    {d : ℕ} {U : Set (Vec d)} (_hUmeas : MeasurableSet U)
    (hUpos : 0 < volume U) (hUtop : volume U < ∞)
    (a : CoeffField d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hell : ∀ᵐ x ∂volumeOn U, IsEllipticMatrix 1 Λ (a x)) :
    (∀ i j, IntegrableOn (fun x => a x i j) U) ∧
    ∀ ξ : Vec d,
      vecNormSq ξ ≤ vecDot ξ (matVecMul
        (symmPart (Matrix.of (fun i j => integralAverage U (fun x => a x i j)))) ξ) ∧
      vecDot ξ (matVecMul
        (symmPart (Matrix.of (fun i j => integralAverage U (fun x => a x i j)))) ξ) ≤
        Λ * vecNormSq ξ := by
  let A0 : Mat d := Matrix.of (fun i j => integralAverage U (fun x => a x i j))
  let μ : Measure (Vec d) := normalizedVolumeOn U
  let : IsProbabilityMeasure μ :=
    isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top hUpos hUtop
  let : IsFiniteMeasure (volumeOn U) :=
    isFiniteMeasure_restrict.mpr hUtop.ne
  have hΛ0 : 0 ≤ Λ := zero_le_one.trans hΛ
  have haInt (i j : Fin d) : IntegrableOn (fun x => a x i j) U := by
    have hm : MemLp (fun x => a x i j) 1 (volumeOn U) := by
      apply MemLp.of_bound (ha i j).aestronglyMeasurable Λ
      filter_upwards [hell] with x hx
      simpa only [Real.norm_eq_abs] using
        abs_apply_le_of_isEllipticMatrix hx i j
    exact hm.integrable le_rfl
  have haIntμ (i j : Fin d) : Integrable (fun x => a x i j) μ := by
    dsimp only [μ, normalizedVolumeOn]
    apply (integrable_inv_smul_measure hUpos.ne' hUtop.ne).2
    exact haInt i j
  have hellμ : ∀ᵐ x ∂μ, IsEllipticMatrix 1 Λ (a x) := by
    dsimp only [μ, normalizedVolumeOn]
    exact Measure.ae_smul_measure hell _
  refine ⟨haInt, ?_⟩
  intro ξ
  have hquadInt : Integrable (fun x => vecDot ξ (matVecMul (a x) ξ)) μ := by
    unfold vecDot matVecMul
    apply integrable_finsetSum
    intro i _
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro j _
    exact (haIntμ i j).mul_const (ξ j)
  have haverage : vecDot ξ (matVecMul A0 ξ) =
      ∫ x, vecDot ξ (matVecMul (a x) ξ) ∂μ := by
    classical
    unfold vecDot matVecMul
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_const_mul]
      congr 1
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j _
        rw [integral_mul_const]
        dsimp only [A0, Matrix.of_apply]
        rw [← integral_normalizedVolumeOn_eq_integralAverage]
      · intro j _
        exact (haIntμ i j).mul_const (ξ j)
    · intro i _
      apply Integrable.const_mul
      apply integrable_finsetSum
      intro j _
      exact (haIntμ i j).mul_const (ξ j)
  have hlowerInt : vecNormSq ξ ≤
      ∫ x, vecDot ξ (matVecMul (a x) ξ) ∂μ := by
    calc
      vecNormSq ξ = ∫ _x, vecNormSq ξ ∂μ := by simp
      _ ≤ ∫ x, vecDot ξ (matVecMul (a x) ξ) ∂μ := by
        apply integral_mono_ae (integrable_const _) hquadInt
        filter_upwards [hellμ] with x hx
        simpa only [one_mul] using hx.coercive ξ
  have hupperInt : (∫ x, vecDot ξ (matVecMul (a x) ξ) ∂μ) ≤
      Λ * vecNormSq ξ := by
    calc
      (∫ x, vecDot ξ (matVecMul (a x) ξ) ∂μ) ≤
          ∫ _x, Λ * vecNormSq ξ ∂μ := by
        apply integral_mono_ae hquadInt (integrable_const _)
        filter_upwards [hellμ] with x hx
        rw [← vecDot_symmPart_matVecMul]
        exact symmPart_quadratic_upper_of_isEllipticMatrix hx ξ
      _ = Λ * vecNormSq ξ := by simp
  rw [vecDot_symmPart_matVecMul]
  exact ⟨haverage ▸ hlowerInt, haverage ▸ hupperInt⟩

end

end PDE
