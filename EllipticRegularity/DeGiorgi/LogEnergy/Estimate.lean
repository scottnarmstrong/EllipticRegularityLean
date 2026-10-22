module

public import EllipticRegularity.DeGiorgi.LogEnergy.Chain
public import PDEFoundation.PDE.DGNM.Caccioppoli
public import PDEFoundation.PDE.WeakInequalities

/-!
# The logarithmic energy estimate for a supersolution

Testing the supersolution inequality with `ψ u⁻¹` (`ψ ≥ 0` smooth, compactly supported) gives, for
`V = log u` and `E = ∇V · a ∇V`,
`∫ ψ E ≤ ∫ (a ∇V) · ∇ψ`.
With `ψ = η²` and the Young inequality of `Caccioppoli.lean` this yields
`∫ η² E ≤ 4 Λ ∫ |∇η|²`.
-/

@[expose] public section

namespace PDE.DGNMLogEnergy

open MeasureTheory PDE.DGNM

variable {d : ℕ} {U : Set (Vec d)} {Λ : ℝ} {a : CoeffField d}

theorem integrableOn_vecNormSq_classicalGradient {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η) :
    IntegrableOn (fun x => vecNormSq (classicalGradient η x)) U := by
  have hcont : Continuous (fun x => vecNormSq (classicalGradient η x)) :=
    continuous_vecNormSq.comp (ContDiff.continuous_classicalGradient (hη.of_le (by simp)))
  have hcs : HasCompactSupport (fun x => vecNormSq (classicalGradient η x)) := by
    refine HasCompactSupport.of_support_subset_isCompact hηc ?_
    intro x hx
    by_contra hnot
    apply hx
    have hf : fderiv ℝ η x = 0 := fderiv_of_notMem_tsupport ℝ hnot
    have hg : classicalGradient η x = 0 := by
      funext i; rw [classicalGradient_apply, hf]; rfl
    show vecNormSq (classicalGradient η x) = 0
    rw [hg]; simp [vecNormSq, vecDot]
  exact (hcont.integrable_of_hasCompactSupport hcs).integrableOn

/-- Testing a supersolution with `ψ u⁻¹`: the logarithmic Caccioppoli identity. -/
theorem logTest (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u)
    {δ : ℝ} (hδ : 0 < δ) (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u.toFun x)
    {V : H1Function U}
    (hV : ∀ᵐ x ∂volumeOn U, V.grad x = (u.toFun x)⁻¹ • u.grad x)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) (hψ0 : ∀ x, 0 ≤ ψ x) :
    IntegrableOn (fun x => ψ x * vecDot (V.grad x) (matVecMul (a x) (V.grad x))) U ∧
      IntegrableOn (fun x => vecDot (matVecMul (a x) (V.grad x)) (classicalGradient ψ x)) U ∧
      ∫ x in U, ψ x * vecDot (V.grad x) (matVecMul (a x) (V.grad x)) ≤
        ∫ x in U, vecDot (matVecMul (a x) (V.grad x)) (classicalGradient ψ x) := by
  obtain ⟨W, hWv, hWg⟩ := exists_invRep hU u hδ hu
  have hW0 : ∀ᵐ x ∂volumeOn U, 0 ≤ W x := by
    filter_upwards [hWv, hu] with x hx1 hx2
    rw [hx1]; exact inv_nonneg.mpr (hδ.le.trans hx2)
  obtain ⟨I1, I2, hle⟩ := superharmonic_productTest hU ha hEll hsuper W hW0 hψ hψc hψU hψ0
  have e1 : ∀ᵐ x ∂volumeOn U, ψ x * vecDot (matVecMul (a x) (u.grad x)) (W.grad x) =
      -(ψ x * vecDot (V.grad x) (matVecMul (a x) (V.grad x))) := by
    filter_upwards [hWg, hV, hu] with x h1 h2 h3
    have ht : u.toFun x ≠ 0 := (hδ.trans_le h3).ne'
    rw [h1, h2, vecDot_smul_right, matVecMul_smul, vecDot_smul_left, vecDot_smul_right,
      vecDot_comm (matVecMul (a x) (u.grad x)) (u.grad x)]
    field_simp
  have e2 : ∀ᵐ x ∂volumeOn U, W x * vecDot (matVecMul (a x) (u.grad x)) (classicalGradient ψ x) =
      vecDot (matVecMul (a x) (V.grad x)) (classicalGradient ψ x) := by
    filter_upwards [hWv, hV] with x h1 h2
    rw [h1, h2, matVecMul_smul, vecDot_smul_left]
  have J1 : IntegrableOn (fun x => ψ x * vecDot (V.grad x) (matVecMul (a x) (V.grad x))) U := by
    exact ((Integrable.congr I1 e1).neg).congr
      (Filter.Eventually.of_forall fun x => by simp)
  have J2 : IntegrableOn
      (fun x => vecDot (matVecMul (a x) (V.grad x)) (classicalGradient ψ x)) U :=
    Integrable.congr I2 e2
  refine ⟨J1, J2, ?_⟩
  rw [integral_congr_ae e1, integral_congr_ae e2, integral_neg] at hle
  linarith

theorem log_energy_cutoff (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u)
    {δ : ℝ} (hδ : 0 < δ) (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u.toFun x)
    {V : H1Function U}
    (hV : ∀ᵐ x ∂volumeOn U, V.grad x = (u.toFun x)⁻¹ • u.grad x)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ U) :
    IntegrableOn (fun x => η x ^ 2 * vecDot (V.grad x) (matVecMul (a x) (V.grad x))) U ∧
      ∫ x in U, η x ^ 2 * vecDot (V.grad x) (matVecMul (a x) (V.grad x)) ≤
        4 * Λ * ∫ x in U, vecNormSq (classicalGradient η x) := by
  obtain ⟨J1, J2, hle⟩ := logTest hU ha hEll hsuper hδ hu hV (contDiff_sq hη)
    (hasCompactSupport_sq hηc) (tsupport_sq_subset hηU) (fun x => sq_nonneg _)
  refine ⟨J1, ?_⟩
  set E : Vec d → ℝ := fun x => η x ^ 2 * vecDot (V.grad x) (matVecMul (a x) (V.grad x)) with hE
  have hG : IntegrableOn (fun x => vecNormSq (classicalGradient η x)) U :=
    integrableOn_vecNormSq_classicalGradient hη hηc
  have hmem : ∀ᵐ x ∂volumeOn U, x ∈ U :=
    (ae_restrict_iff' hU.measurableSet).2 (Filter.Eventually.of_forall fun _ hx => hx)
  have hpt : ∀ᵐ x ∂volumeOn U,
      vecDot (matVecMul (a x) (V.grad x)) (classicalGradient (fun y => η y ^ 2) x) ≤
        E x / 2 + 2 * Λ * vecNormSq (classicalGradient η x) := by
    filter_upwards [hmem] with x hx
    have h := abs_two_mul_mul_vecDot_le_caccioppoli (η := η x) (w := 1) (hEll x hx)
      (V.grad x) (classicalGradient η x)
    rw [classicalGradient_sq hη, vecDot_smul_right]
    have h2 := (le_abs_self _).trans h
    simp only [hE]
    nlinarith [h2]
  have hB : IntegrableOn (fun x => E x / 2 + 2 * Λ * vecNormSq (classicalGradient η x)) U :=
    (J1.div_const 2).add (hG.const_mul (2 * Λ))
  have hbound := integral_mono_ae J2 hB hpt
  have hsplit : ∫ x in U, (E x / 2 + 2 * Λ * vecNormSq (classicalGradient η x)) =
      (∫ x in U, E x) / 2 + 2 * Λ * ∫ x in U, vecNormSq (classicalGradient η x) := by
    rw [integral_add (J1.div_const 2) (hG.const_mul (2 * Λ)), integral_div,
      integral_const_mul]
  rw [hsplit] at hbound
  have hx : ∫ x in U, E x ≤ ∫ x in U, vecDot (matVecMul (a x) (V.grad x))
      (classicalGradient (fun y => η y ^ 2) x) := by
    simpa [hE, sq] using hle
  linarith

end PDE.DGNMLogEnergy
