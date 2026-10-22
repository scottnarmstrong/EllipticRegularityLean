module

public import EllipticRegularity.DeGiorgi.LogEnergy.Ball
public import PDEFoundation.PDE.DGNM.ClassAlgebra
public import PDEFoundation.PDE.DGNM.PositivePart

/-!
# The two logarithmic energy estimates

* `logEnergy d : PDE.DGNMLog.LogEnergyHyp d`;
* `posPartLogEnergy d : PDE.DGNMLog.PosPartLogEnergyHyp d`.
-/

@[expose] public section

namespace PDE.DGNMLogEnergy

open MeasureTheory PDE.DGNM

variable {d : ℕ}

/-- The logarithm of a positive supersolution bounded below is a supersolution of the equation
tested against `φ / u`: `∫ (a ∇V) · ∇φ ≥ ∫ φ ∇V · a ∇V ≥ 0`. -/
theorem superharmonic_logRep {Λ : ℝ} {a : CoeffField d}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hEll : ∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function (euclideanBall (0 : Vec d) 1)}
    (hsuper : IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) u)
    {δ : ℝ} (hδ : 0 < δ) (hu : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1), δ ≤ u.toFun x)
    {V : H1Function (euclideanBall (0 : Vec d) 1)}
    (hV : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1), V.grad x = (u.toFun x)⁻¹ • u.grad x) :
    IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) V := by
  have hU : IsOpenBoundedConvexDomain (euclideanBall (0 : Vec d) 1) :=
    isOpenBoundedConvexDomain_euclideanBall 0 one_pos
  intro φ hφ
  obtain ⟨J1, J2, hle⟩ := logTest hU ha hEll hsuper hδ hu hV φ.contDiff φ.hasCompactSupport
    φ.tsupport_subset hφ
  have hgrad : φ.grad = classicalGradient φ.toFun := rfl
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hgrad]; exact J2
  · simp
  · simp [vecDot_zero_left]
  · have hmem : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
        x ∈ euclideanBall (0 : Vec d) 1 :=
      (ae_restrict_iff' hU.measurableSet).2 (Filter.Eventually.of_forall fun _ hx => hx)
    have hnn : 0 ≤ ∫ x in euclideanBall (0 : Vec d) 1,
        φ.toFun x * vecDot (V.grad x) (matVecMul (a x) (V.grad x)) := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [hmem] with x hx
      exact mul_nonneg (hφ x) (vecDot_matVecMul_self_nonneg (hEll x hx) _)
    rw [hgrad]
    simpa [vecDot_zero_left] using hnn.trans hle

/-- **Logarithmic energy estimate** for a positive supersolution bounded below. -/
theorem logEnergy (d : ℕ) : PDE.DGNMLog.LogEnergyHyp d := by
  intro Λ a ha hEll u hδ hsuper
  obtain ⟨δ, hδ, hu⟩ := hδ
  have hU : IsOpenBoundedConvexDomain (euclideanBall (0 : Vec d) 1) :=
    isOpenBoundedConvexDomain_euclideanBall 0 one_pos
  obtain ⟨V, hV1, hV2⟩ := exists_logRep hU u hδ hu
  exact ⟨V, hV1, fun y r s hr hrs hys =>
    logEnergy_ball_bound ha hEll hsuper hδ hu hV2 y hr hrs hys⟩

/-- **Logarithmic energy estimate for `(-log u)₊`**, which is a subsolution. -/
theorem posPartLogEnergy (d : ℕ) : PDE.DGNMLog.PosPartLogEnergyHyp d := by
  intro Λ a ha hEll u hδ hsuper
  obtain ⟨δ, hδ, hu⟩ := hδ
  have hU : IsOpenBoundedConvexDomain (euclideanBall (0 : Vec d) 1) :=
    isOpenBoundedConvexDomain_euclideanBall 0 one_pos
  obtain ⟨V, hV1, hV2⟩ := exists_logRep hU u hδ hu
  have hVs := superharmonic_logRep ha hEll hsuper hδ hu hV2
  refine ⟨(-V).positivePartSubConst hU 0, ?_, ?_, ?_⟩
  · filter_upwards [hV1] with x hx
    rw [H1Function.positivePartSubConst_toFun, H1Function.neg_toFun]
    simp only [sub_zero]
    rw [hx]
  · exact subharmonicOn_positivePartSubConst hU ha hEll (subharmonicOn_neg hVs) 0
  · intro y r s hr hrs hys
    refine le_trans ?_ (logEnergy_ball_bound ha hEll hsuper hδ hu hV2 y hr hrs hys)
    have hBr : euclideanBall y r ⊆ euclideanBall (0 : Vec d) 1 :=
      (euclideanBall_mono hr.le hrs.le).trans
        (euclideanBall_subset_unit (hr.trans hrs) hys)
    refine setIntegral_mono_on ?_ ?_ (isOpen_euclideanBall y r).measurableSet ?_
    · exact (integrableOn_vecNormSq_of_memVectorL2On
        ((-V).positivePartSubConst hU 0).gradMemL2).mono_set hBr
    · exact (integrableOn_vecNormSq_of_memVectorL2On V.gradMemL2).mono_set hBr
    · intro x _
      rw [H1Function.positivePartSubConst_grad, H1Function.neg_grad]
      beta_reduce
      by_cases hx : x ∈ {z | 0 < (-V) z}
      · rw [Set.indicator_of_mem hx]
        simp [vecNormSq_neg]
      · rw [Set.indicator_of_notMem hx]
        have h0 : vecNormSq (0 : Vec d) = 0 := by simp [vecNormSq, vecDot]
        rw [h0]; exact vecNormSq_nonneg _

end PDE.DGNMLogEnergy
