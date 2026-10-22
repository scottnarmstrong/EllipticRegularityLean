module

public import EllipticRegularity.CalderonZygmund.IdentityBall
public import PDEFoundation.PDE.QuadraticEllipticChange
public import PDEFoundation.Measure.QuadraticCoefficientTransport
public import PDEFoundation.Measure.QuadraticForcingTransport
public import PDEFoundation.Sobolev.H1.QuadraticEllipticMean
public import PDEFoundation.Geometry.EuclideanBall.QuadraticEllipticImage

@[expose] public section

namespace PDE
open MeasureTheory Set
open scoped _root_.ENNReal
noncomputable section

/-- The actual identity CZ estimate transported to inverse normalized balls.
The dimension-only constant is chosen before the ellipticity, given matrix,
exponent, coefficients, solution, forcing, and center. The norm comparison
uses only the lower and upper quadratic bounds of the given matrix. -/
theorem exists_calderonZygmund_quadratic_ellipsoid_constants
    (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (Lam : ℝ) (_hLam : 1 ≤ Lam) (A0 : Mat d)
        (hLower : ∀ xi : Vec d, vecNormSq xi ≤ vecDot xi (matVecMul A0 xi)),
      (∀ xi : Vec d,
        vecDot xi (matVecMul (symmPart A0) xi) ≤ Lam * vecNormSq xi) →
      ∀ (p : ℝ), 2 ≤ p →
      ∀ (a : CoeffField d),
      (∀ i j, AEMeasurable (fun x => a x i j)
        (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
        IsMatrixPerturbationLE (1 / (C * p)) (a x) A0) →
      ∀ (u : H1Function (euclideanBall (0 : Vec d) 1)) (F : Vec d → Vec d),
      (∀ i, AEStronglyMeasurable (fun x => F x i)
        (volumeOn (euclideanBall (0 : Vec d) 1))) →
      MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
        (volumeOn (euclideanBall (0 : Vec d) 1)) →
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u 0 F →
      ∀ (z : Vec d), z ∈ euclideanClosedBall (0 : Vec d) (1 / 2) →
      let e := quadraticEllipticNormalizerContinuousLinearEquiv hLower
      let rho := 1 / (4 * Real.sqrt Lam)
      let E := e.symm '' euclideanBall (e z) rho
      let V := e.symm '' euclideanBall (e z) (rho / 2)
      ∃ (hEpos : 0 < volume E)
        (hVpos : 0 < volume V)
        (hFE : MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) (volumeOn E))
        (hgrad : MemLp (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p) (volumeOn V)),
        euclideanFieldLpMeanNormOn V (ENNReal.ofReal p) u.grad
            (memLp_normalizedVolumeOn_of_memLpOn hgrad hVpos) ≤
          C * (Real.sqrt Lam * Real.sqrt (integralAverage E (fun x => vecNormSq (u.grad x))) +
            p * euclideanFieldLpMeanNormOn E (ENNReal.ofReal p) F
              (memLp_normalizedVolumeOn_of_memLpOn hFE hEpos)) := by
  obtain ⟨C, hC, hIdentity⟩ := exists_calderonZygmund_identity_ball_constants d hd
  refine ⟨C, hC, ?_⟩
  intro Lam hLam A0 hLower hUpper p hp a ha hclose u F hFcoord hF hsol z hz
  dsimp only
  let e := quadraticEllipticNormalizerContinuousLinearEquiv hLower
  let rho := 1 / (4 * Real.sqrt Lam)
  let B := euclideanBall (e z) rho
  let BH := euclideanBall (e z) (rho / 2)
  let E := e.symm '' B
  let V := e.symm '' BH
  have hrho : 0 < rho := by
    have : 0 < Real.sqrt Lam := Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hLam)
    dsimp only [rho]
    positivity
  have hEunit : E ⊆ euclideanBall (0 : Vec d) 1 :=
    quadraticEllipticNormalizer_symm_image_quarter_subset_unitBall hLam hLower hUpper hz
  have hBHsub : BH ⊆ B := euclideanBall_mono (by positivity) (by linarith)
  have hVE : V ⊆ E := image_mono hBHsub
  have hEB : e '' E = B :=
    quadraticEllipticNormalizer_image_symm_image_euclideanBall hLower z
  have hVBH : e '' V = BH :=
    quadraticEllipticNormalizer_image_symm_image_euclideanBall hLower z
  have hEopen : IsOpen E := e.symm.toHomeomorph.isOpenMap _ (isOpen_euclideanBall _ _)
  have hVopen : IsOpen V := e.symm.toHomeomorph.isOpenMap _ (isOpen_euclideanBall _ _)
  have hEpos : 0 < volume E := volume_image_linearEquiv_pos e.symm (volume_euclideanBall_pos _ hrho)
  have hEtop : volume E < ⊤ := volume_image_linearEquiv_lt_top e.symm
    (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ hrho.le))
  have hVpos : 0 < volume V := volume_image_linearEquiv_pos e.symm
    (volume_euclideanBall_pos _ (by positivity))
  have hVtop : volume V < ⊤ := volume_image_linearEquiv_lt_top e.symm
    (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ (by positivity)))
  let uE := u.restrict hEopen hEunit
  let vraw := uE.compLinearEquiv e
  let v : H1Function B := vraw.restrict (isOpen_euclideanBall _ _) (hEB ▸ Set.Subset.rfl)
  let b := quadraticCoefficientTransport hLower a
  let G : Vec d → Vec d := fun y => matVecMul (ellipticNormalizer A0) (F (e.symm y))
  have haE : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn E) :=
    fun i j => (ha i j).mono_measure (Measure.restrict_mono hEunit le_rfl)
  have hb : ∀ i j, AEMeasurable (fun y => b y i j) (volumeOn B) := by
    intro i j
    have hh := aemeasurable_quadraticCoefficientTransport_entry hLower haE i j
    rw [hEB] at hh
    exact hh
  have hdelta : 0 ≤ 1 / (C * p) := by positivity
  have hcloseE : ∀ᵐ x ∂volumeOn E, IsMatrixPerturbationLE (1 / (C * p)) (a x) A0 :=
    ae_mono (Measure.restrict_mono hEunit le_rfl) hclose
  have hbclose : ∀ᵐ y ∂volumeOn B, IsMatrixPerturbationLE (1 / (C * p)) (b y) 1 := by
    have hh := ae_isMatrixPerturbationLE_quadraticCoefficientTransport hLower hdelta hcloseE
    rw [hEB] at hh
    exact hh
  have hFcoordE : ∀ i, AEStronglyMeasurable (fun x => F x i) (volumeOn E) :=
    fun i => (hFcoord i).mono_measure (Measure.restrict_mono hEunit le_rfl)
  have hFE : MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) (volumeOn E) :=
    hF.mono_measure (Measure.restrict_mono hEunit le_rfl)
  obtain ⟨hGcoordX, hGX, hGle⟩ := quadraticEllipticNormalizer_forcing_memLp_and_mean_le
    hEpos hEtop hLower F hFcoordE hFE
  have hGcoord : ∀ i, AEStronglyMeasurable (fun y => G y i) (volumeOn B) := by
    rw [hEB] at hGcoordX
    exact hGcoordX
  have hG : MemLp (fun y => vecEuclideanNorm (G y)) (ENNReal.ofReal p) (volumeOn B) := by
    rw [hEB] at hGX
    exact hGX
  have hsolE := hsol.restrict (isOpen_euclideanBall _ _) hEopen hEunit
  have hsolX := hsolE.quadraticEllipticNormalize hLower
  have hopenX : IsOpen (e '' E) := by
    rw [hEB]
    exact isOpen_euclideanBall _ _
  have hsolB : IsWeakDivergenceFormSolutionOn b B v 0 G := by
    simpa only [b, G, v, vraw, uE, quadraticCoefficientTransport, Pi.zero_apply] using!
      hsolX.restrict hopenX (isOpen_euclideanBall _ _) (hEB ▸ Set.Subset.rfl)
  obtain ⟨_, hgradB, hestB⟩ := hIdentity p hp rho hrho (e z) b hb hbclose v G hGcoord hG hsolB
  let uV := u.restrict hVopen (hVE.trans hEunit)
  have hcompGradEq : (uV.compLinearEquiv e).grad = v.grad := by
    funext y
    ext i
    simp only [uV, v, vraw, uE, H1Function.restrict_grad,
      H1Function.compLinearEquiv_grad_apply]
  have hgradVX : MemLp (fun y => vecEuclideanNorm ((uV.compLinearEquiv e).grad y))
      (ENNReal.ofReal p) (volumeOn (e '' V)) := by
    rw [hcompGradEq, hVBH]
    exact hgradB
  obtain ⟨hgradV, hnormV⟩ :=
    uV.exists_grad_memLp_and_lpMeanNorm_le_comp_quadraticEllipticNormalizer
      hLower hVpos hVtop (ENNReal.ofReal p) hgradVX
  have hgrad : MemLp (fun x => vecEuclideanNorm (u.grad x))
      (ENNReal.ofReal p) (volumeOn V) := hgradV
  have hEnergy := uE.sqrt_integralAverage_comp_quadraticEllipticNormalizer_grad_le
    hLam hLower hUpper hEpos hEtop
  change Real.sqrt (integralAverage (e '' E) (fun y => vecNormSq (vraw.grad y))) ≤
    Real.sqrt Lam * Real.sqrt (integralAverage E (fun x => vecNormSq (u.grad x))) at hEnergy
  change Real.sqrt (integralAverage (e '' E) (fun y => vecNormSq (v.grad y))) ≤ _ at hEnergy
  rw [hEB] at hEnergy
  change (eLpNorm (fun y => vecEuclideanNorm (G y)) (ENNReal.ofReal p)
      (normalizedVolumeOn (e '' E))).toReal ≤
    (eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
      (normalizedVolumeOn E)).toReal at hGle
  rw [hEB] at hGle
  change (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
      (normalizedVolumeOn V)).toReal ≤
    (eLpNorm (fun y => vecEuclideanNorm ((uV.compLinearEquiv e).grad y))
      (ENNReal.ofReal p) (normalizedVolumeOn (e '' V))).toReal at hnormV
  rw [hcompGradEq, hVBH] at hnormV
  refine ⟨hEpos, hVpos, hFE, hgrad, ?_⟩
  change (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
      (normalizedVolumeOn V)).toReal ≤ _
  apply hnormV.trans
  apply hestB.trans
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC)
  exact add_le_add hEnergy (mul_le_mul_of_nonneg_left hGle (by linarith only [hp]))

end
end PDE
