module

public import PDEFoundation.Ambient.MatrixConjugation
public import PDEFoundation.Measure.RestrictedVolume

/-! # Continuous coefficients under elliptic normalization -/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Conjugation by the elliptic normalizer preserves continuity of a
coefficient field on the corresponding linear image. -/
theorem ellipticNormalizedCoefficient_continuousOn
    {A0 : Mat d} {Lam : ℝ} (hA0 : IsEllipticMatrix 1 Lam A0)
    {U : Set (Vec d)} {a : CoeffField d} (ha : ContinuousOn a U) :
    let e := ellipticNormalizerContinuousLinearEquiv hA0
    let T := ellipticNormalizer A0
    ContinuousOn
      (fun y => T * (a (e.symm y) - skewPart A0) * matTranspose T)
      (e '' U) := by
  dsimp only
  let e := ellipticNormalizerContinuousLinearEquiv hA0
  let T := ellipticNormalizer A0
  have hae : ContinuousOn (fun y => a (e.symm y)) (e '' U) := by
    apply ha.comp e.symm.continuous.continuousOn
    rintro y ⟨x, hx, rfl⟩
    simpa using hx
  exact ((continuousOn_const.mul (hae.sub continuousOn_const)).mul continuousOn_const)

/-- Every entry of the normalized continuous coefficient is strongly
measurable on the image of an open set. -/
theorem ellipticNormalizedCoefficient_entry_aestronglyMeasurable
    {A0 : Mat d} {Lam : ℝ} (hA0 : IsEllipticMatrix 1 Lam A0)
    {U : Set (Vec d)} (hU : IsOpen U) {a : CoeffField d}
    (ha : ContinuousOn a U) (i j : Fin d) :
    let e := ellipticNormalizerContinuousLinearEquiv hA0
    let T := ellipticNormalizer A0
    AEStronglyMeasurable
      (fun y => (T * (a (e.symm y) - skewPart A0) * matTranspose T) i j)
      (volumeOn (e '' U)) := by
  dsimp only
  let e := ellipticNormalizerContinuousLinearEquiv hA0
  let T := ellipticNormalizer A0
  have hb := ellipticNormalizedCoefficient_continuousOn hA0 ha
  have hImageOpen : IsOpen (e '' U) := e.isOpenMap U hU
  have hbentry := (continuous_apply j).comp_continuousOn
    ((continuous_apply i).comp_continuousOn hb)
  change ContinuousOn
    (fun y => (T * (a (e.symm y) - skewPart A0) * matTranspose T) i j)
    (e '' U) at hbentry
  exact hbentry.aestronglyMeasurable (μ := volume) hImageOpen.measurableSet

/-- A pointwise perturbation of the given coefficient retains the same
Euclidean operator size after normalization and removal of the skew
part. -/
theorem ellipticNormalizedCoefficient_isMatrixPerturbationLE
    {A0 : Mat d} {Lam delta : ℝ} (hA0 : IsEllipticMatrix 1 Lam A0)
    (hdelta : 0 ≤ delta) {U : Set (Vec d)} {a : CoeffField d}
    (ha : ∀ x ∈ U, IsMatrixPerturbationLE delta (a x) A0) :
    let e := ellipticNormalizerContinuousLinearEquiv hA0
    let T := ellipticNormalizer A0
    ∀ y ∈ e '' U,
      IsMatrixPerturbationLE delta
        (T * (a (e.symm y) - skewPart A0) * matTranspose T) (1 : Mat d) := by
  dsimp only
  let e := ellipticNormalizerContinuousLinearEquiv hA0
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have he : e.symm (e x) = x := e.symm_apply_apply x
  rw [he]
  exact
    isMatrixPerturbationLE_ellipticNormalizer_conjugation hA0 hdelta (ha x hx)

end

end PDE
