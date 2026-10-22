module

public import PDEFoundation.Ambient.QuadraticMatrixConjugation
public import PDEFoundation.Measure.LinearVolume

/-! # Coefficient transport under quadratic elliptic normalization -/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

/-- The literal coefficient obtained by removing the skew part and
conjugating through the quadratic elliptic normalizer. -/
def quadraticCoefficientTransport
    {d : ℕ} {A0 : Mat d}
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi))
    (a : Vec d → Mat d) (y : Vec d) : Mat d :=
  let T := ellipticNormalizer A0
  let e := quadraticEllipticNormalizerContinuousLinearEquiv hLower
  T * (a (e.symm y) - skewPart A0) * matTranspose T

private theorem quasiMeasurePreserving_linearEquiv_symm_volumeOn
    {d : ℕ} (e : Vec d ≃L[ℝ] Vec d) (U : Set (Vec d)) :
    Measure.QuasiMeasurePreserving e.symm
      (volumeOn (e '' U)) (volumeOn U) := by
  have hset : e.symm '' (e '' U) = U := by
    ext x
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      simpa only [e.symm_apply_apply] using hu
    · intro hx
      exact ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩
  refine ⟨e.symm.continuous.measurable, ?_⟩
  rw [map_linearEquiv_volumeOn, hset]
  exact Measure.smul_absolutelyContinuous

/-- Coordinate measurability of a coefficient field transports to the exact
linear image domain under quadratic elliptic normalization. -/
theorem aemeasurable_quadraticCoefficientTransport_entry
    {d : ℕ} {U : Set (Vec d)} {A0 : Mat d}
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi))
    {a : Vec d → Mat d}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (i j : Fin d) :
    AEMeasurable
      (fun y => quadraticCoefficientTransport hLower a y i j)
      (volumeOn
        (quadraticEllipticNormalizerContinuousLinearEquiv hLower '' U)) := by
  let e := quadraticEllipticNormalizerContinuousLinearEquiv hLower
  let T := ellipticNormalizer A0
  have hqmp : Measure.QuasiMeasurePreserving e.symm
      (volumeOn (e '' U)) (volumeOn U) :=
    quasiMeasurePreserving_linearEquiv_symm_volumeOn e U
  have hcomp : ∀ k l, AEMeasurable (fun y => a (e.symm y) k l)
      (volumeOn (e '' U)) := fun k l =>
    (ha k l).comp_quasiMeasurePreserving hqmp
  change AEMeasurable
    (fun y => (T * (a (e.symm y) - skewPart A0) * matTranspose T) i j)
      (volumeOn (e '' U))
  simp only [Matrix.mul_apply, Matrix.sub_apply]
  have hinner (k : Fin d) : AEMeasurable
      (fun y => ∑ l : Fin d,
        T i l * (a (e.symm y) l k - skewPart A0 l k))
      (volumeOn (e '' U)) := by
    have h := Finset.aemeasurable_sum Finset.univ (fun l _hl =>
      AEMeasurable.const_mul ((hcomp l k).sub_const (skewPart A0 l k)) (T i l))
    convert h using 1
    funext y
    simp only [Finset.sum_apply]
  have h := Finset.aemeasurable_sum Finset.univ (fun k _hk =>
    (hinner k).mul_const (matTranspose T k j))
  convert h using 1
  funext y
  simp only [Finset.sum_apply]

/-- The perturbation size is unchanged by quadratic coefficient transport. -/
theorem ae_isMatrixPerturbationLE_quadraticCoefficientTransport
    {d : ℕ} {U : Set (Vec d)} {A0 : Mat d} {delta : ℝ}
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi))
    (hdelta : 0 ≤ delta) {a : Vec d → Mat d}
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) A0) :
    ∀ᵐ y ∂volumeOn
        (quadraticEllipticNormalizerContinuousLinearEquiv hLower '' U),
      IsMatrixPerturbationLE delta
        (quadraticCoefficientTransport hLower a y) (1 : Mat d) := by
  let e := quadraticEllipticNormalizerContinuousLinearEquiv hLower
  have hqmp : Measure.QuasiMeasurePreserving e.symm
      (volumeOn (e '' U)) (volumeOn U) :=
    quasiMeasurePreserving_linearEquiv_symm_volumeOn e U
  filter_upwards [hqmp.ae hclose] with y hy
  exact
    isMatrixPerturbationLE_ellipticNormalizer_conjugation_of_quadratic_lower
      hLower hdelta hy

end

end PDE
