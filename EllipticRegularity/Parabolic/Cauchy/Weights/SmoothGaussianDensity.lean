module

public import EllipticRegularity.Parabolic.Cauchy.Weights.SmoothGaussian
public import EllipticRegularity.Parabolic.Cauchy.Weights.EnergyDensity
public import EllipticRegularity.Parabolic.Cauchy.Weights.SmoothEnergy
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Density inequality for the smooth shifted Gaussian weight

This file plugs the mollified truncated distance weight into the whole-space
weighted energy inequality. The only coefficient input is pointwise
ellipticity, so the final slab statement is an almost-everywhere consequence
of the parabolic coefficient hypothesis.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Weights

open MeasureTheory Set

variable {d : ℕ}

/-- The Nash--Aronson Gaussian weight satisfies the exact pointwise density
inequality needed by the weighted energy identity. -/
theorem nashSmoothGaussian_weightedDensity_pointwise {K : Set (Vec d)}
    (hK : K.Nonempty) {R Lam A σ s : ℝ} (hR : 0 ≤ R) (hLam : 0 ≤ Lam)
    (hA : Lam < A) (hσ : 0 < σ) (n : ℕ) (z : Vec d × ℝ)
    (hforward : s ≤ z.2)
    {M : Mat d} (hM : IsEllipticMatrix 1 Lam M) (u : ℝ) (v : Vec d) :
    u ^ 2 * nashSmoothGaussianWeight K R A σ s n z *
        parTimeDeriv (nashSmoothGaussianWeight K R A σ s n) z ≤
      nashSmoothGaussianWeight K R A σ s n z ^ 2 *
          vecDot v (matVecMul M v) +
        2 * nashSmoothGaussianWeight K R A σ s n z * u *
          vecDot (matVecMul M v)
            (parSpaceGrad (nashSmoothGaussianWeight K R A σ s n) z) -
        ((1 - Lam / A) *
          truncatedDistanceMollify K R n z.1 ^ 2 *
          nashSmoothGaussianWeight K R A σ s n z ^ 2 * u ^ 2 /
          (4 * A * nashPositiveTimeShift σ (z.2 - s) ^ 2)) := by
  let ρ := truncatedDistanceMollify K R n
  let τ := nashPositiveTimeShift σ (z.2 - s)
  let q := ρ z.1 ^ 2
  let W := nashSmoothGaussianWeight K R A σ s n z
  let p := parSpaceGrad (nashSmoothGaussianExponent K R A σ s n) z
  have hτlower := nashPositiveTimeShift_lower (t := z.2 - s) hσ
  have hτpos : 0 < τ := by
    have hσ2 : 0 < σ / 2 := by positivity
    dsimp [τ]
    linarith
  have hApos : 0 < A := lt_of_le_of_lt hLam hA
  have hρrange := (truncatedDistanceMollify_properties hK hR n).2.1 z.1
  have hgradρ := nashSmoothGaussianExponent_spatialGrad_bound
    (s := s) (t := z.2) hK hR hApos hσ n z.1
  have hgradρ' : vecEuclideanNorm p ≤ ρ z.1 / (2 * A * τ) := by
    simpa [p, ρ, τ] using hgradρ
  have hscale : 0 < 2 * A * τ := by positivity
  have hnormNonneg : 0 ≤ vecEuclideanNorm p := vecEuclideanNorm_nonneg p
  have hgradSq : (vecEuclideanNorm p) ^ 2 ≤
      (ρ z.1 / (2 * A * τ)) ^ 2 := by
    nlinarith
  have hcoeff : 0 ≤ 16 * A ^ 2 * τ ^ 2 := by positivity
  have hgrad : 16 * A ^ 2 * τ ^ 2 * vecNormSq p ≤ 4 * q := by
    rw [← vecEuclideanNorm_sq p]
    have hmul := mul_le_mul_of_nonneg_left hgradSq hcoeff
    have hden : 2 * A * τ ≠ 0 := ne_of_gt hscale
    have hnum :
        16 * A ^ 2 * τ ^ 2 * (ρ z.1 / (2 * A * τ)) ^ 2 = 4 * q := by
      dsimp [q]
      field_simp [hden]
      ring
    calc
      16 * A ^ 2 * τ ^ 2 * (vecEuclideanNorm p) ^ 2 ≤
          16 * A ^ 2 * τ ^ 2 * (ρ z.1 / (2 * A * τ)) ^ 2 := hmul
      _ = 4 * q := hnum
  have hfull := nashGaussianWeight_fullEnergy_density hLam hA hτpos hM u v p hgrad
  have hstep : PDE.smoothPositivePartStep (-σ / 4) (σ / 8) (z.2 - s) = 1 := by
    apply PDE.smoothPositivePartStep_eq_one
    · positivity
    · linarith [hforward]
  have htime := parTimeDeriv_nashSmoothGaussianWeight
    (s := s) hK hR hApos hσ n z
  have htime' : parTimeDeriv (nashSmoothGaussianWeight K R A σ s n) z =
      W * (-q / (4 * A * τ ^ 2)) := by
    rw [htime]
    simp [W, q, ρ, τ, hstep]
  have hspace := parSpaceGrad_nashSmoothGaussianWeight_eq
    (s := s) hK hR hApos hσ n z
  have hweightEq : nashGaussianWeight A τ q = W := by
    simp [nashGaussianWeight, W, nashSmoothGaussianWeight,
      nashSmoothGaussianExponent, q, ρ, τ]
  have hdensity := hfull
  rw [hweightEq] at hdensity
  rw [htime', hspace]
  rw [PDE.DGNM.vecDot_smul_right]
  dsimp [W, ρ, τ, q, p] at hdensity ⊢
  let X : ℝ := nashSmoothGaussianWeight K R A σ s n z ^ 2 *
      (-truncatedDistanceMollify K R n z.1 ^ 2 /
        (4 * A * nashPositiveTimeShift σ (z.2 - s) ^ 2) * u ^ 2 -
        vecDot v (matVecMul M v) -
          2 * u * vecDot (matVecMul M v)
            (parSpaceGrad (nashSmoothGaussianExponent K R A σ s n) z))
  let L : ℝ := (1 - Lam / A) * truncatedDistanceMollify K R n z.1 ^ 2 *
      nashSmoothGaussianWeight K R A σ s n z ^ 2 * u ^ 2 /
      (4 * A * nashPositiveTimeShift σ (z.2 - s) ^ 2)
  have hscaled : 2 * X ≤ -2 * L := by
    calc
      2 * X = 2 * nashSmoothGaussianWeight K R A σ s n z ^ 2 *
          (-truncatedDistanceMollify K R n z.1 ^ 2 /
            (4 * A * nashPositiveTimeShift σ (z.2 - s) ^ 2) * u ^ 2 -
            vecDot v (matVecMul M v) -
              2 * u * vecDot (matVecMul M v)
                (parSpaceGrad (nashSmoothGaussianExponent K R A σ s n) z)) := by
        dsimp [X]
        ring
      _ ≤ -((1 - Lam / A) * truncatedDistanceMollify K R n z.1 ^ 2 *
          nashSmoothGaussianWeight K R A σ s n z ^ 2 * u ^ 2 /
          (2 * A * nashPositiveTimeShift σ (z.2 - s) ^ 2)) := hdensity
      _ = -2 * L := by dsimp [L]; ring
  have hresult : X ≤ -L := by linarith
  linear_combination hresult

/-- Almost everywhere on a Cauchy slab, the smooth Gaussian density is
nonpositive after retaining its quantitative loss term. -/
theorem nashSmoothGaussian_weightedDensity_ae {d : ℕ}
    {Lam A σ s t : ℝ} (_hsT : s < t) (hLam : 1 ≤ Lam) (hA : Lam < A)
    (hσ : 0 < σ) {a : ParCoeffField d}
    (ha : IsParabolicCoeff 1 Lam a univ (Icc s t))
    (K : Set (Vec d)) (hK : K.Nonempty) {R : ℝ} (hR : 0 ≤ R) (n : ℕ)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s t)) :
    ∀ᵐ z ∂(volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s t)),
      u.toFun z ^ 2 * nashSmoothGaussianWeight K R A σ s n z *
          parTimeDeriv (nashSmoothGaussianWeight K R A σ s n) z ≤
        nashSmoothGaussianWeight K R A σ s n z ^ 2 *
            PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
          2 * nashSmoothGaussianWeight K R A σ s n z * u.toFun z *
            vecDot (matVecMul (a z) (u.grad z))
              (parSpaceGrad (nashSmoothGaussianWeight K R A σ s n) z) -
          ((1 - Lam / A) * truncatedDistanceMollify K R n z.1 ^ 2 *
            nashSmoothGaussianWeight K R A σ s n z ^ 2 * u.toFun z ^ 2 /
            (4 * A * nashPositiveTimeShift σ (z.2 - s) ^ 2)) := by
  let Q : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s t
  have hQsub : Q ⊆ (univ : Set (Vec d)) ×ˢ Icc s t := by
    intro z hz
    exact ⟨hz.1, ⟨le_of_lt hz.2.1, hz.2.2⟩⟩
  have hQmeasure : volume.restrict Q ≤
      volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s t) :=
    Measure.restrict_mono hQsub le_rfl
  have hcoeff : ∀ᵐ z ∂(volume.restrict Q), IsEllipticMatrix 1 Lam (a z) :=
    ha.elliptic.filter_mono (ae_mono hQmeasure)
  have hQmem : ∀ᵐ z ∂(volume.restrict Q), z ∈ Q :=
    ae_restrict_mem (MeasurableSet.prod MeasurableSet.univ measurableSet_Ioc)
  filter_upwards [hcoeff, hQmem] with z hMz hz
  exact nashSmoothGaussian_weightedDensity_pointwise hK hR
    (by linarith) hA hσ n z (le_of_lt hz.2.1) hMz (u.toFun z) (u.grad z)

end PDE.Parabolic.Cauchy.Weights
