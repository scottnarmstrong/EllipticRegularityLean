module

public import EllipticRegularity.Energy.CaccioppoliIntegrated
public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.Sobolev.Cutoff.Ball
public import PDEFoundation.Sobolev.Mean

/-!
# Concentric-ball Caccioppoli estimate

This module specializes the geometry-free subsolution cutoff estimate to
concentric round balls. The quantitative ball cutoff keeps every numerical
constant literal. Standard smooth-test subsolutions and homogeneous weak
solutions are exported as corollaries.
-/

@[expose] public section

namespace PDE

open MeasureTheory

/-- The concentric-ball positive-part Caccioppoli estimate, retaining the
cutoff constant in factorized form. -/
theorem
    caccioppoli_ball_positivePart_gradient_factorized_of_h10Subharmonic
    {d : ℕ} {lam Lam k r R : ℝ} {U : Set (Vec d)}
    {x₀ : Vec d} {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hr : 0 < r) (hrR : r < R)
    (hball : euclideanBall x₀ R ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsub : IsWeakDivergenceFormH10SubharmonicOn a U u) :
    ∫ x in euclideanBall x₀ r,
        vecNormSq ({y | k < u y}.indicator u.grad x) ≤
      (4 * Lam / lam) * (32 / (R - r)) ^ 2 *
        ∫ x in euclideanBall x₀ R, max (u x - k) 0 ^ 2 := by
  exact caccioppoli_positivePart_on_inner_of_h10Subharmonic
    (k := k) hU
    (measurableSet_euclideanBall x₀ r)
    (measurableSet_euclideanBall x₀ R)
    hEll hlam hLam hsub
    (quantitativeBallCutoff x₀ hr.le hrR) hball

/-- Smooth-test subharmonic wrapper for the factorized concentric-ball
estimate. The positivity-preserving density theorem justifies the passage to
the all-`H¹₀` test used by the energy proof. -/
theorem
    caccioppoli_ball_positivePart_gradient_factorized_of_subharmonic
    {d : ℕ} {lam Lam k r R : ℝ} {U : Set (Vec d)}
    {x₀ : Vec d} {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hr : 0 < r) (hrR : r < R)
    (hball : euclideanBall x₀ R ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsub : IsWeakDivergenceFormSubharmonicOn a U u) :
    ∫ x in euclideanBall x₀ r,
        vecNormSq ({y | k < u y}.indicator u.grad x) ≤
      (4 * Lam / lam) * (32 / (R - r)) ^ 2 *
        ∫ x in euclideanBall x₀ R, max (u x - k) 0 ^ 2 :=
  caccioppoli_ball_positivePart_gradient_factorized_of_h10Subharmonic
    (k := k) hU hr hrR hball hEll hlam hLam
      (hsub.toH10SubharmonicOn hU hEll)

/-- Homogeneous-solution wrapper for the factorized concentric-ball
estimate. -/
theorem caccioppoli_ball_positivePart_gradient_factorized
    {d : ℕ} {lam Lam k r R : ℝ} {U : Set (Vec d)}
    {x₀ : Vec d} {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hr : 0 < r) (hrR : r < R)
    (hball : euclideanBall x₀ R ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u) :
    ∫ x in euclideanBall x₀ r,
        vecNormSq ({y | k < u y}.indicator u.grad x) ≤
      (4 * Lam / lam) * (32 / (R - r)) ^ 2 *
        ∫ x in euclideanBall x₀ R, max (u x - k) 0 ^ 2 :=
  caccioppoli_ball_positivePart_gradient_factorized_of_h10Subharmonic
    (k := k) hU hr hrR hball hEll hlam hLam
      (hsol.toH10SubharmonicOn hEll)

/-- The raw concentric-ball positive-part Caccioppoli estimate with its
fully expanded numerical constant. -/
theorem caccioppoli_ball_positivePart_gradient_of_h10Subharmonic
    {d : ℕ} {lam Lam k r R : ℝ} {U : Set (Vec d)}
    {x₀ : Vec d} {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hr : 0 < r) (hrR : r < R)
    (hball : euclideanBall x₀ R ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsub : IsWeakDivergenceFormH10SubharmonicOn a U u) :
    ∫ x in euclideanBall x₀ r,
        vecNormSq ({y | k < u y}.indicator u.grad x) ≤
      (4096 * (Lam / lam) / (R - r) ^ 2) *
        ∫ x in euclideanBall x₀ R, max (u x - k) 0 ^ 2 := by
  have hfactor :=
    caccioppoli_ball_positivePart_gradient_factorized_of_h10Subharmonic
      (k := k) hU hr hrR hball hEll hlam hLam hsub
  convert hfactor using 1
  field_simp [(sub_pos.mpr hrR).ne']
  ring

/-- Smooth-test subharmonic wrapper for the fully expanded concentric-ball
estimate. -/
theorem caccioppoli_ball_positivePart_gradient_of_subharmonic
    {d : ℕ} {lam Lam k r R : ℝ} {U : Set (Vec d)}
    {x₀ : Vec d} {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hr : 0 < r) (hrR : r < R)
    (hball : euclideanBall x₀ R ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsub : IsWeakDivergenceFormSubharmonicOn a U u) :
    ∫ x in euclideanBall x₀ r,
        vecNormSq ({y | k < u y}.indicator u.grad x) ≤
      (4096 * (Lam / lam) / (R - r) ^ 2) *
        ∫ x in euclideanBall x₀ R, max (u x - k) 0 ^ 2 :=
  caccioppoli_ball_positivePart_gradient_of_h10Subharmonic
    (k := k) hU hr hrR hball hEll hlam hLam
      (hsub.toH10SubharmonicOn hU hEll)

/-- Homogeneous-solution wrapper for the raw concentric-ball estimate. -/
theorem caccioppoli_ball_positivePart_gradient
    {d : ℕ} {lam Lam k r R : ℝ} {U : Set (Vec d)}
    {x₀ : Vec d} {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hr : 0 < r) (hrR : r < R)
    (hball : euclideanBall x₀ R ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u) :
    ∫ x in euclideanBall x₀ r,
        vecNormSq ({y | k < u y}.indicator u.grad x) ≤
      (4096 * (Lam / lam) / (R - r) ^ 2) *
        ∫ x in euclideanBall x₀ R, max (u x - k) 0 ^ 2 :=
  caccioppoli_ball_positivePart_gradient_of_h10Subharmonic
    (k := k) hU hr hrR hball hEll hlam hLam
      (hsol.toH10SubharmonicOn hEll)

/-- The normalized squared concentric-ball estimate. The volume-ratio factor
`(R / r) ^ d` is explicit and is not absorbed into an unspecified constant. -/
theorem
    caccioppoli_ball_positivePart_gradient_integralAverage_of_h10Subharmonic
    {d : ℕ} {lam Lam k r R : ℝ} {U : Set (Vec d)}
    {x₀ : Vec d} {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hr : 0 < r) (hrR : r < R)
    (hball : euclideanBall x₀ R ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsub : IsWeakDivergenceFormH10SubharmonicOn a U u) :
    integralAverage (euclideanBall x₀ r)
        (fun x =>
          vecNormSq ({y | k < u y}.indicator u.grad x)) ≤
      (4096 * (Lam / lam) * (R / r) ^ d / (R - r) ^ 2) *
        integralAverage (euclideanBall x₀ R)
          (fun x => max (u x - k) 0 ^ 2) := by
  have hR : 0 < R := hr.trans hrR
  have hraw :=
    caccioppoli_ball_positivePart_gradient_of_h10Subharmonic
      (k := k) hU hr hrR hball hEll hlam hLam hsub
  have hvolr :
      0 < (volume (euclideanBall x₀ r)).toReal :=
    volume_euclideanBall_toReal_pos x₀ hr
  have hvolR :
      0 < (volume (euclideanBall x₀ R)).toReal :=
    volume_euclideanBall_toReal_pos x₀ hR
  have hscaled := mul_le_mul_of_nonneg_left hraw
    (inv_nonneg.mpr hvolr.le)
  have hratio :
      (volume (euclideanBall x₀ R)).toReal /
          (volume (euclideanBall x₀ r)).toReal =
        (R / r) ^ d :=
    volume_euclideanBall_toReal_div_eq_div_pow x₀ x₀ hr hR
  unfold integralAverage
  calc
    (volume (euclideanBall x₀ r)).toReal⁻¹ *
        (∫ x in euclideanBall x₀ r,
          vecNormSq ({y | k < u y}.indicator u.grad x)) ≤
      (volume (euclideanBall x₀ r)).toReal⁻¹ *
        ((4096 * (Lam / lam) / (R - r) ^ 2) *
          ∫ x in euclideanBall x₀ R, max (u x - k) 0 ^ 2) :=
      hscaled
    _ = (4096 * (Lam / lam) *
          ((volume (euclideanBall x₀ R)).toReal /
            (volume (euclideanBall x₀ r)).toReal) /
          (R - r) ^ 2) *
        ((volume (euclideanBall x₀ R)).toReal⁻¹ *
          ∫ x in euclideanBall x₀ R, max (u x - k) 0 ^ 2) := by
      field_simp [hvolr.ne', hvolR.ne', (sub_pos.mpr hrR).ne']
    _ = (4096 * (Lam / lam) * (R / r) ^ d / (R - r) ^ 2) *
        ((volume (euclideanBall x₀ R)).toReal⁻¹ *
          ∫ x in euclideanBall x₀ R, max (u x - k) 0 ^ 2) := by
      rw [hratio]

/-- Smooth-test subharmonic wrapper for the normalized squared concentric-ball
estimate. -/
theorem
    caccioppoli_ball_positivePart_gradient_integralAverage_of_subharmonic
    {d : ℕ} {lam Lam k r R : ℝ} {U : Set (Vec d)}
    {x₀ : Vec d} {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hr : 0 < r) (hrR : r < R)
    (hball : euclideanBall x₀ R ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsub : IsWeakDivergenceFormSubharmonicOn a U u) :
    integralAverage (euclideanBall x₀ r)
        (fun x =>
          vecNormSq ({y | k < u y}.indicator u.grad x)) ≤
      (4096 * (Lam / lam) * (R / r) ^ d / (R - r) ^ 2) *
        integralAverage (euclideanBall x₀ R)
          (fun x => max (u x - k) 0 ^ 2) :=
  caccioppoli_ball_positivePart_gradient_integralAverage_of_h10Subharmonic
    (k := k) hU hr hrR hball hEll hlam hLam
      (hsub.toH10SubharmonicOn hU hEll)

/-- Homogeneous-solution wrapper for the normalized squared ball estimate. -/
theorem caccioppoli_ball_positivePart_gradient_integralAverage
    {d : ℕ} {lam Lam k r R : ℝ} {U : Set (Vec d)}
    {x₀ : Vec d} {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hr : 0 < r) (hrR : r < R)
    (hball : euclideanBall x₀ R ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u) :
    integralAverage (euclideanBall x₀ r)
        (fun x =>
          vecNormSq ({y | k < u y}.indicator u.grad x)) ≤
      (4096 * (Lam / lam) * (R / r) ^ d / (R - r) ^ 2) *
        integralAverage (euclideanBall x₀ R)
          (fun x => max (u x - k) 0 ^ 2) :=
  caccioppoli_ball_positivePart_gradient_integralAverage_of_h10Subharmonic
    (k := k) hU hr hrR hball hEll hlam hLam
      (hsol.toH10SubharmonicOn hEll)

/-- The normalized `L²` concentric-ball positive-part Caccioppoli estimate.
The dependence on the ellipticity ratio and the volume ratio is displayed
after taking square roots:
`(Lam / lam) ^ (1 / 2)` and `(R / r) ^ (d / 2)`, respectively. -/
theorem
    caccioppoli_ball_positivePart_gradient_integralAverage_sqrt_of_h10Subharmonic
    {d : ℕ} {lam Lam k r R : ℝ} {U : Set (Vec d)}
    {x₀ : Vec d} {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hr : 0 < r) (hrR : r < R)
    (hball : euclideanBall x₀ R ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsub : IsWeakDivergenceFormH10SubharmonicOn a U u) :
    Real.sqrt
        (integralAverage (euclideanBall x₀ r)
          (fun x =>
            vecNormSq ({y | k < u y}.indicator u.grad x))) ≤
      64 * Real.sqrt (Lam / lam) *
        (R / r) ^ ((d : ℝ) / 2) / (R - r) *
          Real.sqrt
            (integralAverage (euclideanBall x₀ R)
              (fun x => max (u x - k) 0 ^ 2)) := by
  let A : ℝ :=
    integralAverage (euclideanBall x₀ r)
      (fun x =>
        vecNormSq ({y | k < u y}.indicator u.grad x))
  let B : ℝ :=
    integralAverage (euclideanBall x₀ R)
      (fun x => max (u x - k) 0 ^ 2)
  let q : ℝ := R / r
  let κ : ℝ := Lam / lam
  let δ : ℝ := R - r
  have hA : 0 ≤ A := by
    apply integralAverage_nonneg
      (measurableSet_euclideanBall x₀ r)
    intro x hx
    exact vecNormSq_nonneg _
  have hB : 0 ≤ B := by
    apply integralAverage_nonneg
      (measurableSet_euclideanBall x₀ R)
    intro x hx
    exact sq_nonneg _
  have hq : 0 < q := by
    exact div_pos (hr.trans hrR) hr
  have hκ : 0 ≤ κ := by
    exact div_nonneg hLam hlam.le
  have hδ : 0 < δ := by
    exact sub_pos.mpr hrR
  have hsq :
      A ≤ (4096 * κ * q ^ d / δ ^ 2) * B := by
    simpa [A, B, q, κ, δ] using
      caccioppoli_ball_positivePart_gradient_integralAverage_of_h10Subharmonic
        (k := k) hU hr hrR hball hEll hlam hLam hsub
  have hqHalfSq :
      (q ^ ((d : ℝ) / 2)) ^ 2 = q ^ d := by
    calc
      (q ^ ((d : ℝ) / 2)) ^ 2 =
          q ^ (((d : ℝ) / 2) * (2 : ℕ)) :=
        (Real.rpow_mul_natCast hq.le ((d : ℝ) / 2) 2).symm
      _ = q ^ (d : ℝ) := by
        congr 1
        norm_num
      _ = q ^ d := Real.rpow_natCast q d
  have hfactorSq :
      (64 * Real.sqrt κ * q ^ ((d : ℝ) / 2) / δ) ^ 2 =
        4096 * κ * q ^ d / δ ^ 2 := by
    calc
      (64 * Real.sqrt κ * q ^ ((d : ℝ) / 2) / δ) ^ 2 =
          4096 * (Real.sqrt κ) ^ 2 *
            (q ^ ((d : ℝ) / 2)) ^ 2 / δ ^ 2 := by
        ring_nf
      _ = 4096 * κ * q ^ d / δ ^ 2 := by
        rw [Real.sq_sqrt hκ, hqHalfSq]
  have hrightSq :
      ((64 * Real.sqrt κ * q ^ ((d : ℝ) / 2) / δ) *
          Real.sqrt B) ^ 2 =
        (4096 * κ * q ^ d / δ ^ 2) * B := by
    rw [mul_pow, hfactorSq, Real.sq_sqrt hB]
  have hsquares :
      (Real.sqrt A) ^ 2 ≤
        ((64 * Real.sqrt κ * q ^ ((d : ℝ) / 2) / δ) *
          Real.sqrt B) ^ 2 := by
    rw [Real.sq_sqrt hA, hrightSq]
    exact hsq
  have hrightNonneg :
      0 ≤ (64 * Real.sqrt κ * q ^ ((d : ℝ) / 2) / δ) *
          Real.sqrt B := by
    positivity
  change Real.sqrt A ≤
    (64 * Real.sqrt κ * q ^ ((d : ℝ) / 2) / δ) *
      Real.sqrt B
  exact (sq_le_sq₀ (Real.sqrt_nonneg A) hrightNonneg).mp hsquares

/-- Smooth-test subharmonic wrapper for the normalized square-root
concentric-ball estimate. The displayed dependence remains sharp in the
ellipticity ratio. -/
theorem
    caccioppoli_ball_positivePart_gradient_integralAverage_sqrt_of_subharmonic
    {d : ℕ} {lam Lam k r R : ℝ} {U : Set (Vec d)}
    {x₀ : Vec d} {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hr : 0 < r) (hrR : r < R)
    (hball : euclideanBall x₀ R ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsub : IsWeakDivergenceFormSubharmonicOn a U u) :
    Real.sqrt
        (integralAverage (euclideanBall x₀ r)
          (fun x =>
            vecNormSq ({y | k < u y}.indicator u.grad x))) ≤
      64 * Real.sqrt (Lam / lam) *
        (R / r) ^ ((d : ℝ) / 2) / (R - r) *
          Real.sqrt
            (integralAverage (euclideanBall x₀ R)
              (fun x => max (u x - k) 0 ^ 2)) :=
  caccioppoli_ball_positivePart_gradient_integralAverage_sqrt_of_h10Subharmonic
    (k := k) hU hr hrR hball hEll hlam hLam
      (hsub.toH10SubharmonicOn hU hEll)

/-- Homogeneous-solution wrapper for the normalized square-root ball
estimate. -/
theorem caccioppoli_ball_positivePart_gradient_integralAverage_sqrt
    {d : ℕ} {lam Lam k r R : ℝ} {U : Set (Vec d)}
    {x₀ : Vec d} {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hr : 0 < r) (hrR : r < R)
    (hball : euclideanBall x₀ R ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u) :
    Real.sqrt
        (integralAverage (euclideanBall x₀ r)
          (fun x =>
            vecNormSq ({y | k < u y}.indicator u.grad x))) ≤
      64 * Real.sqrt (Lam / lam) *
        (R / r) ^ ((d : ℝ) / 2) / (R - r) *
          Real.sqrt
            (integralAverage (euclideanBall x₀ R)
              (fun x => max (u x - k) 0 ^ 2)) :=
  caccioppoli_ball_positivePart_gradient_integralAverage_sqrt_of_h10Subharmonic
    (k := k) hU hr hrR hball hEll hlam hLam
      (hsol.toH10SubharmonicOn hEll)

end PDE
