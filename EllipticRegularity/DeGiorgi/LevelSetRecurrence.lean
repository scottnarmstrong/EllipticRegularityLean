module

public import EllipticRegularity.DeGiorgi.LevelSetOneStep
public import EllipticRegularity.DeGiorgi.Scales

/-!
# De Giorgi level-set recurrence in dimensions at least three

This module packages the one-step level-set estimate along the explicit
nested radii and levels from `EllipticRegularity.DeGiorgi.Scales`.

## Main definitions

- `positivePartEnergyOnEuclideanBall`: the squared positive-part energy on a round ball.
- `deGiorgiLevelSetEnergy`: that energy along the nested De Giorgi radii and levels.
- `deGiorgiBallIterationBeta`, `deGiorgiBallIterationBase`, and
  `deGiorgiBallIterationCoefficient`: the exact scalar recurrence parameters.

## Main result

- `deGiorgiLevelSetEnergy_succ_le_geometric_of_h10Subharmonic`: the explicit
  recurrence `Y (n + 1) ≤ A * B ^ n * Y n ^ (1 + beta)`.

This is the standard nested-ball recurrence. Its eventual ellipticity
dependence is an auxiliary baseline and is not asserted to be the sharp
higher-dimensional De Giorgi dependence.
-/

@[expose] public section

namespace PDE

open MeasureTheory

/-- The squared positive-part energy of `u` above `k` on a round ball. -/
noncomputable def positivePartEnergyOnEuclideanBall
    {d : ℕ} (u : Vec d → ℝ) (x₀ : Vec d) (r k : ℝ) : ℝ :=
  ∫ x in euclideanBall x₀ r, max (u x - k) 0 ^ 2

/-- The positive-part energy along the nested De Giorgi radii and levels.

The level is shifted by `k₀`, so the sequence starts at level `k₀` and
approaches `k₀ + K`. -/
noncomputable def deGiorgiLevelSetEnergy
    {d : ℕ} (u : Vec d → ℝ) (x₀ : Vec d)
    (r R k₀ K : ℝ) (n : ℕ) : ℝ :=
  positivePartEnergyOnEuclideanBall u x₀
    (deGiorgiRadius r R n) (k₀ + deGiorgiLevel K n)

/-- The superlinear exponent increment in the standard ball iteration. -/
noncomputable def deGiorgiBallIterationBeta (d : ℕ) : ℝ :=
  2 / (d : ℝ)

/-- The geometric base generated jointly by the radius and level gaps. -/
noncomputable def deGiorgiBallIterationBase (d : ℕ) : ℝ :=
  (4 : ℝ) ^ (1 + deGiorgiBallIterationBeta d)

/-- The exact leading coefficient in the standard nested-ball recurrence. -/
noncomputable def deGiorgiBallIterationCoefficient
    (d : ℕ) (lam Lam r R K : ℝ) : ℝ :=
  (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
      ((8 * Lam / lam) + 2) * (32 / (R - r)) ^ 2 *
      K ^ (-(4 / (d : ℝ))) * deGiorgiBallIterationBase d

/-- The exponent increment `2 / d` is positive in dimensions at least three. -/
theorem deGiorgiBallIterationBeta_pos {d : ℕ} (hd : 3 ≤ d) :
    0 < deGiorgiBallIterationBeta d := by
  have hd_pos : (0 : ℝ) < d := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 3) hd
  dsimp only [deGiorgiBallIterationBeta]
  positivity

/-- The geometric base of the standard ball iteration is strictly larger than one. -/
theorem deGiorgiBallIterationBase_one_lt (d : ℕ) :
    1 < deGiorgiBallIterationBase d := by
  apply Real.one_lt_rpow (by norm_num)
  have hbeta_nonneg : 0 ≤ deGiorgiBallIterationBeta d := by
    dsimp only [deGiorgiBallIterationBeta]
    positivity
  linarith

/-- The leading iteration coefficient is positive under the analytic sign conditions. -/
theorem deGiorgiBallIterationCoefficient_pos
    (d : ℕ) {lam Lam r R K : ℝ}
    (hlam : 0 < lam) (hLam : 0 ≤ Lam) (hrR : r < R) (hK : 0 < K) :
    0 < deGiorgiBallIterationCoefficient d lam Lam r R K := by
  have hSobolev :
      0 < (zeroBoundarySobolevConstantTwo d : ℝ) := by
    exact_mod_cast zeroBoundarySobolevConstantTwo_pos d
  have hratio_nonneg : 0 ≤ 8 * Lam / lam :=
    div_nonneg (mul_nonneg (by norm_num) hLam) hlam.le
  have hratio : 0 < (8 * Lam / lam) + 2 := by
    linarith
  have hradius : 0 < (32 / (R - r)) ^ 2 :=
    sq_pos_of_pos <| div_pos (by norm_num) (sub_pos.mpr hrR)
  have hKpower : 0 < K ^ (-(4 / (d : ℝ))) :=
    Real.rpow_pos_of_pos hK _
  have hbase : 0 < deGiorgiBallIterationBase d :=
    lt_trans one_pos (deGiorgiBallIterationBase_one_lt d)
  dsimp only [deGiorgiBallIterationCoefficient]
  exact mul_pos
    (mul_pos
      (mul_pos (mul_pos (sq_pos_of_pos hSobolev) hratio) hradius)
      hKpower)
    hbase

/-- Positive-part energy is nonnegative. -/
theorem positivePartEnergyOnEuclideanBall_nonneg
    {d : ℕ} (u : Vec d → ℝ) (x₀ : Vec d) (r k : ℝ) :
    0 ≤ positivePartEnergyOnEuclideanBall u x₀ r k := by
  exact integral_nonneg fun x => sq_nonneg (max (u x - k) 0)

/-- Every energy in the nested De Giorgi sequence is nonnegative. -/
theorem deGiorgiLevelSetEnergy_nonneg
    {d : ℕ} (u : Vec d → ℝ) (x₀ : Vec d)
    (r R k₀ K : ℝ) (n : ℕ) :
    0 ≤ deGiorgiLevelSetEnergy u x₀ r R k₀ K n :=
  positivePartEnergyOnEuclideanBall_nonneg _ _ _ _

/-- The initial nested energy is the energy on the outer ball at level `k₀`. -/
@[simp]
theorem deGiorgiLevelSetEnergy_zero
    {d : ℕ} (u : Vec d → ℝ) (x₀ : Vec d) (r R k₀ K : ℝ) :
    deGiorgiLevelSetEnergy u x₀ r R k₀ K 0 =
      positivePartEnergyOnEuclideanBall u x₀ R k₀ := by
  simp only [deGiorgiLevelSetEnergy, deGiorgiRadius_zero,
    deGiorgiLevel_zero, add_zero]

private theorem dyadic_ball_recurrence_factor
    {d n : ℕ} {D K Y : ℝ}
    (hd : 3 ≤ d) (hD : 0 < D) (hK : 0 < K) (hY : 0 ≤ Y) :
    (32 : ℝ) ^ 2 /
          (D ^ 2 * (4 : ℝ) ^ (-((n : ℝ) + 1))) * Y *
          (Y / (K ^ 2 * (4 : ℝ) ^ (-((n : ℝ) + 1)))) ^
            deGiorgiBallIterationBeta d =
      (32 / D) ^ 2 * K ^ (-(4 / (d : ℝ))) *
          deGiorgiBallIterationBase d *
          deGiorgiBallIterationBase d ^ (n : ℝ) *
          Y ^ (1 + deGiorgiBallIterationBeta d) := by
  let beta : ℝ := deGiorgiBallIterationBeta d
  let t : ℝ := (n : ℝ) + 1
  have hd_pos : (0 : ℝ) < d := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 3) hd
  have hbeta_nonneg : 0 ≤ beta := by
    dsimp only [beta, deGiorgiBallIterationBeta]
    positivity
  have hfour_t_pos : 0 < (4 : ℝ) ^ t :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hradius :
      (32 : ℝ) ^ 2 / (D ^ 2 * (4 : ℝ) ^ (-t)) =
        (32 / D) ^ 2 * (4 : ℝ) ^ t := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
    field_simp [hD.ne', hfour_t_pos.ne']
  have hlevel :
      Y / (K ^ 2 * (4 : ℝ) ^ (-t)) =
        (Y / K ^ 2) * (4 : ℝ) ^ t := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
    field_simp [hK.ne', hfour_t_pos.ne']
  have hKpower :
      (K ^ 2) ^ beta = K ^ (4 / (d : ℝ)) := by
    rw [← Real.rpow_natCast K 2, ← Real.rpow_mul hK.le]
    congr 1
    dsimp only [beta, deGiorgiBallIterationBeta]
    ring
  have henergy :
      Y * (Y / K ^ 2) ^ beta =
        K ^ (-(4 / (d : ℝ))) * Y ^ (1 + beta) := by
    rw [Real.div_rpow hY (sq_nonneg K), hKpower, div_eq_mul_inv,
      ← Real.rpow_neg hK.le,
      Real.rpow_add_of_nonneg hY (by norm_num) hbeta_nonneg,
      Real.rpow_one]
    ring
  have hgeometric :
      (4 : ℝ) ^ t * ((4 : ℝ) ^ t) ^ beta =
        deGiorgiBallIterationBase d *
          deGiorgiBallIterationBase d ^ (n : ℝ) := by
    have hleft :
        (4 : ℝ) ^ t * ((4 : ℝ) ^ t) ^ beta =
          (4 : ℝ) ^ (t * (1 + beta)) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 4)]
      congr 1
      ring
    have hright :
        deGiorgiBallIterationBase d *
            deGiorgiBallIterationBase d ^ (n : ℝ) =
          (4 : ℝ) ^ (t * (1 + beta)) := by
      dsimp only [deGiorgiBallIterationBase, beta]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 4)]
      congr 1
      dsimp only [t]
      ring
    exact hleft.trans hright.symm
  change
    (32 : ℝ) ^ 2 / (D ^ 2 * (4 : ℝ) ^ (-t)) * Y *
          (Y / (K ^ 2 * (4 : ℝ) ^ (-t))) ^ beta =
      (32 / D) ^ 2 * K ^ (-(4 / (d : ℝ))) *
          deGiorgiBallIterationBase d *
          deGiorgiBallIterationBase d ^ (n : ℝ) *
          Y ^ (1 + beta)
  rw [hradius, hlevel, Real.mul_rpow
    (div_nonneg hY (sq_nonneg K)) hfour_t_pos.le]
  calc
    (32 / D) ^ 2 * (4 : ℝ) ^ t * Y *
        ((Y / K ^ 2) ^ beta * ((4 : ℝ) ^ t) ^ beta) =
      (32 / D) ^ 2 * (Y * (Y / K ^ 2) ^ beta) *
        ((4 : ℝ) ^ t * ((4 : ℝ) ^ t) ^ beta) := by ring
    _ = (32 / D) ^ 2 *
        (K ^ (-(4 / (d : ℝ))) * Y ^ (1 + beta)) *
        (deGiorgiBallIterationBase d *
          deGiorgiBallIterationBase d ^ (n : ℝ)) := by
      rw [henergy, hgeometric]
    _ = (32 / D) ^ 2 * K ^ (-(4 / (d : ℝ))) *
          deGiorgiBallIterationBase d *
          deGiorgiBallIterationBase d ^ (n : ℝ) *
          Y ^ (1 + beta) := by ring

/-- The exact standard nested-ball De Giorgi recurrence for a subsolution.

All dependence on the Sobolev constant, ellipticity, radii, level increment,
dimension, and iteration index is displayed in
`deGiorgiBallIterationCoefficient`, `deGiorgiBallIterationBase`, and
`deGiorgiBallIterationBeta`. -/
theorem deGiorgiLevelSetEnergy_succ_le_geometric_of_h10Subharmonic
    {d : ℕ} {lam Lam r R k₀ K : ℝ} {U : Set (Vec d)}
    {x₀ : Vec d} {a : CoeffField d} {u : H1Function U}
    (hd : 3 ≤ d) (hU : IsOpenBoundedConvexDomain U)
    (hr : 0 < r) (hrR : r < R)
    (hball : euclideanBall x₀ R ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsub : IsWeakDivergenceFormH10SubharmonicOn a U u)
    (hK : 0 < K) :
    ∀ n,
      deGiorgiLevelSetEnergy u x₀ r R k₀ K (n + 1) ≤
        deGiorgiBallIterationCoefficient d lam Lam r R K *
          deGiorgiBallIterationBase d ^ (n : ℝ) *
          deGiorgiLevelSetEnergy u x₀ r R k₀ K n ^
            (1 + deGiorgiBallIterationBeta d) := by
  intro n
  let rn : ℝ := deGiorgiRadius r R n
  let rn1 : ℝ := deGiorgiRadius r R (n + 1)
  let kn : ℝ := k₀ + deGiorgiLevel K n
  let kn1 : ℝ := k₀ + deGiorgiLevel K (n + 1)
  let Y : ℝ := deGiorgiLevelSetEnergy u x₀ r R k₀ K n
  have hrn1_pos : 0 < rn1 := by
    dsimp only [rn1]
    exact deGiorgiRadius_pos hr hrR (n + 1)
  have hrn1rn : rn1 < rn := by
    dsimp only [rn1, rn]
    exact deGiorgiRadius_strictAnti hrR (Nat.lt_succ_self n)
  have hballn : euclideanBall x₀ rn ⊆ U := by
    dsimp only [rn]
    exact (euclideanBall_deGiorgiRadius_subset hr hrR n).trans hball
  have hknkn1 : kn < kn1 := by
    dsimp only [kn, kn1]
    simpa only [add_comm, Nat.succ_eq_add_one] using
      add_lt_add_left
        (deGiorgiLevel_strictMono hK (Nat.lt_succ_self n)) k₀
  have hY_nonneg : 0 ≤ Y := by
    dsimp only [Y]
    exact deGiorgiLevelSetEnergy_nonneg _ _ _ _ _ _ _
  have hinner_outer :
      positivePartEnergyOnEuclideanBall u x₀ rn1 kn ≤
        positivePartEnergyOnEuclideanBall u x₀ rn kn := by
    let wk : Vec d → ℝ := fun x => max (u x - kn) 0
    have hwk : MemLp wk 2 (volume.restrict (euclideanBall x₀ rn)) := by
      simpa only [wk, H1Function.positivePartSubConst_toFun] using
        memLpOn_mono hballn (u.positivePartSubConst hU kn).memL2
    have hwkSq : IntegrableOn (fun x => wk x ^ 2) (euclideanBall x₀ rn) := by
      simpa only [pow_two] using integrableOn_mul_of_memL2On hwk hwk
    apply MeasureTheory.setIntegral_mono_set hwkSq
    · exact Filter.Eventually.of_forall fun x => sq_nonneg (wk x)
    · exact Filter.Eventually.of_forall fun x hx =>
        euclideanBall_deGiorgiRadius_succ_subset hr hrR n hx
  have hgap_pos : 0 < (kn1 - kn) ^ 2 :=
    sq_pos_of_pos (sub_pos.mpr hknkn1)
  have hquotient :
      positivePartEnergyOnEuclideanBall u x₀ rn1 kn /
          (kn1 - kn) ^ 2 ≤
        Y / (kn1 - kn) ^ 2 := by
    apply (div_le_div_iff_of_pos_right hgap_pos).2
    simpa only [Y, deGiorgiLevelSetEnergy, rn, kn] using hinner_outer
  have hbeta_nonneg : 0 ≤ deGiorgiBallIterationBeta d := by
    dsimp only [deGiorgiBallIterationBeta]
    positivity
  have hquotient_rpow :
      (positivePartEnergyOnEuclideanBall u x₀ rn1 kn /
          (kn1 - kn) ^ 2) ^ deGiorgiBallIterationBeta d ≤
        (Y / (kn1 - kn) ^ 2) ^ deGiorgiBallIterationBeta d :=
    Real.rpow_le_rpow
      (div_nonneg
        (positivePartEnergyOnEuclideanBall_nonneg _ _ _ _)
        (sq_nonneg _))
      hquotient hbeta_nonneg
  have hbase_nonneg :
      0 ≤ (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
          ((8 * Lam / lam) + 2) * (32 / (rn - rn1)) ^ 2 := by
    have hratio : 0 ≤ 8 * Lam / lam :=
      div_nonneg (mul_nonneg (by norm_num) hLam) hlam.le
    positivity
  have hstep :=
    setIntegral_positivePartSubConst_sq_ball_le_outer_energy_of_h10Subharmonic
      (u := u) (x₀ := x₀) (k := kn) (ell := kn1)
      hd hU hrn1_pos hrn1rn hballn hEll hlam hLam hsub hknkn1
  have hcoarse :
      deGiorgiLevelSetEnergy u x₀ r R k₀ K (n + 1) ≤
        (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
          ((8 * Lam / lam) + 2) * (32 / (rn - rn1)) ^ 2 * Y *
          (Y / (kn1 - kn) ^ 2) ^ deGiorgiBallIterationBeta d := by
    calc
      deGiorgiLevelSetEnergy u x₀ r R k₀ K (n + 1) ≤
          (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
            ((8 * Lam / lam) + 2) * (32 / (rn - rn1)) ^ 2 *
            positivePartEnergyOnEuclideanBall u x₀ rn kn *
            (positivePartEnergyOnEuclideanBall u x₀ rn1 kn /
              (kn1 - kn) ^ 2) ^ deGiorgiBallIterationBeta d := by
        simpa only [deGiorgiLevelSetEnergy,
          positivePartEnergyOnEuclideanBall, rn, rn1, kn, kn1,
          deGiorgiBallIterationBeta] using hstep
      _ ≤ (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
            ((8 * Lam / lam) + 2) * (32 / (rn - rn1)) ^ 2 *
            positivePartEnergyOnEuclideanBall u x₀ rn kn *
            (Y / (kn1 - kn) ^ 2) ^ deGiorgiBallIterationBeta d := by
        exact mul_le_mul_of_nonneg_left hquotient_rpow
          (mul_nonneg hbase_nonneg
            (positivePartEnergyOnEuclideanBall_nonneg _ _ _ _))
      _ = (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
            ((8 * Lam / lam) + 2) * (32 / (rn - rn1)) ^ 2 * Y *
            (Y / (kn1 - kn) ^ 2) ^ deGiorgiBallIterationBeta d := by
        rfl
  have hfactor := dyadic_ball_recurrence_factor
    hd (sub_pos.mpr hrR) hK hY_nonneg (n := n)
  calc
    deGiorgiLevelSetEnergy u x₀ r R k₀ K (n + 1) ≤
        (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
          ((8 * Lam / lam) + 2) * (32 / (rn - rn1)) ^ 2 * Y *
          (Y / (kn1 - kn) ^ 2) ^ deGiorgiBallIterationBeta d := hcoarse
    _ = (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
          ((8 * Lam / lam) + 2) *
          ((32 : ℝ) ^ 2 /
            ((R - r) ^ 2 * (4 : ℝ) ^ (-((n : ℝ) + 1))) * Y *
            (Y / (K ^ 2 * (4 : ℝ) ^ (-((n : ℝ) + 1)))) ^
              deGiorgiBallIterationBeta d) := by
        rw [div_pow, show rn - rn1 =
          deGiorgiRadius r R n - deGiorgiRadius r R (n + 1) by rfl,
          show kn1 - kn =
            deGiorgiLevel K (n + 1) - deGiorgiLevel K n by
              dsimp only [kn1, kn]
              ring,
          deGiorgiRadius_sub_succ_sq, deGiorgiLevel_succ_sub_sq]
        ring
    _ = (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
          ((8 * Lam / lam) + 2) *
          ((32 / (R - r)) ^ 2 * K ^ (-(4 / (d : ℝ))) *
            deGiorgiBallIterationBase d *
            deGiorgiBallIterationBase d ^ (n : ℝ) *
            Y ^ (1 + deGiorgiBallIterationBeta d)) := by
        rw [hfactor]
    _ = deGiorgiBallIterationCoefficient d lam Lam r R K *
          deGiorgiBallIterationBase d ^ (n : ℝ) *
          deGiorgiLevelSetEnergy u x₀ r R k₀ K n ^
            (1 + deGiorgiBallIterationBeta d) := by
      dsimp only [deGiorgiBallIterationCoefficient, Y]
      ring

/-- Homogeneous-solution wrapper for the exact standard nested-ball recurrence. -/
theorem deGiorgiLevelSetEnergy_succ_le_geometric_of_harmonic
    {d : ℕ} {lam Lam r R k₀ K : ℝ} {U : Set (Vec d)}
    {x₀ : Vec d} {a : CoeffField d} {u : H1Function U}
    (hd : 3 ≤ d) (hU : IsOpenBoundedConvexDomain U)
    (hr : 0 < r) (hrR : r < R)
    (hball : euclideanBall x₀ R ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u)
    (hK : 0 < K) :
    ∀ n,
      deGiorgiLevelSetEnergy u x₀ r R k₀ K (n + 1) ≤
        deGiorgiBallIterationCoefficient d lam Lam r R K *
          deGiorgiBallIterationBase d ^ (n : ℝ) *
          deGiorgiLevelSetEnergy u x₀ r R k₀ K n ^
            (1 + deGiorgiBallIterationBeta d) :=
  deGiorgiLevelSetEnergy_succ_le_geometric_of_h10Subharmonic
    hd hU hr hrR hball hEll hlam hLam (hsol.toH10SubharmonicOn hEll) hK

end PDE
