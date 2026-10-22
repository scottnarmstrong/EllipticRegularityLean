module

public import PDEFoundation.Sobolev.Inequalities.Poincare

/-!
# Quantitative mean-zero Sobolev–Poincaré theorem contract

The subcritical exponent and every geometric factor are part of the public
statement. The analytic theorem is posed once on bounded open convex domains;
round-ball and axis-cube surfaces are derived from it.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

/-- The subcritical Sobolev conjugate `d * p / (d - p)`. -/
noncomputable def sobolevConjugate (d : ℕ) (p : ℝ) : ℝ :=
  (d : ℝ) * p / ((d : ℝ) - p)

theorem sobolevConjugate_pos {d : ℕ} {p : ℝ}
    (hp : 0 < p) (hpd : p < d) :
    0 < sobolevConjugate d p := by
  exact div_pos (mul_pos (by exact_mod_cast hp.trans hpd) hp)
    (sub_pos.mpr hpd)

theorem inv_sobolevConjugate {d : ℕ} {p : ℝ}
    (hp : 0 < p) (hpd : p < d) :
    (sobolevConjugate d p)⁻¹ =
      p⁻¹ - (d : ℝ)⁻¹ := by
  have hd : (0 : ℝ) < d := by
    exact_mod_cast hp.trans hpd
  have hpNe : p ≠ 0 := hp.ne'
  have hdNe : (d : ℝ) ≠ 0 := hd.ne'
  unfold sobolevConjugate
  field_simp [hpNe, hdNe]

/-- The reciprocal Sobolev-exponent identity in the exact real form used by
the `ENNReal.rpow` volume factors. -/
theorem toReal_one_div_ofReal_sobolevConjugate
    {d : ℕ} {p : ℝ} (hp : 0 < p) (hpd : p < d) :
    (1 / ENNReal.ofReal (sobolevConjugate d p)).toReal =
      -(d : ℝ)⁻¹ +
        (1 / ENNReal.ofReal p).toReal := by
  have hq : 0 < sobolevConjugate d p :=
    sobolevConjugate_pos hp hpd
  calc
    (1 / ENNReal.ofReal (sobolevConjugate d p)).toReal =
        (sobolevConjugate d p)⁻¹ := by
      rw [one_div, ENNReal.toReal_inv,
        ENNReal.toReal_ofReal hq.le]
    _ = p⁻¹ - (d : ℝ)⁻¹ :=
      inv_sobolevConjugate hp hpd
    _ = -(d : ℝ)⁻¹ +
        (1 / ENNReal.ofReal p).toReal := by
      rw [one_div, ENNReal.toReal_inv,
        ENNReal.toReal_ofReal hp.le]
      ring

/-- `C` is a normalized mean-zero Sobolev–Poincaré constant at exponent `p`
in dimension `d`.

The definition records the subcritical range, the exact exponent `p*`, the
Euclidean diameter, positive finite volume, and Euclidean gradient magnitude.
-/
def IsMeanZeroSobolevPoincareConstant
    (d : ℕ) (p C : ℝ) : Prop :=
  1 ≤ p ∧ p < d ∧ 0 ≤ C ∧
    ∀ (U : Set (Vec d)) (D : ℝ),
      IsOpenBoundedConvexDomain U →
      HasEuclideanDiameterLE U D →
      0 ≤ D →
      0 < volume U →
      volume U < ∞ →
      ∀ u : W1pFunction U (ENNReal.ofReal p),
        MeanZeroOn U u.toFun →
        eLpMeanNormOn U
            (ENNReal.ofReal (sobolevConjugate d p)) u.toFun ≤
          ENNReal.ofReal (C * D) *
            euclideanFieldELpMeanNormOn U
              (ENNReal.ofReal p) u.grad

namespace IsMeanZeroSobolevPoincareConstant

/-- The normalized statement on a bounded open convex domain. This named
projection is the common theorem used by the shape-specific interfaces. -/
theorem on_domain {d : ℕ} {p C : ℝ}
    (hC : IsMeanZeroSobolevPoincareConstant d p C)
    {U : Set (Vec d)} {D : ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hUDiameter : HasEuclideanDiameterLE U D)
    (hD : 0 ≤ D) (hUPos : 0 < volume U)
    (hUTop : volume U < ∞)
    (u : W1pFunction U (ENNReal.ofReal p))
    (huMean : MeanZeroOn U u.toFun) :
    eLpMeanNormOn U
        (ENNReal.ofReal (sobolevConjugate d p)) u.toFun ≤
      ENNReal.ofReal (C * D) *
        euclideanFieldELpMeanNormOn U
          (ENNReal.ofReal p) u.grad :=
  hC.2.2.2 U D hU hUDiameter hD hUPos hUTop u huMean

/-- The unnormalized bounded-convex-domain statement. The conversion from
normalized norms exposes the scale-free volume factor `|U|⁻¹ᐟᵈ`; it is not
absorbed into the constant. -/
theorem on_domain_unnormalized {d : ℕ} {p C : ℝ}
    (hC : IsMeanZeroSobolevPoincareConstant d p C)
    {U : Set (Vec d)} {D : ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hUDiameter : HasEuclideanDiameterLE U D)
    (hD : 0 ≤ D) (hUPos : 0 < volume U)
    (hUTop : volume U < ∞)
    (u : W1pFunction U (ENNReal.ofReal p))
    (huMean : MeanZeroOn U u.toFun) :
    eLpNormOn U
        (ENNReal.ofReal (sobolevConjugate d p)) u.toFun ≤
      ENNReal.ofReal (C * D) *
        volume U ^ (-(d : ℝ)⁻¹) *
          euclideanFieldELpNormOn U
            (ENNReal.ofReal p) u.grad := by
  have hp : 0 < p := zero_lt_one.trans_le hC.1
  have hNormalized :=
    hC.on_domain hU hUDiameter hD hUPos hUTop u huMean
  rw [eLpNormOn_eq_volume_rpow_mul_eLpMeanNormOn
      hUPos hUTop,
    euclideanFieldELpNormOn_eq_volume_rpow_mul
      hUPos hUTop]
  calc
    volume U ^
          (1 / ENNReal.ofReal (sobolevConjugate d p)).toReal *
          eLpMeanNormOn U
            (ENNReal.ofReal (sobolevConjugate d p)) u.toFun ≤
        volume U ^
          (1 / ENNReal.ofReal (sobolevConjugate d p)).toReal *
          (ENNReal.ofReal (C * D) *
            euclideanFieldELpMeanNormOn U
              (ENNReal.ofReal p) u.grad) :=
      mul_le_mul_right hNormalized _
    _ = ENNReal.ofReal (C * D) *
        volume U ^ (-(d : ℝ)⁻¹) *
          (volume U ^ (1 / ENNReal.ofReal p).toReal *
            euclideanFieldELpMeanNormOn U
              (ENNReal.ofReal p) u.grad) := by
      rw [toReal_one_div_ofReal_sobolevConjugate hp hC.2.1,
        ENNReal.rpow_add _ _ hUPos.ne' hUTop.ne]
      ac_rfl

/-- The normalized round-ball statement, with diameter `2 * R`. -/
theorem on_euclideanBall {d : ℕ} {p C : ℝ}
    (hC : IsMeanZeroSobolevPoincareConstant d p C)
    (x₀ : Vec d) {R : ℝ} (hR : 0 < R)
    (u : W1pFunction (euclideanBall x₀ R) (ENNReal.ofReal p))
    (huMean : MeanZeroOn (euclideanBall x₀ R) u.toFun) :
    eLpMeanNormOn (euclideanBall x₀ R)
        (ENNReal.ofReal (sobolevConjugate d p)) u.toFun ≤
      ENNReal.ofReal (C * (2 * R)) *
        euclideanFieldELpMeanNormOn (euclideanBall x₀ R)
          (ENNReal.ofReal p) u.grad := by
  exact
    hC.on_domain
      (isOpenBoundedConvexDomain_euclideanBall x₀ hR)
      (hasEuclideanDiameterLE_euclideanBall x₀ hR)
      (mul_nonneg (by norm_num) hR.le)
      (volume_euclideanBall_pos x₀ hR)
      (lt_top_iff_ne_top.mpr
        (volume_euclideanBall_ne_top x₀ hR.le))
      u huMean

/-- The unnormalized round-ball statement, including the explicit
`|B_R|⁻¹ᐟᵈ` factor. -/
theorem on_euclideanBall_unnormalized {d : ℕ} {p C : ℝ}
    (hC : IsMeanZeroSobolevPoincareConstant d p C)
    (x₀ : Vec d) {R : ℝ} (hR : 0 < R)
    (u : W1pFunction (euclideanBall x₀ R) (ENNReal.ofReal p))
    (huMean : MeanZeroOn (euclideanBall x₀ R) u.toFun) :
    eLpNormOn (euclideanBall x₀ R)
        (ENNReal.ofReal (sobolevConjugate d p)) u.toFun ≤
      ENNReal.ofReal (C * (2 * R)) *
        volume (euclideanBall x₀ R) ^ (-(d : ℝ)⁻¹) *
          euclideanFieldELpNormOn (euclideanBall x₀ R)
            (ENNReal.ofReal p) u.grad := by
  exact
    hC.on_domain_unnormalized
      (isOpenBoundedConvexDomain_euclideanBall x₀ hR)
      (hasEuclideanDiameterLE_euclideanBall x₀ hR)
      (mul_nonneg (by norm_num) hR.le)
      (volume_euclideanBall_pos x₀ hR)
      (lt_top_iff_ne_top.mpr
        (volume_euclideanBall_ne_top x₀ hR.le))
      u huMean

/-- The normalized axis-cube statement, with diameter `sqrt d * L`. -/
theorem on_axisCube {d : ℕ} {p C : ℝ}
    (hC : IsMeanZeroSobolevPoincareConstant d p C)
    (z : Vec d) {L : ℝ} (hL : 0 < L)
    (u : W1pFunction (axisCube z L) (ENNReal.ofReal p))
    (huMean : MeanZeroOn (axisCube z L) u.toFun) :
    eLpMeanNormOn (axisCube z L)
        (ENNReal.ofReal (sobolevConjugate d p)) u.toFun ≤
      ENNReal.ofReal (C * (Real.sqrt d * L)) *
        euclideanFieldELpMeanNormOn (axisCube z L)
          (ENNReal.ofReal p) u.grad := by
  exact
    hC.on_domain
      (isOpenBoundedConvexDomain_axisCube z L)
      (hasEuclideanDiameterLE_axisCube z hL.le)
      (mul_nonneg (Real.sqrt_nonneg d) hL.le)
      (volume_axisCube_pos z hL)
      (lt_top_iff_ne_top.mpr (volume_axisCube_ne_top z L))
      u huMean

/-- The unnormalized axis-cube statement, including the explicit
`|Q|⁻¹ᐟᵈ` factor. -/
theorem on_axisCube_unnormalized {d : ℕ} {p C : ℝ}
    (hC : IsMeanZeroSobolevPoincareConstant d p C)
    (z : Vec d) {L : ℝ} (hL : 0 < L)
    (u : W1pFunction (axisCube z L) (ENNReal.ofReal p))
    (huMean : MeanZeroOn (axisCube z L) u.toFun) :
    eLpNormOn (axisCube z L)
        (ENNReal.ofReal (sobolevConjugate d p)) u.toFun ≤
      ENNReal.ofReal (C * (Real.sqrt d * L)) *
        volume (axisCube z L) ^ (-(d : ℝ)⁻¹) *
          euclideanFieldELpNormOn (axisCube z L)
            (ENNReal.ofReal p) u.grad := by
  exact
    hC.on_domain_unnormalized
      (isOpenBoundedConvexDomain_axisCube z L)
      (hasEuclideanDiameterLE_axisCube z hL.le)
      (mul_nonneg (Real.sqrt_nonneg d) hL.le)
      (volume_axisCube_pos z hL)
      (lt_top_iff_ne_top.mpr (volume_axisCube_ne_top z L))
      u huMean

end IsMeanZeroSobolevPoincareConstant

end PDE
