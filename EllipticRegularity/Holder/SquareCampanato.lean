module

public import EllipticRegularity.Energy.SquareHoleFillingDecay
public import PDEFoundation.Regularity.DyadicCampanato

/-!
# Two-dimensional square energy decay to Campanato decay

This module converts the compiled square hole-filling energy decay into the
normalized `L²` oscillation hypothesis used by the dyadic Campanato theorem.
The Hölder exponent is half of the energy-decay exponent, and every scale and
energy factor remains explicit.

The output here is the honest Campanato bound. Composing it with a
Campanato-to-Hölder theorem incurs that theorem's explicit
`(1 - 2 ^ (-α))⁻¹` factor; no sharper final PDE estimate is claimed in this
module.
-/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

/-- The Hölder exponent supplied by the current two-dimensional square
hole-filling argument: one half of its energy-decay exponent. -/
def squareHoleFillingHolderExponent (lam Lam : ℝ) : ℝ :=
  holeFillingDyadicExponent
    (687865857 * Real.sqrt (Lam / lam)) / 2

/-- The square hole-filling Hölder exponent is positive. -/
theorem squareHoleFillingHolderExponent_pos
    (lam Lam : ℝ) :
    0 < squareHoleFillingHolderExponent lam Lam := by
  unfold squareHoleFillingHolderExponent
  exact div_pos
    (holeFillingDyadicExponent_pos
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
    (by norm_num)

/-- The square hole-filling Hölder exponent is at most `1 / 2`. -/
theorem squareHoleFillingHolderExponent_le_half
    (lam Lam : ℝ) :
    squareHoleFillingHolderExponent lam Lam ≤ 1 / 2 := by
  unfold squareHoleFillingHolderExponent
  exact div_le_div_of_nonneg_right
    (holeFillingDyadicExponent_le_one
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
    (by norm_num)

private theorem dyadicEnergyScale_sq
    {R β E : ℝ} (hR : 0 < R) (hE : 0 ≤ E)
    (n : ℕ) :
    32 * (2 : ℝ) ^ (-β * (n : ℝ)) * E =
      (4 * Real.sqrt 2 * Real.sqrt E /
          R ^ (β / 2) *
        (R / (2 : ℝ) ^ n) ^ (β / 2)) ^ 2 := by
  let t : ℝ := (2 : ℝ) ^ n
  let α : ℝ := β / 2
  have ht : 0 < t :=
    pow_pos (by norm_num) _
  have hRα : 0 < R ^ α :=
    Real.rpow_pos_of_pos hR _
  have htα :
      t ^ α = (2 : ℝ) ^ ((n : ℝ) * α) := by
    dsimp only [t]
    rw [← Real.rpow_natCast]
    exact (Real.rpow_mul (by norm_num) _ _).symm
  have hratio :
      (R / t) ^ α / R ^ α =
        (2 : ℝ) ^ (-β * (n : ℝ) / 2) := by
    calc
      (R / t) ^ α / R ^ α =
          (R ^ α / t ^ α) / R ^ α := by
        rw [Real.div_rpow hR.le ht.le]
      _ = (t ^ α)⁻¹ := by
        field_simp
      _ = (2 : ℝ) ^ (-β * (n : ℝ) / 2) := by
        rw [htα, ← Real.rpow_neg (by norm_num)]
        congr 1
        ring
  have hqSq :
      ((2 : ℝ) ^ (-β * (n : ℝ) / 2)) ^ 2 =
        (2 : ℝ) ^ (-β * (n : ℝ)) := by
    rw [← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hbase :
      4 * Real.sqrt 2 * Real.sqrt E / R ^ α *
          (R / t) ^ α =
        4 * Real.sqrt 2 * Real.sqrt E *
          (2 : ℝ) ^ (-β * (n : ℝ) / 2) := by
    calc
      4 * Real.sqrt 2 * Real.sqrt E / R ^ α *
          (R / t) ^ α =
          4 * Real.sqrt 2 * Real.sqrt E *
            ((R / t) ^ α / R ^ α) := by
        field_simp
      _ = _ := by
        rw [hratio]
  change
    32 * (2 : ℝ) ^ (-β * (n : ℝ)) * E =
      (4 * Real.sqrt 2 * Real.sqrt E / R ^ α *
        (R / t) ^ α) ^ 2
  rw [hbase, mul_pow, mul_pow, mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt hE, hqSq]
  ring

/-- Two-dimensional square hole filling produces a uniform dyadic
centered-cube Campanato bound from a uniform bound `E` on the initial
`lam`-normalized coefficient energy.

The normalized cube Poincaré computation is exact:
its raw constant `128 r²`, divided by the square volume `4 r²`, gives
`osc₂² ≤ 32 Eλ`. Consequently the displayed Campanato constant is
`4 sqrt 2 sqrt E / R ^ α`. -/
theorem
    dyadicCenteredCubeCampanatoBoundOn_of_square_hole_filling
    {lam Lam R E : ℝ} {U S : Set (Vec 2)}
    {a : CoeffField 2} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U) (hR : 0 < R)
    (hS : ∀ x ∈ S, centeredAxisCube x R ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 < Lam)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u)
    (hE : ∀ x ∈ S,
      (∫ z in centeredAxisCube x R,
        vecDot (u.grad z)
          (matVecMul (a z) (u.grad z))) / lam ≤ E) :
    DyadicCenteredCubeCampanatoBoundOn u S R
      (squareHoleFillingHolderExponent lam Lam)
      (4 * Real.sqrt 2 * Real.sqrt E /
        R ^ squareHoleFillingHolderExponent lam Lam) := by
  intro x hx n
  let β : ℝ :=
    holeFillingDyadicExponent
      (687865857 * Real.sqrt (Lam / lam))
  let α : ℝ := β / 2
  let r : ℝ := R / (2 : ℝ) ^ n
  change
    centeredCubeL2Oscillation u x r ≤
      4 * Real.sqrt 2 * Real.sqrt E /
        R ^ α * r ^ α
  have hr : 0 < r := by
    dsimp only [r]
    exact div_pos hR (pow_pos (by norm_num) _)
  have hrR : r ≤ R := by
    dsimp only [r]
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ n :=
      one_le_pow₀ (by norm_num)
    apply (div_le_iff₀ (pow_pos (by norm_num) _)).2
    nlinarith
  have hQU : centeredAxisCube x r ⊆ U :=
    (centeredAxisCube_mono x hrR).trans (hS x hx)
  have henergyNonneg :
      0 ≤ (∫ z in centeredAxisCube x R,
        vecDot (u.grad z)
          (matVecMul (a z) (u.grad z))) / lam := by
    apply div_nonneg
    · apply integral_nonneg_of_ae
      filter_upwards [
          ae_restrict_mem
            (isOpen_centeredAxisCube x R).measurableSet] with
        z hz
      exact
        (mul_nonneg hlam.le
          (vecNormSq_nonneg (u.grad z))).trans
            ((hEll.elliptic ((hS x hx) hz)).coercive
              (u.grad z))
    · exact hlam.le
  have hENonneg : 0 ≤ E :=
    henergyNonneg.trans (hE x hx)
  have hPoincareRaw :=
    centeredPoincare_sq_on_boundedConvexSubdomain u
      (isOpenBoundedConvexDomain_centeredAxisCube x r)
      hQU
      (hasEuclideanDiameterLE_centeredAxisCube x hr.le)
      (mul_nonneg (Real.sqrt_nonneg _)
        (by linarith : 0 ≤ 2 * r))
      ⟨x, center_mem_centeredAxisCube x hr⟩
  have hPoincare :
      ∫ z in centeredAxisCube x r,
          (u z -
            integralAverage (centeredAxisCube x r) u) ^ 2 ≤
        128 * r ^ 2 *
          ∫ z in centeredAxisCube x r,
            vecNormSq (u.grad z) := by
    have hcoeff :
        ((2 : ℝ) ^ 2 *
          (Real.sqrt 2 * (2 * r))) ^ 2 =
            128 * r ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow,
        Real.sq_sqrt
          (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    calc
      ∫ z in centeredAxisCube x r,
          (u z -
            integralAverage
              (centeredAxisCube x r) u) ^ 2 ≤
          ((2 : ℝ) ^ 2 *
            (Real.sqrt 2 * (2 * r))) ^ 2 *
              ∫ z in centeredAxisCube x r,
                vecNormSq (u.grad z) := by
        simpa only using! hPoincareRaw
      _ = 128 * r ^ 2 *
          ∫ z in centeredAxisCube x r,
            vecNormSq (u.grad z) := by
        rw [hcoeff]
  have hgrad :=
    setIntegral_vecNormSq_le_coefficientEnergy_div
      hEll u.gradMemL2
      (isOpen_centeredAxisCube x r).measurableSet
      hQU hlam
  have hdecay :=
    square_hole_filling_dyadic_decay
      hU x hR (hS x hx) hEll hlam hLam hsol n
  have hIntegral :
      ∫ z in centeredAxisCube x r,
          (u z -
            integralAverage (centeredAxisCube x r) u) ^ 2 ≤
        128 * r ^ 2 *
          (2 : ℝ) ^ (-β * (n : ℝ)) * E := by
    calc
      ∫ z in centeredAxisCube x r,
          (u z -
            integralAverage
              (centeredAxisCube x r) u) ^ 2 ≤
          128 * r ^ 2 *
            ∫ z in centeredAxisCube x r,
              vecNormSq (u.grad z) :=
        hPoincare
      _ ≤ 128 * r ^ 2 *
          ((∫ z in centeredAxisCube x r,
            vecDot (u.grad z)
              (matVecMul (a z) (u.grad z))) / lam) := by
        gcongr
      _ ≤ 128 * r ^ 2 *
          ((2 : ℝ) ^ (-β * (n : ℝ)) *
            ((∫ z in centeredAxisCube x R,
              vecDot (u.grad z)
                (matVecMul (a z) (u.grad z))) / lam)) := by
        gcongr
      _ ≤ 128 * r ^ 2 *
          ((2 : ℝ) ^ (-β * (n : ℝ)) * E) := by
        gcongr
        exact hE x hx
      _ = 128 * r ^ 2 *
          (2 : ℝ) ^ (-β * (n : ℝ)) * E := by
        ring
  have hOscSq :
      centeredCubeL2Oscillation u x r ^ 2 ≤
        32 * (2 : ℝ) ^ (-β * (n : ℝ)) * E := by
    rw [
      centeredCubeL2Oscillation_sq_eq_setIntegral_div_volume]
    calc
      (∫ z in centeredAxisCube x r,
          (u z -
            integralAverage
              (centeredAxisCube x r) u) ^ 2) /
          (volume (centeredAxisCube x r)).toReal ≤
        (128 * r ^ 2 *
          (2 : ℝ) ^ (-β * (n : ℝ)) * E) /
          (volume (centeredAxisCube x r)).toReal :=
        div_le_div_of_nonneg_right hIntegral
          (volume_centeredAxisCube_toReal_pos x hr).le
      _ = 32 * (2 : ℝ) ^ (-β * (n : ℝ)) * E := by
        rw [volume_centeredAxisCube_toReal x hr.le]
        field_simp [hr.ne']
        ring
  have hright :
      0 ≤ 4 * Real.sqrt 2 * Real.sqrt E /
        R ^ α * r ^ α := by
    exact mul_nonneg
      (div_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num)
            (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _))
        (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg hr.le _)
  apply
    (sq_le_sq₀
      (centeredCubeL2Oscillation_nonneg u x r)
      hright).mp
  calc
    centeredCubeL2Oscillation u x r ^ 2 ≤
        32 * (2 : ℝ) ^ (-β * (n : ℝ)) * E :=
      hOscSq
    _ =
        (4 * Real.sqrt 2 * Real.sqrt E /
          R ^ α * r ^ α) ^ 2 := by
      simpa only [r, α] using
        dyadicEnergyScale_sq
          (β := β) hR hENonneg n

-- The metric balls in the next proof are the inherited supremum-metric
-- cubes, used only through the explicit native-cube bridge.
private theorem innerCenter_initialCube_subset
    (x₀ z : Vec 2) {R : ℝ} (hR : 0 < R)
    (hz : z ∈ closedCenteredAxisCube x₀ (R / 5)) :
    centeredAxisCube z (4 * R / 5) ⊆
      centeredAxisCube x₀ R := by
  have hsmall : 0 ≤ R / 5 := by
    positivity
  have hscale : 0 < 4 * R / 5 := by
    positivity
  have hz' :
      z ∈ Metric.closedBall x₀ (R / 5) := by
    rw [←
      closedCenteredAxisCube_eq_metric_closedBall
        x₀ hsmall]
    exact hz
  rw [centeredAxisCube_eq_metric_ball z hscale,
    centeredAxisCube_eq_metric_ball x₀ hR]
  apply Metric.ball_subset_ball'
  have hdist : dist z x₀ ≤ R / 5 :=
    Metric.mem_closedBall.mp hz'
  linarith

/-- On the buffered inner fifth of an outer square, the uniform initial
energy in the Campanato theorem can be taken to be the normalized
coefficient energy of the single outer square.

The Campanato initial half-side is `4R/5`; every such cube centered in the
closed inner `R/5` cube remains inside the outer `R` cube. -/
theorem square_hole_filling_dyadicCampanatoBoundOn_innerCube
    {lam Lam : ℝ} {U : Set (Vec 2)}
    {a : CoeffField 2} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (x₀ : Vec 2) {R : ℝ} (hR : 0 < R)
    (houter : centeredAxisCube x₀ R ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 < Lam)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u) :
    DyadicCenteredCubeCampanatoBoundOn u
      (closedCenteredAxisCube x₀ (R / 5))
      (4 * R / 5)
      (squareHoleFillingHolderExponent lam Lam)
      (4 * Real.sqrt 2 *
        Real.sqrt
          ((∫ z in centeredAxisCube x₀ R,
            vecDot (u.grad z)
              (matVecMul (a z) (u.grad z))) / lam) /
        (4 * R / 5) ^
          squareHoleFillingHolderExponent lam Lam) := by
  let energy : Vec 2 → ℝ :=
    fun z =>
      vecDot (u.grad z)
        (matVecMul (a z) (u.grad z))
  have henergyU : IntegrableOn energy U :=
    integrableOn_coefficientEnergy_of_isEllipticFieldOn
      hEll u.gradMemL2
  have henergyOuter :
      IntegrableOn energy (centeredAxisCube x₀ R) :=
    henergyU.mono_set houter
  apply
    dyadicCenteredCubeCampanatoBoundOn_of_square_hole_filling
      hU (by positivity)
      (fun z hz =>
        (innerCenter_initialCube_subset x₀ z hR hz).trans
          houter)
      hEll hlam hLam hsol
  intro z hz
  have hsub :=
    innerCenter_initialCube_subset x₀ z hR hz
  have hnonneg :
      0 ≤ᵐ[
        volume.restrict (centeredAxisCube x₀ R)]
        energy := by
    filter_upwards [
        ae_restrict_mem
          (isOpen_centeredAxisCube x₀ R).measurableSet] with
      w hw
    exact
      (mul_nonneg hlam.le
        (vecNormSq_nonneg (u.grad w))).trans
          ((hEll.elliptic (houter hw)).coercive
            (u.grad w))
  have hmono :
      (∫ w in centeredAxisCube z (4 * R / 5),
          energy w) ≤
        ∫ w in centeredAxisCube x₀ R, energy w :=
    setIntegral_mono_set henergyOuter hnonneg
      (Filter.Eventually.of_forall fun w hw =>
        hsub hw)
  exact div_le_div_of_nonneg_right hmono hlam.le

/-- The square hole-filling Hölder exponent has the sharp ellipticity order
`sqrt (lam / Lam)`, up to the displayed numerical factor. -/
theorem squareHoleFillingHolderExponent_lowerBound
    {lam Lam R : ℝ} {U : Set (Vec 2)}
    {a : CoeffField 2} (x₀ : Vec 2)
    (hR : 0 < R)
    (houter : centeredAxisCube x₀ R ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    Real.sqrt (lam / Lam) /
        (4 * 687865857) ≤
      squareHoleFillingHolderExponent lam Lam := by
  have hlower :=
    square_hole_filling_dyadicExponent_lowerBound
      x₀ hR houter hEll
  unfold squareHoleFillingHolderExponent
  nlinarith

end

end PDE
