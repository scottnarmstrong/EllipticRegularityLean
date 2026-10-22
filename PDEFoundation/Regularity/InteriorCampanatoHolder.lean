module

public import PDEFoundation.Regularity.CampanatoConstant
public import PDEFoundation.Regularity.CubeGradient
public import PDEFoundation.Regularity.DyadicCampanato
public import PDEFoundation.Regularity.HolderLocalToGlobal
public import PDEFoundation.Geometry.EuclideanBall.Interior
public import PDEFoundation.Analysis.DyadicRadius
public import PDEFoundation.Sobolev.H1.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Interior Campanato and Hölder estimates from gradient-scale control

This module converts normalized gradient bounds on all interior balls into a
dyadic cube Campanato row, then packages the selected representative as a
Hölder function on the half ball.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The cube Poincaré and enclosing-ball volume factor in the cube-gradient
oscillation estimate. -/
def interiorCampanatoCubeCoefficient (d : ℕ) : ℝ :=
  ((2 : ℝ) ^ d * (2 * Real.sqrt d)) *
    Real.sqrt ((Real.sqrt d) ^ d *
      (volume (euclideanBall (0 : Vec d) 1)).toReal)

/-- A fixed dyadic starting half-side whose enclosing ball lies in the
interior half ball. -/
def interiorCampanatoBaseRadius (d : ℕ) : ℝ :=
  1 / (4 * Real.sqrt d)

theorem interiorCampanatoCubeCoefficient_pos (hd : 0 < d) :
    0 < interiorCampanatoCubeCoefficient d := by
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdR
  have hunit : 0 < (volume (euclideanBall (0 : Vec d) 1)).toReal :=
    volume_euclideanBall_toReal_pos _ (by norm_num)
  unfold interiorCampanatoCubeCoefficient
  positivity

theorem interiorCampanatoBaseRadius_pos (hd : 0 < d) :
    0 < interiorCampanatoBaseRadius d := by
  have hsqrt : 0 < Real.sqrt d :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  unfold interiorCampanatoBaseRadius
  positivity

/-- An all-centre gradient-scale row gives the corresponding dyadic
centered-cube Campanato row at the dimension-scaled base radius. -/
theorem dyadicCenteredCubeCampanatoBoundOn_of_interiorGradientScale
    (hd : 0 < d) {α K : ℝ} (hα1 : α < 1)
    (hK : 0 ≤ K) {u : H1Function (euclideanBall (0 : Vec d) 1)}
    (hscale : ∀ z ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ,
      0 < r → r ≤ 1 / 2 →
        r ^ (1 - α) *
          Real.sqrt (integralAverage (euclideanBall z r)
            (fun x => vecNormSq (u.grad x))) ≤ K) :
    DyadicCenteredCubeCampanatoBoundOn u.toFun
      (euclideanBall (0 : Vec d) (1 / 2))
      (interiorCampanatoBaseRadius d) α
      (interiorCampanatoCubeCoefficient d * K) := by
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hroot : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdR
  have hdge1 : 1 ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hd)
  have hrootge1 : 1 ≤ Real.sqrt d := by
    have hsqrt := Real.sqrt_le_sqrt hdge1
    simpa using hsqrt
  have hH : 1 ≤ 2 * Real.sqrt d := by nlinarith
  have hR : 0 < interiorCampanatoBaseRadius d :=
    interiorCampanatoBaseRadius_pos hd
  have hKcube : 0 ≤ interiorCampanatoCubeCoefficient d * K :=
    mul_nonneg (interiorCampanatoCubeCoefficient_pos hd).le hK
  intro z hz n
  let r := dyadicRadius (interiorCampanatoBaseRadius d) n
  let rb := 2 * Real.sqrt d * r
  have hr : 0 < r := by
    dsimp [r]
    exact dyadicRadius_pos hR n
  have hrle : r ≤ interiorCampanatoBaseRadius d := by
    dsimp [r]
    exact dyadicRadius_le hR.le n
  have hrball : 0 < rb := by
    dsimp [rb]
    exact mul_pos (mul_pos (by norm_num) hroot) hr
  have hrball_le : rb ≤ 1 / 2 := by
    dsimp [rb]
    calc
      2 * Real.sqrt d * r ≤
          (2 * Real.sqrt d) * interiorCampanatoBaseRadius d :=
        mul_le_mul_of_nonneg_left hrle (by positivity)
      _ = 1 / 2 := by
        rw [interiorCampanatoBaseRadius]
        field_simp
        ring
  have hball : euclideanBall z rb ⊆ euclideanBall (0 : Vec d) 1 := by
    have hsmall : euclideanBall z rb ⊆ euclideanBall z (1 / 2) :=
      euclideanBall_mono hrball.le hrball_le
    exact hsmall.trans (euclideanBall_half_subset_unit_of_center_mem_half hz)
  have hscale' := hscale z hz rb hrball hrball_le
  have hrpowPos : 0 < rb ^ (1 - α) :=
    Real.rpow_pos_of_pos hrball _
  have havg :
      Real.sqrt (integralAverage (euclideanBall z rb)
          (fun x => vecNormSq (u.grad x))) ≤ K / rb ^ (1 - α) := by
    apply (le_div_iff₀ hrpowPos).2
    simpa only [mul_comm] using hscale'
  have hrle_rb : r ≤ rb := by
    dsimp [rb]
    calc
      r = 1 * r := by ring
      _ ≤ (2 * Real.sqrt d) * r :=
        mul_le_mul_of_nonneg_right hH hr.le
  have hpower_mono : r ^ (1 - α) ≤ rb ^ (1 - α) :=
    Real.rpow_le_rpow hr.le hrle_rb (sub_nonneg.mpr hα1.le)
  have hpower_pos : 0 < r ^ (1 - α) :=
    Real.rpow_pos_of_pos hr _
  have hratio : r / rb ^ (1 - α) ≤ r ^ α := by
    calc
      r / rb ^ (1 - α) ≤ r / r ^ (1 - α) :=
        div_le_div_of_nonneg_left hr.le hpower_pos hpower_mono
      _ = r ^ α := by
        apply (div_eq_iff (ne_of_gt hpower_pos)).2
        have hpow : r ^ α * r ^ (1 - α) = r := by
          calc
            r ^ α * r ^ (1 - α) = r ^ (α + (1 - α)) :=
              (Real.rpow_add hr α (1 - α)).symm
            _ = r := by
              rw [show α + (1 - α) = 1 by ring, Real.rpow_one]
        exact hpow.symm
  have hcube := centeredCubeL2Oscillation_le_radius_mul_ball_gradient_mean
    hd u z hr hball
  have hcube' :
      centeredCubeL2Oscillation u.toFun z r ≤
        (interiorCampanatoCubeCoefficient d * r) *
          Real.sqrt (integralAverage (euclideanBall z rb)
            (fun x => vecNormSq (u.grad x))) := by
    simpa only [interiorCampanatoCubeCoefficient, rb] using hcube
  have hcamp :
      centeredCubeL2Oscillation u.toFun z r ≤
        (interiorCampanatoCubeCoefficient d * K) * r ^ α := by
    calc
      centeredCubeL2Oscillation u.toFun z r ≤
          (interiorCampanatoCubeCoefficient d * r) *
            Real.sqrt (integralAverage (euclideanBall z rb)
              (fun x => vecNormSq (u.grad x))) := hcube'
      _ ≤ (interiorCampanatoCubeCoefficient d * r) * (K / rb ^ (1 - α)) :=
        mul_le_mul_of_nonneg_left havg
          (mul_nonneg (interiorCampanatoCubeCoefficient_pos hd).le hr.le)
      _ = (interiorCampanatoCubeCoefficient d * K) *
          (r / rb ^ (1 - α)) := by ring
      _ ≤ (interiorCampanatoCubeCoefficient d * K) * r ^ α :=
        mul_le_mul_of_nonneg_left hratio hKcube
  simpa only [r, dyadicRadius] using hcamp

private theorem centeredCubeL2Oscillation_congr_ae
    {f g : Vec d → ℝ} {z : Vec d} {r : ℝ}
    (hfg : f =ᵐ[volumeOn (centeredAxisCube z r)] g) :
    centeredCubeL2Oscillation f z r = centeredCubeL2Oscillation g z r := by
  have hmean : centeredCubeAverage f z r = centeredCubeAverage g z r :=
    integralAverage_congr_ae hfg
  have hfgNorm : f =ᵐ[normalizedVolumeOn (centeredAxisCube z r)] g := by
    unfold normalizedVolumeOn
    exact MeasureTheory.Measure.ae_smul_measure hfg _
  unfold centeredCubeL2Oscillation
  rw [hmean]
  congr 1
  apply integral_congr_ae
  filter_upwards [hfgNorm] with x hx
  rw [hx]

/-- In positive dimension, an all-centre, all-radius gradient-scale bound on
the half ball gives a genuine Euclidean Hölder representative there. The
dimension-only constant is chosen before the exponent, function, and energy
bound. -/
theorem exists_interiorCampanato_holder_constant
    (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α K : ℝ}, 0 < α → α < 1 → 0 ≤ K →
        ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
          (∀ z ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ,
            0 < r → r ≤ 1 / 2 →
              r ^ (1 - α) *
                Real.sqrt (integralAverage (euclideanBall z r)
                  (fun x => vecNormSq (u.grad x))) ≤ K) →
          HasEuclideanHolderRepresentativeOn
            (euclideanBall (0 : Vec d) (1 / 2)) u.toFun α (C * K / α) := by
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hroot : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdR
  have hdge1 : 1 ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hd)
  have hrootge1 : 1 ≤ Real.sqrt d := by
    have hsqrt := Real.sqrt_le_sqrt hdge1
    simpa using hsqrt
  have hscaleBase : 0 < 8 * Real.sqrt d := by positivity
  obtain ⟨N, hNlarge⟩ := exists_nat_gt (8 * Real.sqrt d)
  have hNreal : 0 < (N : ℝ) := lt_trans hscaleBase hNlarge
  have hN : 0 < N := by exact_mod_cast hNreal
  have hRhalf : interiorCampanatoBaseRadius d / 2 =
      1 / (8 * Real.sqrt d) := by
    unfold interiorCampanatoBaseRadius
    field_simp
    ring
  have hNrho :
      1 ≤ (N : ℝ) * (interiorCampanatoBaseRadius d / 2) := by
    rw [hRhalf]
    calc
      1 ≤ (N : ℝ) / (8 * Real.sqrt d) := by
        apply (le_div_iff₀ hscaleBase).2
        nlinarith only [hNlarge]
      _ = (N : ℝ) * (1 / (8 * Real.sqrt d)) := by ring
  let A := interiorCampanatoCubeCoefficient d
  let C := (N : ℝ) * (32 * Real.sqrt ((2 : ℝ) ^ d)) * A
  have hApos : 0 < A := by
    dsimp [A]
    exact interiorCampanatoCubeCoefficient_pos hd
  have hroot2pos : 0 < Real.sqrt ((2 : ℝ) ^ d) :=
    Real.sqrt_pos.mpr (by positivity)
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hCpos, ?_⟩
  intro α K hα0 hα1 hK u hscale
  let U := euclideanBall (0 : Vec d) 1
  let S := euclideanBall (0 : Vec d) (1 / 2)
  let g : Vec d → ℝ := U.indicator u.toFun
  have hUopen : IsOpen U := by
    dsimp [U]
    exact isOpen_euclideanBall _ _
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  let : IsFiniteMeasure (volumeOn U) := by
    dsimp [U]
    exact isFiniteMeasure_volumeOn_euclideanBall _ (by norm_num)
  have huInt : IntegrableOn u.toFun U := by
    exact MeasureTheory.MemLp.integrable (q := (2 : ℝ≥0∞))
      (by norm_num) u.memL2
  have huSqInt : IntegrableOn (fun x => u.toFun x ^ 2) U := by
    simpa [pow_two] using
      (integrableOn_mul_of_memL2On (U := U) u.memL2 u.memL2)
  have hgInt : Integrable g volume := by
    dsimp [g]
    exact huInt.integrable_indicator hUmeas
  have hgSqFun : (fun x => g x ^ 2) =
      U.indicator (fun x => u.toFun x ^ 2) := by
    funext x
    by_cases hx : x ∈ U <;> simp [g, hx]
  have hgSqInt : Integrable (fun x => g x ^ 2) volume := by
    rw [hgSqFun]
    exact huSqInt.integrable_indicator hUmeas
  have hgLoc : LocallyIntegrable g volume := hgInt.locallyIntegrable
  have hgSqLoc : LocallyIntegrable (fun x => g x ^ 2) volume :=
    hgSqInt.locallyIntegrable
  have hcampU :=
    dyadicCenteredCubeCampanatoBoundOn_of_interiorGradientScale
      hd hα1 hK hscale
  have hcampG :
      DyadicCenteredCubeCampanatoBoundOn g S
        (interiorCampanatoBaseRadius d) α (A * K) := by
    intro z hz n
    let r := dyadicRadius (interiorCampanatoBaseRadius d) n
    let rb := 2 * Real.sqrt d * r
    have hr : 0 < r := by
      dsimp [r]
      exact dyadicRadius_pos (interiorCampanatoBaseRadius_pos hd) n
    have hrball : 0 < rb := by
      dsimp [rb]
      exact mul_pos (mul_pos (by norm_num) hroot) hr
    have hrle : r ≤ interiorCampanatoBaseRadius d := by
      dsimp [r]
      exact dyadicRadius_le (interiorCampanatoBaseRadius_pos hd).le n
    have hrball_le : rb ≤ 1 / 2 := by
      dsimp [rb]
      calc
        2 * Real.sqrt d * r ≤
            (2 * Real.sqrt d) * interiorCampanatoBaseRadius d :=
          mul_le_mul_of_nonneg_left hrle (by positivity)
        _ = 1 / 2 := by
          rw [interiorCampanatoBaseRadius]
          field_simp
          ring
    have hcubeBall : centeredAxisCube z r ⊆ euclideanBall z rb :=
      centeredAxisCube_subset_euclideanBall hd z hr
    have hballHalf : euclideanBall z rb ⊆ euclideanBall z (1 / 2) :=
      euclideanBall_mono hrball.le hrball_le
    have hballUnit : euclideanBall z (1 / 2) ⊆ U := by
      dsimp [U]
      exact euclideanBall_half_subset_unit_of_center_mem_half hz
    have hcubeUnit : centeredAxisCube z r ⊆ U :=
      hcubeBall.trans (hballHalf.trans hballUnit)
    have hfg : g =ᵐ[volumeOn (centeredAxisCube z r)] u.toFun := by
      filter_upwards
        [ae_restrict_mem (isOpen_centeredAxisCube z r).measurableSet]
        with x hx
      have hxU := hcubeUnit hx
      simp [g, hxU]
    have hoscEq := centeredCubeL2Oscillation_congr_ae hfg
    change centeredCubeL2Oscillation g z r ≤ (A * K) * r ^ α
    rw [hoscEq]
    simpa [r, dyadicRadius, A] using hcampU z hz n
  have hR : 0 < interiorCampanatoBaseRadius d :=
    interiorCampanatoBaseRadius_pos hd
  have hA_K : 0 ≤ A * K := mul_nonneg hApos.le hK
  have hRepGlobal := dyadicCenteredCubeRepresentative_ae_eq hgLoc hR
  let rep := dyadicCenteredCubeRepresentative g (interiorCampanatoBaseRadius d)
  have hRepS : rep =ᵐ[volumeOn S] g :=
    hRepGlobal.filter_mono (ae_mono Measure.restrict_le_self)
  have hgU : g =ᵐ[volumeOn S] u.toFun := by
    filter_upwards
      [ae_restrict_mem (isOpen_euclideanBall (0 : Vec d) (1 / 2)).measurableSet]
      with x hx
    have hxU : x ∈ U := by
      dsimp [U]
      exact euclideanBall_mono (by norm_num) (by norm_num) hx
    simp [g, hxU]
  have hRep : rep =ᵐ[volumeOn S] u.toFun := hRepS.trans hgU
  have hlocalK :
      0 ≤ dyadicCampanatoHolderConst d α * (A * K) :=
    mul_nonneg (dyadicCampanatoHolderConst_nonneg d hα0) hA_K
  have hlocal : ∀ x ∈ S, ∀ y ∈ S,
      ‖x - y‖ ≤ interiorCampanatoBaseRadius d / 2 →
        |rep x - rep y| ≤
          (dyadicCampanatoHolderConst d α * (A * K)) * ‖x - y‖ ^ α := by
    intro x hx y hy hxy
    exact hcampG.abs_representative_sub_le hα0 hR hA_K
      (fun z hz => locallyIntegrable_integrableOn_centeredAxisCube hgLoc z hR)
      (fun z hz => locallyIntegrable_integrableOn_centeredAxisCube hgSqLoc z hR)
      hx hy hxy
  have hglobalK :
      0 ≤ (N : ℝ) * (dyadicCampanatoHolderConst d α * (A * K)) :=
    mul_nonneg hNreal.le hlocalK
  have hglobal : SupHolderSeminormLE S rep α
      ((N : ℝ) * (dyadicCampanatoHolderConst d α * (A * K))) := by
    intro x hx y hy
    exact abs_sub_le_of_localHolder_on_convex
      (convex_euclideanBall (0 : Vec d) (1 / 2))
      (fun x hx y hy => norm_sub_le_one_of_mem_euclideanBall_half hx hy)
      hα0 hlocalK hN hNrho hlocal x hx y hy
  have hconstantBound :
      (N : ℝ) * (dyadicCampanatoHolderConst d α * (A * K)) ≤ C * K / α := by
    have hfactorNonneg : 0 ≤ (N : ℝ) * (A * K) :=
      mul_nonneg hNreal.le hA_K
    calc
      (N : ℝ) * (dyadicCampanatoHolderConst d α * (A * K)) =
          ((N : ℝ) * (A * K)) * dyadicCampanatoHolderConst d α := by ring
      _ ≤ ((N : ℝ) * (A * K)) *
          ((32 * Real.sqrt ((2 : ℝ) ^ d)) / α) :=
        mul_le_mul_of_nonneg_left
          (dyadicCampanatoHolderConst_le_inv_alpha d hα0 hα1)
          hfactorNonneg
      _ = C * K / α := by
        dsimp [C, A]
        ring
  have hHolderSup :=
    (supHolderSeminormLE_to_euclidean hglobal hα0.le hglobalK).mono_const
      hconstantBound
  exact ⟨rep, hRep, hHolderSup⟩

end

end PDE
