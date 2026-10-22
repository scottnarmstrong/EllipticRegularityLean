module

public import EllipticRegularity.Meyers.EnergyBounds
public import EllipticRegularity.Meyers.CubeSP
public import EllipticRegularity.Meyers.Cutoff
public import EllipticRegularity.Meyers.RHIdentity
public import EllipticRegularity.Meyers.RHInteriorNorm
public import EllipticRegularity.Meyers.RHInteriorSP
public import PDEFoundation.Measure.EuclideanFieldMeasurability
public import PDEFoundation.Measure.EuclideanFieldLpTriangle
public import PDEFoundation.Sobolev.W1p.EuclideanGradient

/-!
# The interior reverse Hölder inequality (Lemma 4.5 (i))
-/

@[expose] public section

open scoped ENNReal

namespace PDE.MeyersRH

open MeasureTheory

/-- A native vector field in `L²(U)` has Euclidean magnitude in `L²` for the normalized
volume of any positive-volume subset `V ⊆ U`. -/
theorem memLp_norm_normalizedVolumeOn {d : ℕ} {U V : Set (Vec d)} {F : Vec d → Vec d}
    (hF : MemVectorL2On U F) (hVU : V ⊆ U) (hVpos : 0 < volume V) :
    MemLp (fun x => vecEuclideanNorm (F x)) 2 (normalizedVolumeOn V) :=
  memLp_normalizedVolumeOn_of_memLpOn
    (GradMemLpOn.memLp_vecEuclideanNorm hF |>.mono_measure
      (Measure.restrict_mono_set volume hVU)) hVpos

theorem memLp_normalizedVolumeOn_of_sub {d : ℕ} {U V : Set (Vec d)} {g : Vec d → ℝ}
    (hg : MemL2On U g) (hVU : V ⊆ U) (hVpos : 0 < volume V) :
    MemLp g 2 (normalizedVolumeOn V) :=
  memLp_normalizedVolumeOn_of_memLpOn (hg.mono_measure (Measure.restrict_mono_set volume hVU))
    hVpos


/-- The interior reverse Hölder inequality for one cube, with the explicit constant
`interiorConst d S`, given the cube Sobolev--Poincaré inequality with constant `S`. -/
theorem interior_core {d : ℕ} (hd : 2 ≤ d) {S : ℝ} (hS : 0 < S)
    (hSPc : ∀ (z : Vec d) (r : ℝ), 0 < r →
      ∀ v : W1pFunction (centeredAxisCube z r)
          (ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) + 1))),
        eLpMeanNormOn (centeredAxisCube z r)
            (ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) - 1)))
            (fun x => v.toFun x - integralAverage (centeredAxisCube z r) v.toFun) ≤
          ENNReal.ofReal (S * (2 * r)) *
            euclideanFieldELpMeanNormOn (centeredAxisCube z r)
              (ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) + 1))) v.grad)
    {Λ : ℝ} {U : Set (Vec d)} {a : CoeffField d}
    (hU : IsOpenBoundedConvexDomain U) (hEll : IsEllipticFieldOn 1 Λ U a) (hΛ : 1 ≤ Λ)
    (u : H1Function U) (f : Vec d → Vec d) (hf : MemVectorL2On U f)
    (hsol : IsWeakDivergenceFormSolutionOn a U u (0 : Vec d → ℝ) f)
    (z : Vec d) {r : ℝ} (hr : 0 < r) (hV : centeredAxisCube z (2 * r) ⊆ U) :
    ∫ x in centeredAxisCube z r,
        Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x))) ^ 2 ≤
      (interiorConst d S * Real.sqrt Λ) * (volume (centeredAxisCube z r)).toReal *
          (integralAverage (centeredAxisCube z (2 * r))
            (fun x => (Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x))) ^ 2) ^
              ((d : ℝ) / ((d : ℝ) + 1)))) ^ (((d : ℝ) + 1) / (d : ℝ)) +
        interiorConst d S *
          ∫ x in centeredAxisCube z (2 * r), vecEuclideanNorm (f x) ^ 2 := by
  classical
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hr2 : 0 < 2 * r := by linarith
  have hVmeas : MeasurableSet (centeredAxisCube z (2 * r)) :=
    (isOpen_centeredAxisCube z _).measurableSet
  have hVpos : 0 < volume (centeredAxisCube z (2 * r)) := volume_centeredAxisCube_pos z hr2
  have hVtop : volume (centeredAxisCube z (2 * r)) < ∞ :=
    (volume_centeredAxisCube_ne_top z _).lt_top
  have hQV : centeredAxisCube z r ⊆ centeredAxisCube z (2 * r) := by
    intro x hx i _
    have := hx i (Set.mem_univ i)
    simp only [Set.mem_Ioo] at this ⊢
    constructor <;> linarith [this.1, this.2]
  have hQU : centeredAxisCube z r ⊆ U := hQV.trans hV
  have hVreal : (volume (centeredAxisCube z (2 * r))).toReal =
      2 ^ d * (volume (centeredAxisCube z r)).toReal :=
    volume_centeredAxisCube_two_mul z hr.le
  have hVrealpos : 0 < (volume (centeredAxisCube z (2 * r))).toReal :=
    volume_centeredAxisCube_toReal_pos z hr2
  have hprob : IsProbabilityMeasure (normalizedVolumeOn (centeredAxisCube z (2 * r))) :=
    isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top hVpos hVtop
  -- exponents
  have hq1 : 1 ≤ 2 * (d : ℝ) / ((d : ℝ) + 1) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hqpos : 0 < 2 * (d : ℝ) / ((d : ℝ) + 1) := by linarith
  have hq2 : 2 * (d : ℝ) / ((d : ℝ) + 1) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hconj : (2 * (d : ℝ) / ((d : ℝ) - 1)).HolderConjugate (2 * (d : ℝ) / ((d : ℝ) + 1)) := by
    rw [Real.holderConjugate_iff]
    have h1 : (d : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (d : ℝ) + 1 ≠ 0 := by linarith
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ (by linarith)]; linarith
    · field_simp; ring
  have hqE2 : ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) + 1)) ≤ 2 := by
    calc ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) + 1)) ≤ ENNReal.ofReal 2 :=
          ENNReal.ofReal_le_ofReal hq2
      _ = 2 := by simp
  have hs1 : 1 ≤ Real.sqrt Λ := Real.one_le_sqrt.2 hΛ
  -- the energy density
  have hE0 : ∀ x ∈ U, 0 ≤ vecDot (u.grad x) (matVecMul (a x) (u.grad x)) := by
    intro x hx
    have := (hEll.elliptic hx).coercive (u.grad x)
    linarith [vecNormSq_nonneg (u.grad x)]
  have hflux : MemVectorL2On U (fun x => matVecMul (a x) (u.grad x)) :=
    memVectorL2On_matVecMul_of_isEllipticFieldOn hEll u.gradMemL2
  have hEint : IntegrableOn (fun x => vecDot (u.grad x) (matVecMul (a x) (u.grad x))) U :=
    integrableOn_vecDot_of_memVectorL2On u.gradMemL2 hflux
  have hwfsq : ∀ x ∈ U,
      Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x))) ^ 2 =
        vecDot (u.grad x) (matVecMul (a x) (u.grad x)) :=
    fun x hx => Real.sq_sqrt (hE0 x hx)
  have hwfU : MemLp (fun x => Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x))))
      2 (volumeOn U) := by
    have hm : AEStronglyMeasurable
        (fun x => Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x)))) (volumeOn U) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hEint.aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq hm]
    exact (integrableOn_congr_fun (fun x hx => (hwfsq x hx).symm) hU.measurableSet).mp hEint
  have hwfV : MemLp (fun x => Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x))))
      2 (normalizedVolumeOn (centeredAxisCube z (2 * r))) :=
    memLp_normalizedVolumeOn_of_memLpOn
      (hwfU.mono_measure (Measure.restrict_mono_set volume hV)) hVpos
  have hwfq : MemLp (fun x => Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x))))
      (ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) + 1)))
      (normalizedVolumeOn (centeredAxisCube z (2 * r))) := hwfV.mono_exponent hqE2
  have hgradV := memLp_norm_normalizedVolumeOn u.gradMemL2 hV hVpos
  have hfV := memLp_norm_normalizedVolumeOn hf hV hVpos
  have hfluxV := memLp_norm_normalizedVolumeOn hflux hV hVpos
  have hμV : ∀ᵐ x ∂(normalizedVolumeOn (centeredAxisCube z (2 * r))),
      x ∈ centeredAxisCube z (2 * r) := by
    unfold normalizedVolumeOn
    exact Measure.ae_smul_measure (ae_restrict_mem hVmeas) _
  set V := centeredAxisCube z (2 * r) with hVdef
  set Q := centeredAxisCube z r with hQdef
  set μ := normalizedVolumeOn V with hμdef
  set q : ℝ := 2 * (d : ℝ) / ((d : ℝ) + 1) with hqdef
  set q' : ℝ := 2 * (d : ℝ) / ((d : ℝ) - 1) with hq'def
  set wf : Vec d → ℝ := fun x => Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x)))
    with hwfdef
  set c : ℝ := integralAverage V u.toFun with hcdef
  have hμU : ∀ᵐ x ∂μ, x ∈ U := hμV.mono fun x hx => hV hx
  -- Sobolev--Poincaré on `V`
  have hsp : eLpNorm (fun x => u.toFun x - c) (ENNReal.ofReal q') μ ≤
      ENNReal.ofReal (S * (2 * (2 * r))) *
        eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal q) μ :=
    hSPc z (2 * r) hr2 (restrictCubeW1p u z hV (ENNReal.ofReal q) hqE2)
  have hgrad_le : eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal q) μ ≤
      eLpNorm wf (ENNReal.ofReal q) μ := by
    refine eLpNorm_mono_ae hgradV.aestronglyMeasurable ?_
    filter_upwards [hμU] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _),
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact vecEuclideanNorm_le_energyRoot (hEll.elliptic hx) (u.grad x)
  have hPn : eLpNorm (fun x => u.toFun x - c) (ENNReal.ofReal q') μ ≤
      ENNReal.ofReal (S * (2 * (2 * r))) * eLpNorm wf (ENNReal.ofReal q) μ :=
    hsp.trans (mul_le_mul_right hgrad_le _)
  have hWfin : eLpNorm wf (ENNReal.ofReal q) μ ≠ ∞ := hwfq.eLpNorm_ne_top
  have hum : AEStronglyMeasurable (fun x => u.toFun x - c) μ :=
    (memLp_normalizedVolumeOn_of_sub u.memL2 hV hVpos).aestronglyMeasurable.sub
      aestronglyMeasurable_const
  have hPm : MemLp (fun x => u.toFun x - c) (ENNReal.ofReal q') μ :=
    memLp_iff.2 (lt_of_le_of_lt hPn (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hWfin.lt_top))
  -- the flux plus forcing
  have hcoord : ∀ (F : Vec d → Vec d), MemVectorL2On U F →
      ∀ i, AEStronglyMeasurable (fun x => F x i) μ := fun F hF i =>
    (memLp_normalizedVolumeOn_of_sub (hF i) hV hVpos).aestronglyMeasurable
  have hGmeas : AEStronglyMeasurable
      (fun x => vecEuclideanNorm (matVecMul (a x) (u.grad x) + f x)) μ :=
    aestronglyMeasurable_vecEuclideanNorm_of_coord fun i =>
      (hcoord _ hflux i).add (hcoord _ hf i)
  have hq1E : 1 ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq1
  have hfq : MemLp (fun x => vecEuclideanNorm (f x)) (ENNReal.ofReal q) μ := hfV.mono_exponent hqE2
  have hfluxq : MemLp (fun x => vecEuclideanNorm (matVecMul (a x) (u.grad x)))
      (ENNReal.ofReal q) μ := hfluxV.mono_exponent hqE2
  have hflux_le : eLpNorm (fun x => vecEuclideanNorm (matVecMul (a x) (u.grad x)))
      (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (Real.sqrt Λ) * eLpNorm wf (ENNReal.ofReal q) μ := by
    have hsm : eLpNorm (Real.sqrt Λ • wf) (ENNReal.ofReal q) μ =
        ENNReal.ofReal (Real.sqrt Λ) * eLpNorm wf (ENNReal.ofReal q) μ := by
      rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [← hsm]
    refine eLpNorm_mono_ae hfluxq.aestronglyMeasurable ?_
    filter_upwards [hμU] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _),
      Pi.smul_apply, smul_eq_mul, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _))]
    exact vecEuclideanNorm_matVecMul_le_energyRoot (hEll.elliptic hx) (u.grad x)
  have hG_le : eLpNorm (fun x => vecEuclideanNorm (matVecMul (a x) (u.grad x) + f x))
      (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (Real.sqrt Λ) * eLpNorm wf (ENNReal.ofReal q) μ +
        eLpNorm (fun x => vecEuclideanNorm (f x)) 2 μ := by
    refine (eLpNorm_vecEuclideanNorm_add_le hq1E _ _ hfluxq.aestronglyMeasurable
      hfq.aestronglyMeasurable hGmeas).trans ?_
    exact add_le_add hflux_le (eLpNorm_le_eLpNorm_of_exponent_le hqE2)
  have hFfin : eLpNorm (fun x => vecEuclideanNorm (f x)) 2 μ ≠ ∞ := hfV.eLpNorm_ne_top
  have hGm : MemLp (fun x => vecEuclideanNorm (matVecMul (a x) (u.grad x) + f x))
      (ENNReal.ofReal q) μ :=
    memLp_iff.2 (lt_of_le_of_lt hG_le (ENNReal.add_lt_top.2
      ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hWfin.lt_top, hFfin.lt_top⟩))
  -- real quantities and the Hölder step
  set Wr : ℝ := (eLpNorm wf (ENNReal.ofReal q) μ).toReal with hWr
  set Fr : ℝ := (eLpNorm (fun x => vecEuclideanNorm (f x)) 2 μ).toReal with hFr
  have hWr0 : 0 ≤ Wr := ENNReal.toReal_nonneg
  have hFr0 : 0 ≤ Fr := ENNReal.toReal_nonneg
  set P : Vec d → ℝ := fun x => ‖u.toFun x - c‖ with hPdef
  set G : Vec d → ℝ := fun x => vecEuclideanNorm (matVecMul (a x) (u.grad x) + f x) with hGdef
  have hPm' : MemLp P (ENNReal.ofReal q') μ := hPm.norm
  have hPn_real : (eLpNorm P (ENNReal.ofReal q') μ).toReal ≤ S * (2 * (2 * r)) * Wr := by
    have h1 : eLpNorm P (ENNReal.ofReal q') μ =
        eLpNorm (fun x => u.toFun x - c) (ENNReal.ofReal q') μ := eLpNorm_norm _ hum
    rw [h1]
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hWfin) hPn
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h2
  have hGn_real : (eLpNorm G (ENNReal.ofReal q) μ).toReal ≤ Real.sqrt Λ * Wr + Fr := by
    have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hWfin, hFfin⟩) hG_le
    rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hWfin) hFfin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at h2
  have hHolder := integral_mul_le_toReal_eLpNorm_mul hconj (fun x => norm_nonneg _)
    (fun x => vecEuclideanNorm_nonneg _) hPm' hGm
  have hPG : ∫ x, P x * G x ∂μ ≤ (S * (2 * (2 * r)) * Wr) * (Real.sqrt Λ * Wr + Fr) :=
    hHolder.trans (mul_le_mul hPn_real hGn_real ENNReal.toReal_nonneg (by positivity))
  have hPGint : Integrable (fun x => P x * G x) μ := by
    have := hconj.ennrealOfReal
    exact hPm'.integrable_mul hGm
  have hPGV : IntegrableOn (fun x => P x * G x) V :=
    (integrable_normalizedVolumeOn_iff hVpos hVtop).1 hPGint
  have hPGavg : (volume V).toReal * ∫ x, P x * G x ∂μ = ∫ x in V, P x * G x := by
    rw [integral_normalizedVolumeOn_eq_integralAverage, integralAverage,
      ← mul_assoc, mul_inv_cancel₀ hVrealpos.ne', one_mul]
  -- the cutoff and the identity
  let η := cubeCutoff z hr
  have hid := cutoff_energy_le (c := c) hU hEll u f hf hsol η hV
  set I2 : ℝ := ∫ x in U, (u.toFun x - c) *
      vecDot (matVecMul (a x) (u.grad x) + f x) (classicalGradient η.toFun x) with hI2def
  have hI2V : I2 = ∫ x in V, (u.toFun x - c) *
      vecDot (matVecMul (a x) (u.grad x) + f x) (classicalGradient η.toFun x) := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hV ?_
    intro x hx
    rw [η.classicalGradient_eq_zero_of_not_mem_outer hx.2]
    simp [vecDot]
  have hI2le : |I2| ≤ (32 * (d : ℝ) / r) * ((volume V).toReal * ∫ x, P x * G x ∂μ) := by
    rw [hI2V, ← Real.norm_eq_abs, hPGavg]
    calc ‖∫ x in V, (u.toFun x - c) *
          vecDot (matVecMul (a x) (u.grad x) + f x) (classicalGradient η.toFun x)‖
        ≤ ∫ x in V, (32 * (d : ℝ) / r) * (P x * G x) := by
          refine norm_integral_le_of_norm_le (hPGV.const_mul _) ?_
          filter_upwards [ae_restrict_mem hVmeas] with x hx
          rw [norm_mul, Real.norm_eq_abs]
          have h1 := abs_vecDot_le_vecEuclideanNorm_mul
            (matVecMul (a x) (u.grad x) + f x) (classicalGradient η.toFun x)
          have h2 := η.gradient_bound x
          have hG0 : 0 ≤ vecEuclideanNorm (matVecMul (a x) (u.grad x) + f x) :=
            vecEuclideanNorm_nonneg _
          have h3 : |vecDot (matVecMul (a x) (u.grad x) + f x) (classicalGradient η.toFun x)| ≤
              (32 * (d : ℝ) / r) * G x :=
            h1.trans (by
              calc _ ≤ vecEuclideanNorm (matVecMul (a x) (u.grad x) + f x) *
                    (32 * (d : ℝ) / r) := mul_le_mul_of_nonneg_left h2 hG0
                _ = _ := by simp only [hGdef]; ring)
          calc ‖u.toFun x - c‖ * |vecDot (matVecMul (a x) (u.grad x) + f x)
                (classicalGradient η.toFun x)|
              ≤ ‖u.toFun x - c‖ * ((32 * (d : ℝ) / r) * G x) :=
                mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
            _ = (32 * (d : ℝ) / r) * (P x * G x) := by simp only [hPdef]; ring
      _ = _ := by rw [integral_const_mul]
  have hI2' : |I2| ≤ (32 * (d : ℝ) / r) * (volume V).toReal *
      (S * (2 * (2 * r)) * Wr) * (Real.sqrt Λ * Wr + Fr) := by
    refine hI2le.trans ?_
    have hK : 0 ≤ 32 * (d : ℝ) / r := by positivity
    calc (32 * (d : ℝ) / r) * ((volume V).toReal * ∫ x, P x * G x ∂μ)
        ≤ (32 * (d : ℝ) / r) * ((volume V).toReal *
            ((S * (2 * (2 * r)) * Wr) * (Real.sqrt Λ * Wr + Fr))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPG hVrealpos.le) hK
      _ = _ := by ring
  -- energy comparison
  have hEηint : IntegrableOn
      (fun x => η.toFun x * vecDot (u.grad x) (matVecMul (a x) (u.grad x))) U :=
    hEint.bdd_mul (c := 1) η.smooth.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (η.nonneg x)]; exact η.le_one x)
  have hQle : ∫ x in Q, wf x ^ 2 ≤
      ∫ x in U, η.toFun x * vecDot (u.grad x) (matVecMul (a x) (u.grad x)) := by
    calc ∫ x in Q, wf x ^ 2
        = ∫ x in Q, η.toFun x * vecDot (u.grad x) (matVecMul (a x) (u.grad x)) :=
          setIntegral_congr_fun (isOpen_centeredAxisCube z r).measurableSet fun x hx => by
            rw [η.eq_one_on_inner x hx, one_mul]
            exact hwfsq x (hQU hx)
      _ ≤ _ := setIntegral_mono_set hEηint
          ((ae_restrict_iff' hU.measurableSet).2
            (Filter.Eventually.of_forall fun x hx => mul_nonneg (η.nonneg x) (hE0 x hx)))
          (Filter.Eventually.of_forall fun x hx => hQU hx)
  have hNint : IntegrableOn (fun x => vecNormSq (f x)) U :=
    integrableOn_vecNormSq_of_memVectorL2On hf
  have hηNint : IntegrableOn (fun x => η.toFun x * vecNormSq (f x)) U :=
    hNint.bdd_mul (c := 1) η.smooth.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (η.nonneg x)]; exact η.le_one x)
  have hNle : ∫ x in U, η.toFun x * vecNormSq (f x) ≤ ∫ x in V, vecEuclideanNorm (f x) ^ 2 := by
    simp_rw [vecEuclideanNorm_sq]
    calc ∫ x in U, η.toFun x * vecNormSq (f x)
        = ∫ x in V, η.toFun x * vecNormSq (f x) := by
          refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hV ?_
          intro x hx
          rw [η.eq_zero_of_not_mem_outer hx.2, zero_mul]
      _ ≤ ∫ x in V, vecNormSq (f x) :=
          setIntegral_mono_on (hηNint.mono_set hV) (hNint.mono_set hV) hVmeas fun x _ =>
            mul_le_of_le_one_left (vecNormSq_nonneg (f x)) (η.le_one x)
  -- identification of the normalized norms
  have hWr2 : Wr ^ 2 = (integralAverage V (fun x => (wf x ^ 2) ^ ((d : ℝ) / ((d : ℝ) + 1)))) ^
      (((d : ℝ) + 1) / (d : ℝ)) := by
    have h1 : Wr = (∫ x, ‖wf x‖ ^ q ∂μ) ^ (1 / q) := toReal_eLpNorm_eq_integral_rpow hqpos hwfq
    have h2 : integralAverage V (fun x => (wf x ^ 2) ^ ((d : ℝ) / ((d : ℝ) + 1))) =
        ∫ x, ‖wf x‖ ^ q ∂μ := by
      rw [← integral_normalizedVolumeOn_eq_integralAverage]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      have hw0 : 0 ≤ wf x := Real.sqrt_nonneg _
      show (wf x ^ 2) ^ ((d : ℝ) / ((d : ℝ) + 1)) = ‖wf x‖ ^ q
      rw [Real.norm_of_nonneg hw0, ← Real.rpow_natCast, ← Real.rpow_mul hw0]
      congr 1
      simp only [hqdef]
      push_cast
      field_simp
    have hA0 : 0 ≤ ∫ x, ‖wf x‖ ^ q ∂μ :=
      integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
    rw [h2, h1, ← Real.rpow_natCast, ← Real.rpow_mul hA0]
    congr 1
    simp only [hqdef]
    push_cast
    field_simp
  have hFr2 : (volume V).toReal * Fr ^ 2 = ∫ x in V, vecEuclideanNorm (f x) ^ 2 := by
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    have hfV' : MemLp (fun x => vecEuclideanNorm (f x)) (ENNReal.ofReal 2) μ := by
      rw [← h2]; exact hfV
    have h1 : Fr = (∫ x, ‖vecEuclideanNorm (f x)‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
      rw [hFr, h2]
      exact toReal_eLpNorm_eq_integral_rpow (by norm_num) hfV'
    have hA0 : 0 ≤ ∫ x, ‖vecEuclideanNorm (f x)‖ ^ (2 : ℝ) ∂μ :=
      integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
    have h3 : Fr ^ 2 = ∫ x, vecEuclideanNorm (f x) ^ 2 ∂μ := by
      rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul hA0]
      norm_num
    rw [h3, integral_normalizedVolumeOn_eq_integralAverage, integralAverage,
      ← mul_assoc, mul_inv_cancel₀ hVrealpos.ne', one_mul]
  have hI1 : ∫ x in Q, wf x ^ 2 ≤ 2 * |I2| +
      ∫ x in U, η.toFun x * vecNormSq (f x) := hQle.trans hid
  have hfinal := interior_arith (d := d) (S := S) (r := r) (s := Real.sqrt Λ) (Wr := Wr)
    (Fr := Fr) (Vol := (volume V).toReal) (Qv := (volume Q).toReal)
    (I1 := ∫ x in Q, wf x ^ 2) (I2 := I2)
    (Hη := ∫ x in U, η.toFun x * vecNormSq (f x))
    (H := ∫ x in V, vecEuclideanNorm (f x) ^ 2)
    hS hr hs1 ENNReal.toReal_nonneg hVreal hFr2.symm hI1 hNle hI2'
  rw [hWr2] at hfinal
  exact hfinal


/-- **Interior reverse Hölder inequality** (Lemma 4.5 (i)), on the unit ball.

The constant `C0 ≥ 1` depends only on `d` (through the constant of the convex
Sobolev--Poincaré hypothesis) and is chosen before `Λ`, `a`, `u`, `f` and the cube. With
`w = (∇u · a∇u)^{1/2}`, `θ = d/(d+1)` and `h = |f|²` the conclusion reads
`∫_Q w² ≤ C0 Λ^{1/2} |Q| (avg_{2Q} w^{2θ})^{1/θ} + C0 ∫_{2Q} h`. -/
theorem rh_interior (d : ℕ) (hd : 2 ≤ d) (hSP : ConvexSobolevPoincareHyp d) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧
      ∀ (Λ : ℝ) (a : CoeffField d),
      IsEllipticFieldOn 1 Λ (euclideanBall (0 : Vec d) 1) a →
      ∀ (f : Vec d → Vec d), MemVectorL2On (euclideanBall (0 : Vec d) 1) f →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) f →
      ∀ (z : Vec d) (r : ℝ), 0 < r →
        centeredAxisCube z (2 * r) ⊆ euclideanBall (0 : Vec d) 1 →
          ∫ x in centeredAxisCube z r,
              Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x))) ^ 2 ≤
            (C0 * Real.sqrt Λ) * (volume (centeredAxisCube z r)).toReal *
                (integralAverage (centeredAxisCube z (2 * r))
                  (fun x => (Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x))) ^ 2) ^
                    ((d : ℝ) / ((d : ℝ) + 1)))) ^ (((d : ℝ) + 1) / (d : ℝ)) +
              C0 * ∫ x in centeredAxisCube z (2 * r), vecEuclideanNorm (f x) ^ 2 := by
  obtain ⟨S, hS, hcube⟩ := cube_sobolevPoincare d hd hSP
  refine ⟨interiorConst d S, ?_, ?_⟩
  · unfold interiorConst
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have h2 : (0 : ℝ) ≤ 384 * d * S * 2 ^ d := by positivity
    have h3 : (0 : ℝ) ≤ 128 * d * S := by positivity
    linarith
  · intro Λ a hEll f hf u hsol z r hr hsub
    have hΛ : 1 ≤ Λ := (hEll.elliptic (center_mem_euclideanBall (0 : Vec d) one_pos)).lam_le_Lam
    exact interior_core hd hS hcube (isOpenBoundedConvexDomain_euclideanBall 0 one_pos) hEll hΛ
      u f hf hsol z hr hsub

end PDE.MeyersRH
