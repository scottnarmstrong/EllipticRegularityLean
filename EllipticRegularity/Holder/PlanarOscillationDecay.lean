module

public import EllipticRegularity.Holder.PlanarOscillation
public import EllipticRegularity.Holder.PlanarOscillationEnergy
public import PDEFoundation.Analysis.DyadicOscillationWeights

/-! # Planar oscillation decay from square energy decay -/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

private theorem dyadic_factor_eq_radius_ratio
    {R : ℝ} (hR : 0 < R) (β : ℝ) (n : ℕ) :
    (2 : ℝ) ^ (-β * (n : ℝ)) =
      (dyadicRadius R n / R) ^ β := by
  have hRn : 0 ≤ dyadicRadius R n := (dyadicRadius_pos hR n).le
  have hRβ : 0 < R ^ β := Real.rpow_pos_of_pos hR _
  have hpow := dyadicRadius_rpow_eq hR β n
  rw [Real.div_rpow hRn hR.le, hpow]
  have hpow2 : ((2 : ℝ) ^ (-β)) ^ n =
      (2 : ℝ) ^ (-β * (n : ℝ)) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hpow2]
  field_simp

/-- Dyadic square energy decay read at every radius `s ≤ 1/64`, with the
literal exponent `β = 1/(687865857 √Λ+1)` and a dimension-only factor `128`.
The root energy bound is explicit and may be supplied by Caccioppoli. -/
theorem coefficientEnergy_centeredAxisCube_two_s_decay
    {Lam E : ℝ} {U : Set (Vec 2)} {a : CoeffField 2}
    {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (x : Vec 2)
    (hroot : centeredAxisCube x (1 / 32) ⊆ U)
    (hEll : IsEllipticFieldOn 1 Lam U a)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u)
    (hE : (∫ z in centeredAxisCube x (1 / 32),
      vecDot (u.grad z) (matVecMul (a z) (u.grad z))) ≤ E)
    {s : ℝ} (hs : 0 < s) (hsmax : s ≤ 1 / 64) :
    (∫ z in centeredAxisCube x (2 * s),
      vecDot (u.grad z) (matVecMul (a z) (u.grad z))) ≤
      128 * s ^
        (holeFillingDyadicExponent (687865857 * Real.sqrt Lam)) * E := by
  let R : ℝ := 1 / 32
  let β : ℝ := holeFillingDyadicExponent (687865857 * Real.sqrt Lam)
  let energy : Vec 2 → ℝ :=
    fun z => vecDot (u.grad z) (matVecMul (a z) (u.grad z))
  have hR : 0 < R := by norm_num [R]
  have htwosR : 2 * s ≤ R := by dsimp [R]; linarith
  obtain ⟨n, hnlow, hnhigh⟩ :=
    exists_dyadicRadius_bracket hR (by positivity : 0 < 2 * s) htwosR
  let t : ℝ := dyadicRadius R n
  have ht : 0 < t := dyadicRadius_pos hR n
  have htR : t ≤ R := dyadicRadius_le hR.le n
  have hts : 2 * s ≤ t := hnhigh
  have ht4s : t < 4 * s := by
    have h := hnlow
    rw [dyadicRadius_succ] at h
    dsimp only [t]
    linarith only [h]
  have hroot' : centeredAxisCube x R ⊆ U := hroot
  have htU : centeredAxisCube x t ⊆ U :=
    (centeredAxisCube_mono x htR).trans hroot'
  have hEint : IntegrableOn energy U :=
    integrableOn_coefficientEnergy_of_isEllipticFieldOn hEll u.gradMemL2
  have hnonneg : 0 ≤ᵐ[volume.restrict (centeredAxisCube x t)] energy := by
    filter_upwards [ae_restrict_mem (isOpen_centeredAxisCube x t).measurableSet]
      with z hz
    have hA := hEll.elliptic (htU hz)
    exact (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      (vecNormSq_nonneg (u.grad z))).trans (hA.coercive (u.grad z))
  have hsmall : centeredAxisCube x (2 * s) ⊆ centeredAxisCube x t :=
    centeredAxisCube_mono x hts
  have hmono : (∫ z in centeredAxisCube x (2 * s), energy z) ≤
      ∫ z in centeredAxisCube x t, energy z :=
    setIntegral_mono_set (hEint.mono_set htU) hnonneg
      (Filter.Eventually.of_forall fun z hz => hsmall hz)
  have hxU : x ∈ U := hroot' (center_mem_centeredAxisCube x hR)
  have hLam : 0 < Lam := (hEll.elliptic hxU).Lam_pos
  have hβ : 0 < β := holeFillingDyadicExponent_pos
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg Lam))
  have hβone : β ≤ 1 := holeFillingDyadicExponent_le_one
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg Lam))
  have hdecay := square_hole_filling_dyadic_decay
    hU x hR hroot' hEll (by norm_num) hLam hsol n
  have hdecay' : (∫ z in centeredAxisCube x t, energy z) ≤
      (2 : ℝ) ^ (-β * (n : ℝ)) *
        (∫ z in centeredAxisCube x R, energy z) := by
    simpa only [t, R, β, energy, dyadicRadius, div_one]
      using hdecay
  have hE0 : 0 ≤ (∫ z in centeredAxisCube x R, energy z) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (isOpen_centeredAxisCube x R).measurableSet]
      with z hz
    have hA := hEll.elliptic (hroot' hz)
    exact (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      (vecNormSq_nonneg (u.grad z))).trans (hA.coercive (u.grad z))
  have hratio : t / R ≤ 128 * s := by
    apply (div_le_iff₀ hR).2
    dsimp only [R]
    nlinarith only [ht4s.le]
  have hscale : (2 : ℝ) ^ (-β * (n : ℝ)) ≤ 128 * s ^ β := by
    rw [dyadic_factor_eq_radius_ratio hR β n]
    calc
      (t / R) ^ β ≤ (128 * s) ^ β :=
        Real.rpow_le_rpow (div_nonneg ht.le hR.le) hratio hβ.le
      _ = (128 : ℝ) ^ β * s ^ β := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 128) hs.le]
      _ ≤ 128 * s ^ β := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hs.le _)
        calc
          (128 : ℝ) ^ β ≤ (128 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hβone
          _ = 128 := by norm_num
  calc
    (∫ z in centeredAxisCube x (2 * s), energy z) ≤
      ∫ z in centeredAxisCube x t, energy z := hmono
    _ ≤ (2 : ℝ) ^ (-β * (n : ℝ)) *
      (∫ z in centeredAxisCube x R, energy z) := hdecay'
    _ ≤ (128 * s ^ β) *
      (∫ z in centeredAxisCube x R, energy z) :=
        mul_le_mul_of_nonneg_right hscale hE0
    _ ≤ (128 * s ^ β) * E := by
      exact mul_le_mul_of_nonneg_left hE
        (mul_nonneg (by norm_num) (Real.rpow_nonneg hs.le _))

end

end PDE

namespace PDE

open MeasureTheory

noncomputable section

/-- The two-dimensional essential oscillation on a square decays with the
sharp ellipticity order of the exponent and a prefactor of order `√Λ`.
The explicit scale range is `0 < s ≤ 1/64`. -/
theorem planar_essentialOscillationLEOn_decay
    {Lam : ℝ} {a : CoeffField 2}
    {u : H1Function (euclideanBall (0 : Vec 2) 1)}
    (x : Vec 2) (hx : x ∈ euclideanBall (0 : Vec 2) (3 / 4))
    (hEll : IsEllipticFieldOn 1 Lam
      (euclideanBall (0 : Vec 2) 1) a)
    (hsol : IsWeakDivergenceFormHarmonicOn a
      (euclideanBall (0 : Vec 2) 1) u)
    {s : ℝ} (hs : 0 < s) (hsmax : s ≤ 1 / 64) :
    HasEssentialOscillationLEOn u.toFun (centeredAxisCube x s)
      (131072 * Real.sqrt Lam *
        s ^ (holeFillingDyadicExponent
          (687865857 * Real.sqrt Lam) / 2) *
        Real.sqrt (∫ z in euclideanBall (0 : Vec 2) 1, (u z) ^ 2)) := by
  let U : Set (Vec 2) := euclideanBall (0 : Vec 2) 1
  let β : ℝ := holeFillingDyadicExponent (687865857 * Real.sqrt Lam)
  let L : ℝ := ∫ z in U, (u z) ^ 2
  let shell : ℝ := squareShellVectorEnergy u.grad x s
  let energy : Vec 2 → ℝ :=
    fun z => vecDot (u.grad z) (matVecMul (a z) (u.grad z))
  have hroot : centeredAxisCube x (1 / 32) ⊆ U :=
    centeredAxisCube_one_thirtysecond_subset_unit x hx
  have htwos : 2 * s ≤ 1 / 32 := by linarith
  have houter : centeredAxisCube x (2 * s) ⊆ U :=
    (centeredAxisCube_mono x htwos).trans hroot
  have hLam : 0 < Lam :=
    (hEll.elliptic (hroot (center_mem_centeredAxisCube x (by norm_num)))).Lam_pos
  have hL : 0 ≤ L := integral_nonneg fun z => sq_nonneg (u z)
  have hshell : 0 ≤ shell := integral_nonneg fun z => vecNormSq_nonneg (u.grad z)
  have hrootE := coefficientEnergy_centeredAxisCube_one_thirtysecond_le
    x hx hEll hsol
  have hdecay := coefficientEnergy_centeredAxisCube_two_s_decay
    (isOpenBoundedConvexDomain_euclideanBall (0 : Vec 2) (by norm_num))
    x hroot hEll hsol hrootE hs hsmax
  have henergyInt : IntegrableOn energy U :=
    integrableOn_coefficientEnergy_of_isEllipticFieldOn hEll u.gradMemL2
  have henergyNonneg :
      0 ≤ᵐ[volume.restrict (centeredAxisCube x (2 * s))] energy := by
    filter_upwards [ae_restrict_mem (isOpen_centeredAxisCube x (2 * s)).measurableSet]
      with z hz
    have hA := hEll.elliptic (houter hz)
    exact (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      (vecNormSq_nonneg (u.grad z))).trans (hA.coercive (u.grad z))
  have hshellSub : dyadicSquareShell x s ⊆ centeredAxisCube x (2 * s) :=
    fun _ hz => hz.1
  have hshellU : dyadicSquareShell x s ⊆ U := hshellSub.trans houter
  have hcoerc := setIntegral_vecNormSq_le_coefficientEnergy_div
    hEll u.gradMemL2 (isOpen_dyadicSquareShell x s).measurableSet
    hshellU (by norm_num : (0 : ℝ) < 1)
  have hshellLe : shell ≤ ∫ z in centeredAxisCube x (2 * s), energy z := by
    calc
      shell ≤ (∫ z in dyadicSquareShell x s, energy z) / 1 := by
        simpa only [shell, squareShellVectorEnergy, energy] using hcoerc
      _ = ∫ z in dyadicSquareShell x s, energy z := by ring
      _ ≤ ∫ z in centeredAxisCube x (2 * s), energy z :=
        setIntegral_mono_set (henergyInt.mono_set houter) henergyNonneg
          (Filter.Eventually.of_forall fun z hz => hshellSub hz)
  have hdecay' : shell ≤ 128 * s ^ β * (262144 * Lam * L) := by
    exact hshellLe.trans (by simpa only [β, L, U, energy] using hdecay)
  have hβ : 0 < β := holeFillingDyadicExponent_pos
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg Lam))
  have hpow : (s ^ (β / 2)) ^ 2 = s ^ β := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    congr 1
    ring
  have hleft : 0 ≤ 16 * Real.sqrt shell :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hright : 0 ≤
      131072 * Real.sqrt Lam * s ^ (β / 2) * Real.sqrt L := by
    positivity
  have hcompare :
      16 * Real.sqrt shell ≤
        131072 * Real.sqrt Lam * s ^ (β / 2) * Real.sqrt L := by
    apply (sq_le_sq₀ hleft hright).mp
    have hshellSq : (16 * Real.sqrt shell) ^ 2 = 256 * shell := by
      rw [mul_pow, Real.sq_sqrt hshell]
      ring
    have hrightSq :
        (131072 * Real.sqrt Lam * s ^ (β / 2) * Real.sqrt L) ^ 2 =
          17179869184 * (Lam * s ^ β * L) := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hLam.le,
        Real.sq_sqrt hL, hpow]
      ring
    rw [hshellSq, hrightSq]
    have hmul := mul_le_mul_of_nonneg_left hdecay' (by norm_num : (0 : ℝ) ≤ 256)
    nlinarith [mul_nonneg (mul_nonneg hLam.le (Real.rpow_nonneg hs.le β)) hL]
  obtain ⟨lo, hi, hrange, hwidth⟩ :=
    essentialOscillationLEOn_centeredAxisCube_of_harmonic
      (isOpenBoundedConvexDomain_euclideanBall (0 : Vec 2) (by norm_num))
      hs houter hEll hsol
  exact ⟨lo, hi, hrange, hwidth.trans (by simpa only [β, L, U, shell] using hcompare)⟩

end

end PDE
