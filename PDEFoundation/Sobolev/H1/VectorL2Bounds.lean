module

public import PDEFoundation.Measure.LpPower
public import PDEFoundation.Measure.NormalizedLp
public import PDEFoundation.Sobolev.H1.Pairing
public import PDEFoundation.Sobolev.H1.GraphPairing

/-!
# Euclidean vector `L²` bounds on restricted domains

These estimates keep the native-vector representative and the exact
Euclidean-valued `L²` norm in sync.  The Hilbert quotient is used only to
obtain factor-free Cauchy--Schwarz and triangle inequalities.
-/

@[expose] public section

open scoped ENNReal RealInnerProductSpace

namespace PDE

open MeasureTheory

variable {d : ℕ} {U : Set (Vec d)}

/-- The native squared Euclidean energy is exactly the squared norm of its
canonical Hilbert-valued `L²` class. -/
theorem setIntegral_vecNormSq_eq_sq_norm_toHilbertVectorLp
    {F : Vec d → Vec d} (hF : MemVectorL2On U F) :
    (∫ x in U, vecNormSq (F x)) =
      ‖hF.toHilbertVectorLp‖ ^ 2 := by
  have hpair := setIntegral_vecDot_eq_inner_of_ae_eq
    hF.toHilbertVectorLp hF.toHilbertVectorLp F F
    hF.coeFn_toHilbertVectorLp hF.coeFn_toHilbertVectorLp
  simpa only [vecNormSq] using
    hpair.trans (real_inner_self_eq_norm_sq hF.toHilbertVectorLp)

/-- The guarded real Euclidean field `L²` norm is exactly the square root of
the native squared energy. -/
theorem euclideanFieldLpNormOn_two_eq_sqrt_setIntegral_vecNormSq
    {F : Vec d → Vec d} (hF : MemVectorL2On U F) :
    euclideanFieldLpNormOn U (2 : ℝ≥0∞) F
        hF.memLp_vecEuclideanNorm =
      Real.sqrt (∫ x in U, vecNormSq (F x)) := by
  have hPower :
      euclideanFieldLpNormOn U (2 : ℝ≥0∞) F
          hF.memLp_vecEuclideanNorm ^ 2 =
        ∫ x in U, vecNormSq (F x) := by
    rw [euclideanFieldLpNormOn, lpNormOn_eq_toReal]
    simpa only [vecEuclideanNorm_sq] using!
      toReal_eLpNorm_two_sq_eq_integral_sq hF.memLp_vecEuclideanNorm
  have hNormNonneg :
      0 ≤ euclideanFieldLpNormOn U (2 : ℝ≥0∞) F
          hF.memLp_vecEuclideanNorm := by
    rw [euclideanFieldLpNormOn, lpNormOn_eq_toReal]
    exact ENNReal.toReal_nonneg
  exact ((Real.sqrt_eq_iff_eq_sq
    (integral_nonneg fun x => vecNormSq_nonneg (F x)) hNormNonneg).2
      hPower.symm).symm

/-- Cauchy--Schwarz for the integral of the native Euclidean dot product,
with the exact raw energy square roots and no dimension loss. -/
theorem abs_setIntegral_vecDot_le_sqrt_setIntegral_vecNormSq_mul
    {F G : Vec d → Vec d}
    (hF : MemVectorL2On U F) (hG : MemVectorL2On U G) :
    |∫ x in U, vecDot (F x) (G x)| ≤
      Real.sqrt (∫ x in U, vecNormSq (F x)) *
        Real.sqrt (∫ x in U, vecNormSq (G x)) := by
  have hpair := setIntegral_vecDot_eq_inner_of_ae_eq
    hF.toHilbertVectorLp hG.toHilbertVectorLp F G
    hF.coeFn_toHilbertVectorLp hG.coeFn_toHilbertVectorLp
  have hEnergyF := setIntegral_vecNormSq_eq_sq_norm_toHilbertVectorLp hF
  have hEnergyG := setIntegral_vecNormSq_eq_sq_norm_toHilbertVectorLp hG
  have hRootF :
      Real.sqrt (∫ x in U, vecNormSq (F x)) =
        ‖hF.toHilbertVectorLp‖ :=
    (Real.sqrt_eq_iff_eq_sq
      (integral_nonneg fun x => vecNormSq_nonneg (F x))
      (norm_nonneg _)).2 hEnergyF
  have hRootG :
      Real.sqrt (∫ x in U, vecNormSq (G x)) =
        ‖hG.toHilbertVectorLp‖ :=
    (Real.sqrt_eq_iff_eq_sq
      (integral_nonneg fun x => vecNormSq_nonneg (G x))
      (norm_nonneg _)).2 hEnergyG
  rw [hpair, hRootF, hRootG]
  exact abs_real_inner_le_norm
    hF.toHilbertVectorLp hG.toHilbertVectorLp

/-- The same mixed integral bound expressed with guarded Euclidean field
`L²` norms. -/
theorem abs_setIntegral_vecDot_le_euclideanFieldLpNormOn_mul
    {F G : Vec d → Vec d}
    (hF : MemVectorL2On U F) (hG : MemVectorL2On U G) :
    |∫ x in U, vecDot (F x) (G x)| ≤
      euclideanFieldLpNormOn U (2 : ℝ≥0∞) F
        hF.memLp_vecEuclideanNorm *
      euclideanFieldLpNormOn U (2 : ℝ≥0∞) G
        hG.memLp_vecEuclideanNorm := by
  calc
    |∫ x in U, vecDot (F x) (G x)| ≤
        Real.sqrt (∫ x in U, vecNormSq (F x)) *
          Real.sqrt (∫ x in U, vecNormSq (G x)) :=
      abs_setIntegral_vecDot_le_sqrt_setIntegral_vecNormSq_mul hF hG
    _ = euclideanFieldLpNormOn U (2 : ℝ≥0∞) F
          hF.memLp_vecEuclideanNorm *
        euclideanFieldLpNormOn U (2 : ℝ≥0∞) G
          hG.memLp_vecEuclideanNorm := by
      rw [← euclideanFieldLpNormOn_two_eq_sqrt_setIntegral_vecNormSq hF,
        ← euclideanFieldLpNormOn_two_eq_sqrt_setIntegral_vecNormSq hG]

/-- Pointwise Euclidean norm domination gives the corresponding sharp
domination of raw `L²` energy square roots. -/
theorem sqrt_setIntegral_vecNormSq_le_mul_of_ae_vecEuclideanNorm_le
    {F G : Vec d → Vec d} {C : ℝ}
    (hF : MemVectorL2On U F) (hG : MemVectorL2On U G)
    (hC : 0 ≤ C)
    (hbound : ∀ᵐ x ∂(volumeOn U),
      vecEuclideanNorm (F x) ≤ C * vecEuclideanNorm (G x)) :
    Real.sqrt (∫ x in U, vecNormSq (F x)) ≤
      C * Real.sqrt (∫ x in U, vecNormSq (G x)) := by
  have hboundSq : ∀ᵐ x ∂(volumeOn U),
      vecNormSq (F x) ≤ C ^ 2 * vecNormSq (G x) := by
    filter_upwards [hbound] with x hx
    rw [← vecEuclideanNorm_sq, ← vecEuclideanNorm_sq]
    calc
      vecEuclideanNorm (F x) ^ 2 ≤
          (C * vecEuclideanNorm (G x)) ^ 2 :=
        (sq_le_sq₀ (vecEuclideanNorm_nonneg _)
          (mul_nonneg hC (vecEuclideanNorm_nonneg _))).2 hx
      _ = C ^ 2 * vecEuclideanNorm (G x) ^ 2 := by ring
  have henergy := integral_mono_ae
    (integrableOn_vecNormSq_of_memVectorL2On hF)
    ((integrableOn_vecNormSq_of_memVectorL2On hG).const_mul (C ^ 2))
    hboundSq
  calc
    Real.sqrt (∫ x in U, vecNormSq (F x)) ≤
        Real.sqrt (C ^ 2 * ∫ x in U, vecNormSq (G x)) := by
      apply Real.sqrt_le_sqrt
      simpa only [integral_const_mul] using henergy
    _ = C * Real.sqrt (∫ x in U, vecNormSq (G x)) := by
      rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hC]

/-- A pairing against a field with pointwise Euclidean norm at most `C` times
another field is bounded by `C` times the product of their raw energy square
roots. -/
theorem abs_setIntegral_vecDot_le_mul_of_ae_vecEuclideanNorm_le
    {F H G : Vec d → Vec d} {C : ℝ}
    (hF : MemVectorL2On U F) (hH : MemVectorL2On U H)
    (hG : MemVectorL2On U G) (hC : 0 ≤ C)
    (hbound : ∀ᵐ x ∂(volumeOn U),
      vecEuclideanNorm (H x) ≤ C * vecEuclideanNorm (F x)) :
    |∫ x in U, vecDot (G x) (H x)| ≤
      C * Real.sqrt (∫ x in U, vecNormSq (G x)) *
        Real.sqrt (∫ x in U, vecNormSq (F x)) := by
  calc
    |∫ x in U, vecDot (G x) (H x)| ≤
        Real.sqrt (∫ x in U, vecNormSq (G x)) *
          Real.sqrt (∫ x in U, vecNormSq (H x)) :=
      abs_setIntegral_vecDot_le_sqrt_setIntegral_vecNormSq_mul hG hH
    _ ≤ Real.sqrt (∫ x in U, vecNormSq (G x)) *
          (C * Real.sqrt (∫ x in U, vecNormSq (F x))) :=
      mul_le_mul_of_nonneg_left
        (sqrt_setIntegral_vecNormSq_le_mul_of_ae_vecEuclideanNorm_le
          hH hF hC hbound)
        (Real.sqrt_nonneg _)
    _ = C * Real.sqrt (∫ x in U, vecNormSq (G x)) *
          Real.sqrt (∫ x in U, vecNormSq (F x)) := by ring

/-- The raw Euclidean `L²` energy square root satisfies the triangle
inequality on native representatives. -/
theorem sqrt_setIntegral_vecNormSq_add_le
    {F G : Vec d → Vec d}
    (hF : MemVectorL2On U F) (hG : MemVectorL2On U G) :
    Real.sqrt (∫ x in U, vecNormSq (F x + G x)) ≤
      Real.sqrt (∫ x in U, vecNormSq (F x)) +
        Real.sqrt (∫ x in U, vecNormSq (G x)) := by
  let hsum : MemVectorL2On U (fun x => F x + G x) := by
    intro i
    simpa only [Pi.add_apply] using! (hF i).add (hG i)
  let Hsum := hsum.toHilbertVectorLp
  let HF := hF.toHilbertVectorLp
  let HG := hG.toHilbertVectorLp
  have hclass : Hsum = HF + HG := by
    apply Lp.ext
    filter_upwards [hsum.coeFn_toHilbertVectorLp,
      Lp.coeFn_add HF HG, hF.coeFn_toHilbertVectorLp,
      hG.coeFn_toHilbertVectorLp] with x hsumx hadd hFx hGx
    dsimp [Hsum, HF, HG] at *
    rw [hsumx, hadd, hFx, hGx]
    rfl
  rw [setIntegral_vecNormSq_eq_sq_norm_toHilbertVectorLp hsum,
    setIntegral_vecNormSq_eq_sq_norm_toHilbertVectorLp hF,
    setIntegral_vecNormSq_eq_sq_norm_toHilbertVectorLp hG]
  change Real.sqrt (‖Hsum‖ ^ 2) ≤
    Real.sqrt (‖HF‖ ^ 2) + Real.sqrt (‖HG‖ ^ 2)
  rw [hclass]
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]
  exact norm_add_le _ _

end PDE
