module

public import PDEFoundation.PDE.LocalLaplacianEstimate
public import PDEFoundation.PDE.PerturbativeLaplacianForcing
public import PDEFoundation.PDE.PerturbativeForcingLpBound
public import PDEFoundation.Measure.InteriorBoundedFieldLp

@[expose] public section

namespace PDE

open MeasureTheory
open scoped _root_.ENNReal Topology

/-- The actual perturbative equation gives the radius recurrence, with the
local norm finiteness derived from an explicit interior essential bound. -/
theorem exists_perturbativeLaplacian_radiusRecurrence_constants
    (d : ℕ) (hd : 0 < d) :
    ∃ A K : ℝ, 0 ≤ A ∧ 0 ≤ K ∧
    ∀ (p delta M : ℝ), 4 ≤ p → 0 ≤ delta → 0 ≤ M →
    ∀ (a : CoeffField d) (F : Vec d → Vec d)
      (u : H1Function (euclideanBall (0 : Vec d) 1)),
    (∀ i j, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec d) 1))) →
    (∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
      IsMatrixPerturbationLE delta (a x) (1 : Mat d)) →
    (∀ i, AEStronglyMeasurable (fun x => F x i)
      (volumeOn (euclideanBall (0 : Vec d) 1))) →
    MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
      (volumeOn (euclideanBall (0 : Vec d) 1)) →
    IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u 0 F →
    (∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) (3 / 4)),
      vecEuclideanNorm (u.grad x) ≤ M) →
    ∀ s t, 1 / 2 ≤ s → s < t → t < 3 / 4 →
    (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
      ((volume (euclideanBall (0 : Vec d) 1))⁻¹ •
        volumeOn (euclideanBall (0 : Vec d) s))).toReal ≤
    A * (t - s) ^ (-(d : ℝ) / 2) *
      Real.sqrt (integralAverage (euclideanBall (0 : Vec d) 1)
        (fun x => vecNormSq (u.grad x))) +
    K * p * (eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
      (normalizedVolumeOn (euclideanBall (0 : Vec d) 1))).toReal +
    (K * p * delta) *
      (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
        ((volume (euclideanBall (0 : Vec d) 1))⁻¹ •
          volumeOn (euclideanBall (0 : Vec d) t))).toReal := by
  obtain ⟨A, K, hA, hK, hlocal⟩ := exists_localLaplacianLp_constants d hd
  refine ⟨A, K, hA, hK, ?_⟩
  intro p delta M hp hdelta hM a F u ha hclose hFcoord hFp hsol hbound
    s t hs hst ht
  let B1 := euclideanBall (0 : Vec d) 1
  let Bt := euclideanBall (0 : Vec d) t
  let Bs := euclideanBall (0 : Vec d) s
  let c := (volume B1)⁻¹
  let G : Vec d → Vec d := fun x => F x + matVecMul (a x - 1) (u.grad x)
  have hp1 : 1 ≤ p := by linarith
  have hpe : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) (hs.trans hst.le)
  have hsub : Bt ⊆ B1 := euclideanBall_mono ht0.le (by linarith)
  have htmem := (exists_uniform_interior_eLpNorm_of_ae_bound u hp1 hM hbound
    t (hs.trans hst.le) ht).1
  have hF2 : MemVectorL2On B1 F :=
    memVectorL2On_euclideanBall_of_memLp_vecEuclideanNorm (by linarith)
      (0 : Vec d) (by norm_num) (Set.Subset.refl _) hFp hFcoord
  have hsolG := hsol.toLaplacian_of_isMatrixPerturbationLE ha hclose hF2
  let ut : H1Function Bt := u.restrict (isOpen_euclideanBall _ _) hsub
  have hat : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn Bt) :=
    fun i j => (ha i j).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hcloset : ∀ᵐ x ∂volumeOn Bt, IsMatrixPerturbationLE delta (a x) 1 :=
    ae_mono (Measure.restrict_mono hsub le_rfl) hclose
  have hFcoordt : ∀ i, AEStronglyMeasurable (fun x => F x i) (volumeOn Bt) :=
    fun i => (hFcoord i).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hgcoordt : ∀ i, AEStronglyMeasurable (fun x => u.grad x i) (volumeOn Bt) :=
    fun i => (ut.gradMemL2 i).aestronglyMeasurable
  have hGcoord : ∀ i, AEStronglyMeasurable (fun x => G x i) (volumeOn Bt) :=
    fun i => (hFcoordt i).add (aestronglyMeasurable_perturbationFlux_coord
      hat hgcoordt i)
  have hGmeas := aestronglyMeasurable_vecEuclideanNorm_of_coord hGcoord
  have hFt := hFp.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hGnorm := eLpNorm_perturbativeForcing_le hdelta hpe hat hcloset
    hFcoordt hgcoordt
  have hGp : MemLp (fun x => vecEuclideanNorm (G x)) (ENNReal.ofReal p)
      (volumeOn Bt) := (hGnorm.trans_lt (ENNReal.add_lt_top.mpr
        ⟨hFt.eLpNorm_lt_top, ENNReal.mul_lt_top ENNReal.ofReal_lt_top htmem.eLpNorm_lt_top⟩))
  have hsolGt : IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat d)) Bt ut 0 G :=
    hsolG.restrict (isOpen_euclideanBall _ _) (isOpen_euclideanBall _ _) hsub
  have hlocalt := (hlocal p hp s t (by linarith) hst (by linarith)
    ut G hGcoord hGp hsolGt).2
  have hcTop : c ≠ ⊤ := ENNReal.inv_ne_top.mpr
    (volume_euclideanBall_pos (0 : Vec d) (by norm_num)).ne'
  have hFfixed := hFp.smul_measure hcTop
  have htFixed := htmem.smul_measure hcTop
  have hGFixed := hGp.smul_measure hcTop
  have hGnormFixed := eLpNorm_perturbativeForcing_le
    (μ := c • volumeOn Bt) hdelta hpe
    (fun i j => (hat i j).smul_measure c)
    (Measure.ae_smul_measure hcloset c)
    (fun i => (hFcoordt i).smul_measure c) (fun i => (hgcoordt i).smul_measure c)
  have hFmono : eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
      (c • volumeOn Bt) ≤
      eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
        (normalizedVolumeOn B1) := by
    have hc0 : c ≠ 0 := ENNReal.inv_ne_zero.mpr
      (volume_euclideanBall_ne_top (0 : Vec d) (by norm_num))
    rw [normalizedVolumeOn, eLpNorm_smul_measure_of_ne_zero hc0,
      eLpNorm_smul_measure_of_ne_zero hc0]
    exact mul_le_mul_right
      (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)) _
  have hGbound := hGnormFixed.trans
    (add_le_add hFmono le_rfl)
  have henergy : Real.sqrt ((∫ x in Bt, vecNormSq (u.grad x)) /
      (volume B1).toReal) ≤ Real.sqrt (integralAverage B1
        (fun x => vecNormSq (u.grad x))) := by
    rw [integralAverage]
    apply Real.sqrt_le_sqrt
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left
        (setIntegral_vecNormSq_mono_set hsub u.gradMemL2)
        (inv_nonneg.mpr (ENNReal.toReal_nonneg : 0 ≤ (volume B1).toReal))
  have hlocalReal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGFixed.eLpNorm_ne_top⟩) hlocalt
  have hGReal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hFfixed.eLpNorm_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top htFixed.eLpNorm_ne_top⟩) hGbound
  have henergyCoeff : 0 ≤ A * (t - s) ^ (-(d : ℝ) / 2) := by
    exact mul_nonneg hA (Real.rpow_nonneg (sub_pos.mpr hst).le _)
  have hKp : 0 ≤ K * p := mul_nonneg hK (by linarith)
  simp only [ENNReal.toReal_add ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGFixed.eLpNorm_ne_top),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg henergyCoeff
      (Real.sqrt_nonneg _)), ENNReal.toReal_ofReal hKp,
    ut, H1Function.restrict_grad] at hlocalReal
  simp only [ENNReal.toReal_add hFfixed.eLpNorm_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top htFixed.eLpNorm_ne_top),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hdelta] at hGReal
  dsimp only [c, B1, Bt, Bs, G] at hlocalReal hGReal henergy
  simp only [normalizedVolumeOn] at ⊢
  nlinarith only [hlocalReal, mul_le_mul_of_nonneg_left henergy henergyCoeff,
    mul_le_mul_of_nonneg_left hGReal hKp]

end PDE
