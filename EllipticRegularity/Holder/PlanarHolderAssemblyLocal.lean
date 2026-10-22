module

public import HoleFillingStatements.OscillationHolder
public import EllipticRegularity.Holder.PlanarOscillationExponent
public import PDEFoundation.Geometry.EuclideanBall.Interior
public import PDEFoundation.Measure.AxisBoxVolume

/-! # Local planar Hölder representatives from oscillation decay -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The numerical root radius used for planar Hölder assembly. -/
def planarHolderRootRadius : ℝ := 1 / 64

/-- The closed-cube half-side on which the oscillation lemma returns a
Hölder representative. -/
def planarHolderPatchRadius : ℝ := planarHolderRootRadius / 8

/-- The root square at a center in the half unit ball lies in the unit ball. -/
theorem planarHolderRootCube_subset_unit
    (z : Vec 2) (hz : z ∈ euclideanBall (0 : Vec 2) (1 / 2)) :
    centeredAxisCube z planarHolderRootRadius ⊆
      euclideanBall (0 : Vec 2) 1 := by
  have hzNorm : vecEuclideanNorm (z - (0 : Vec 2)) < 1 / 2 :=
    (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hz
  have hball : euclideanBall z (1 / 8) ⊆
      euclideanBall (0 : Vec 2) 1 := by
    apply euclideanBall_subset_of_center_norm_add_le
      (by norm_num) (by norm_num)
    linarith only [hzNorm]
  have hsqrt : Real.sqrt (2 : ℕ) ≤ 2 := by
    have hsq : Real.sqrt (2 : ℕ) ^ 2 = 2 := by norm_num
    nlinarith [Real.sqrt_nonneg (2 : ℕ)]
  have hrad : 2 * Real.sqrt (2 : ℕ) * planarHolderRootRadius ≤ 1 / 8 := by
    dsimp only [planarHolderRootRadius]
    calc
      2 * Real.sqrt (2 : ℕ) * (1 / 64 : ℝ) ≤
          2 * 2 * (1 / 64 : ℝ) := by gcongr
      _ ≤ 1 / 8 := by norm_num
  exact (centeredAxisCube_subset_euclideanBall
    (by norm_num : 0 < 2) z (by norm_num [planarHolderRootRadius])).trans
      ((euclideanBall_mono
        (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
          (by norm_num : (0 : ℝ) ≤ 1 / 64)) hrad).trans hball)

private theorem radius_le_of_centeredAxisCube_subset
    {x z : Vec 2} {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hsub : centeredAxisCube x r ⊆ centeredAxisCube z R) : r ≤ R := by
  have hvol : volume (centeredAxisCube x r) ≤
      volume (centeredAxisCube z R) := measure_mono hsub
  have hvol' := ENNReal.toReal_mono
    (volume_centeredAxisCube_ne_top z R) hvol
  rw [volume_centeredAxisCube_toReal x hr.le,
    volume_centeredAxisCube_toReal z hR.le] at hvol'
  nlinarith [sq_nonneg (r + R)]

/-- Every cube inside the root square at `z ∈ B₁/₂` has radius at most the
root radius and center in `B₃/₄`. -/
theorem planarHolder_subcube_scale_and_center
    {z x : Vec 2} {r : ℝ}
    (hz : z ∈ euclideanBall (0 : Vec 2) (1 / 2))
    (hr : 0 < r)
    (hsub : centeredAxisCube x r ⊆
      centeredAxisCube z planarHolderRootRadius) :
    r ≤ planarHolderRootRadius ∧
      x ∈ euclideanBall (0 : Vec 2) (3 / 4) := by
  have hR : 0 < planarHolderRootRadius := by norm_num [planarHolderRootRadius]
  have hrle := radius_le_of_centeredAxisCube_subset hr hR hsub
  have hxroot : x ∈ centeredAxisCube z planarHolderRootRadius :=
    hsub (center_mem_centeredAxisCube x hr)
  have hsqrt : Real.sqrt (2 : ℕ) ≤ 2 := by
    have hsq : Real.sqrt (2 : ℕ) ^ 2 = 2 := by norm_num
    nlinarith [Real.sqrt_nonneg (2 : ℕ)]
  have hrad : 2 * Real.sqrt (2 : ℕ) * planarHolderRootRadius ≤ 1 / 8 := by
    dsimp only [planarHolderRootRadius]
    calc
      2 * Real.sqrt (2 : ℕ) * (1 / 64 : ℝ) ≤
          2 * 2 * (1 / 64 : ℝ) := by gcongr
      _ ≤ 1 / 8 := by norm_num
  have hxBall : x ∈ euclideanBall z (1 / 8) :=
    (euclideanBall_mono (by positivity) hrad)
      (centeredAxisCube_subset_euclideanBall (by norm_num : 0 < 2) z hR hxroot)
  have hzNorm : vecEuclideanNorm (z - (0 : Vec 2)) < 1 / 2 :=
    (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hz
  have hball : euclideanBall z (1 / 8) ⊆
      euclideanBall (0 : Vec 2) (3 / 4) := by
    apply euclideanBall_subset_of_center_norm_add_le
      (by norm_num) (by norm_num)
    linarith only [hzNorm]
  exact ⟨hrle, hball hxBall⟩

/-- The oscillation-decay theorem supplies the Hölder representative
on a fixed local closed cube at every center of the half unit ball. -/
theorem exists_planarHolder_local_representative
    {C Lam : ℝ} {a : CoeffField 2}
    {u : H1Function (euclideanBall (0 : Vec 2) 1)}
    (hC : (4 * 687865857 : ℝ) ^ 2 ≤ C)
    (hEll : IsEllipticFieldOn 1 Lam
      (euclideanBall (0 : Vec 2) 1) a)
    (hsol : IsWeakDivergenceFormSolutionOn a
      (euclideanBall (0 : Vec 2) 1) u
      (0 : Vec 2 → ℝ) (0 : Vec 2 → Vec 2))
    (z : Vec 2) (hz : z ∈ euclideanBall (0 : Vec 2) (1 / 2)) :
    ∃ v : Vec 2 → ℝ,
      (∀ᵐ y ∂volumeOn (closedCenteredAxisCube z planarHolderPatchRadius),
        v y = u.toFun y) ∧
      ∀ x ∈ closedCenteredAxisCube z planarHolderPatchRadius,
        ∀ y ∈ closedCenteredAxisCube z planarHolderPatchRadius,
          |v x - v y| ≤
            (2 ^ ((C * Lam) ^ (-(1 / 2 : ℝ))) *
              (131072 * Real.sqrt Lam *
                Real.sqrt (∫ w in euclideanBall (0 : Vec 2) 1,
                  u.toFun w ^ 2))) *
              vecEuclideanNorm (x - y) ^ ((C * Lam) ^ (-(1 / 2 : ℝ))) := by
  let U : Set (Vec 2) := euclideanBall (0 : Vec 2) 1
  let α : ℝ := (C * Lam) ^ (-(1 / 2 : ℝ))
  let K : ℝ := 131072 * Real.sqrt Lam *
    Real.sqrt (∫ w in U, u.toFun w ^ 2)
  have hLam : 1 ≤ Lam := by
    have hA := hEll.elliptic
      (center_mem_euclideanBall (0 : Vec 2) (by norm_num : (0 : ℝ) < 1))
    exact hA.lam_le_Lam
  have hCpos : 0 < C := by nlinarith [hC]
  have hprod : 1 ≤ C * Lam := by nlinarith [hC, hLam]
  have hαpos : 0 < α := Real.rpow_pos_of_pos (by positivity) _
  have hαone : α ≤ 1 := by
    dsimp only [α]
    have h := Real.rpow_le_rpow_of_nonpos
      (by norm_num : (0 : ℝ) < 1) hprod
      (by norm_num : -(1 / 2 : ℝ) ≤ 0)
    simpa using h
  have hK : 0 ≤ K := by positivity
  have hR : 0 < planarHolderRootRadius := by norm_num [planarHolderRootRadius]
  have hroot := planarHolderRootCube_subset_unit z hz
  let : IsFiniteMeasure (volumeOn U) :=
    isFiniteMeasure_volumeOn_euclideanBall _ (by norm_num)
  have huInt : IntegrableOn u.toFun U :=
    MeasureTheory.MemLp.integrable (q := (2 : ℝ≥0∞))
      (by norm_num) u.memL2
  have huRoot : IntegrableOn u.toFun
      (centeredAxisCube z planarHolderRootRadius) :=
    huInt.mono_set hroot
  have hosc : ∀ (x : Vec 2) (r : ℝ), 0 < r →
      centeredAxisCube x r ⊆ centeredAxisCube z planarHolderRootRadius →
      ∃ lo hi : ℝ,
        (∀ᵐ y ∂volumeOn (centeredAxisCube x r),
          u.toFun y ∈ Set.Icc lo hi) ∧
        hi - lo ≤ K * r ^ α := by
    intro x r hr hsub
    obtain ⟨hrle, hx⟩ := planarHolder_subcube_scale_and_center hz hr hsub
    obtain ⟨lo, hi, hrange, hwidth⟩ :=
      planar_essentialOscillationLEOn_decay_with_alpha x hx hEll hsol hC
        hr (by simpa only [planarHolderRootRadius] using hrle)
    refine ⟨lo, hi, hrange, ?_⟩
    convert hwidth using 1
    ring
  have h := exists_holderRepresentative_of_essOsc_decay
    2 z hαpos hαone hK hR u.toFun huRoot hosc
  simpa only [planarHolderPatchRadius, α, K, U, mul_assoc] using h

end

end PDE
