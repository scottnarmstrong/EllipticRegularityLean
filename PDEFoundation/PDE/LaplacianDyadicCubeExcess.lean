module

public import PDEFoundation.Geometry.BoxCenterDisplacement
public import PDEFoundation.Measure.BoxCircumscribedBallVolume
public import PDEFoundation.PDE.HarmonicComparisonMaximal
public import PDEFoundation.Sobolev.H1.VectorMeanSetCongruence

/-! # Laplacian excess estimate on a dyadic cube -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Harmonic comparison on the circumscribed balls of a dyadic descendant,
converted to the literal half-open cube with dimension-only volume factors. -/
theorem ofReal_centeredVectorMeanL2_dyadicDescendant_le
    {d : ℕ} (I : Box (Fin d)) (L : ℝ) (hd : 0 < d)
    (hwidth : ∀ i, I.upper i - I.lower i = L)
    (u : H1Function (euclideanBall (boxCenter I)
      (2 * (Real.sqrt d * L / 2))))
    (F : Vec d → Vec d)
    (hF : MemVectorL2On (euclideanBall (boxCenter I)
      (2 * (Real.sqrt d * L / 2))) F)
    (hsol : IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat d))
      (euclideanBall (boxCenter I) (2 * (Real.sqrt d * L / 2))) u 0 F)
    (q : List (Set (Fin d))) {x : Vec d}
    (hx : x ∈ Box.Ioo (dyadicDescendant I q)) :
    ENNReal.ofReal
        (centeredVectorMeanL2 (dyadicDescendant I q : Set (Vec d)) u.grad) ≤
      ENNReal.ofReal
          ((Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
              (Real.sqrt d / 2) ^ d) * Real.sqrt ((2 : ℝ) ^ d) /
              (2 : ℝ) ^ q.length) *
            Real.sqrt (integralAverage
              (euclideanBall (boxCenter I) (2 * (Real.sqrt d * L / 2)))
              (fun y => vecNormSq (u.grad y)))) +
        ENNReal.ofReal
          (Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
              (Real.sqrt d / 2) ^ d) *
            (((d : ℝ) + 2) / 2 * (1 + 2 / (d : ℝ)) ^ ((d : ℝ) / 2))) *
          quadraticBallMaximal F x := by
  let J := dyadicDescendant I q
  let r0 := Real.sqrt d * L / 2
  let r := Real.sqrt d * (L / (2 : ℝ) ^ q.length) / 2
  let D := Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
    (Real.sqrt d / 2) ^ d)
  let κ := ((d : ℝ) + 2) / 2 *
    (1 + 2 / (d : ℝ)) ^ ((d : ℝ) / 2)
  let B0 := euclideanBall (boxCenter I) (2 * r0)
  let BJ := euclideanBall (boxCenter J) r0
  let Bj := euclideanBall (boxCenter J) r
  let Q := (J : Set (Vec d))
  let Qo := Box.Ioo J
  let i0 : Fin d := ⟨0, hd⟩
  have hL : 0 < L := by
    rw [← hwidth i0]
    exact sub_pos.mpr (I.lower_lt_upper i0)
  have hr0 : 0 < r0 := by
    dsimp only [r0]
    have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
    positivity
  have hr : 0 < r := by
    dsimp only [r]
    have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
    positivity
  have hJB0 : BJ ⊆ B0 := by
    simpa only [BJ, B0, J, r0] using
      euclideanBall_boxCenter_dyadicDescendant_subset_two_mul I L hd hwidth q
  have hQoBj : Qo ⊆ Bj := by
    dsimp only [Qo, Bj, J, r]
    apply Box.Ioo_subset_euclideanBall_boxCenter J
      (L / (2 : ℝ) ^ q.length) hd
    exact upper_sub_lower_dyadicDescendant_of_commonWidth I L hwidth q
  have hxBj : x ∈ Bj := hQoBj hx
  have hgradBJ : MemVectorL2On BJ u.grad := fun i =>
    memLpOn_mono hJB0 (u.gradMemL2 i)
  have hFBJ : MemVectorL2On BJ F := fun i => memLpOn_mono hJB0 (hF i)
  have hrR : r ≤ r0 := by
    dsimp only [r, r0]
    have hp : 1 ≤ (2 : ℝ) ^ q.length := one_le_pow₀ (by norm_num)
    have hscale : L / (2 : ℝ) ^ q.length ≤ L := div_le_self hL.le hp
    gcongr
  have hBjBJ : Bj ⊆ BJ := euclideanBall_mono hr.le hrR
  have hgradBj : MemVectorL2On Bj u.grad := fun i =>
    memLpOn_mono hBjBJ (hgradBJ i)
  let uJ : H1Function BJ := u.restrict (isOpen_euclideanBall _ _) hJB0
  have hsolJ : IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat d)) BJ uJ 0 F :=
    hsol.restrict (isOpen_euclideanBall _ _) (isOpen_euclideanBall _ _) hJB0
  have hcomp : ENNReal.ofReal (centeredVectorMeanL2 Bj u.grad) ≤
      ENNReal.ofReal ((r / r0) * centeredVectorMeanL2 BJ u.grad) +
        ENNReal.ofReal κ * quadraticBallMaximal F x := by
    simpa only [uJ, H1Function.restrict_grad, κ] using
      centeredVectorMeanL2_weakLaplacian_retained_excess
        hd hr0 uJ hFBJ hsolJ hr hrR hxBj
  have hratioCube : Real.sqrt ((volume Bj).toReal / (volume Qo).toReal) = D := by
    rw [← (Box.coe_ae_eq_Ioo J).measure_eq]
    simpa only [Bj, J, r, D] using
      sqrt_volume_euclideanBall_boxCenter_div_box_of_commonWidth
        J (L / (2 : ℝ) ^ q.length) hd
          (upper_sub_lower_dyadicDescendant_of_commonWidth I L hwidth q)
  have hcubeReal : centeredVectorMeanL2 Q u.grad ≤
      D * centeredVectorMeanL2 Bj u.grad := by
    rw [centeredVectorMeanL2_congr_set_ae (Box.coe_ae_eq_Ioo J) u.grad]
    have hmono := centeredVectorMeanL2_mono_set hQoBj hgradBj
      (volume_box_Ioo_pos J) (volume_box_Ioo_lt_top J)
      (volume_euclideanBall_pos _ hr)
      (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ hr.le))
    simpa only [hratioCube] using hmono
  have hratioOuter : Real.sqrt ((volume B0).toReal / (volume BJ).toReal) =
      Real.sqrt ((2 : ℝ) ^ d) := by
    have hvol := volume_euclideanBall_toReal_div_eq_div_pow
      (boxCenter I) (boxCenter J) hr0 (by positivity : 0 < 2 * r0)
    dsimp only [B0, BJ]
    rw [hvol]
    congr 1
    have hr0ne := hr0.ne'
    field_simp
  have houterCentered : centeredVectorMeanL2 BJ u.grad ≤
      Real.sqrt ((2 : ℝ) ^ d) *
        Real.sqrt (integralAverage B0 (fun y => vecNormSq (u.grad y))) := by
    have hmono := centeredVectorMeanL2_mono_set hJB0 u.gradMemL2
      (volume_euclideanBall_pos _ hr0)
      (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ hr0.le))
      (volume_euclideanBall_pos _ (by positivity : 0 < 2 * r0))
      (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ (by positivity)))
    have hroot := centeredVectorMeanL2_le_sqrt_integralAverage_vecNormSq
      u.gradMemL2 (volume_euclideanBall_pos _ (by positivity : 0 < 2 * r0))
      (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ (by positivity)))
    rw [hratioOuter] at hmono
    exact hmono.trans (mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _))
  have hratioRadius : r / r0 = 1 / (2 : ℝ) ^ q.length := by
    exact boxCenter_circumscribedRadius_dyadicDescendant_div I L hd hwidth q
  have hbase : (r / r0) * centeredVectorMeanL2 BJ u.grad ≤
      (Real.sqrt ((2 : ℝ) ^ d) / (2 : ℝ) ^ q.length) *
        Real.sqrt (integralAverage B0 (fun y => vecNormSq (u.grad y))) := by
    rw [hratioRadius]
    calc
      (1 / (2 : ℝ) ^ q.length) * centeredVectorMeanL2 BJ u.grad ≤
          (1 / (2 : ℝ) ^ q.length) *
            (Real.sqrt ((2 : ℝ) ^ d) *
              Real.sqrt (integralAverage B0 (fun y => vecNormSq (u.grad y)))) :=
        mul_le_mul_of_nonneg_left houterCentered (by positivity)
      _ = _ := by ring
  have hcomp' : ENNReal.ofReal (centeredVectorMeanL2 Bj u.grad) ≤
      ENNReal.ofReal ((Real.sqrt ((2 : ℝ) ^ d) / (2 : ℝ) ^ q.length) *
        Real.sqrt (integralAverage B0 (fun y => vecNormSq (u.grad y)))) +
        ENNReal.ofReal κ * quadraticBallMaximal F x :=
    hcomp.trans (add_le_add (ENNReal.ofReal_le_ofReal hbase) le_rfl)
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hcubeENN := ENNReal.ofReal_le_ofReal hcubeReal
  rw [ENNReal.ofReal_mul hD] at hcubeENN
  calc
    ENNReal.ofReal (centeredVectorMeanL2 Q u.grad) ≤
        ENNReal.ofReal D * ENNReal.ofReal (centeredVectorMeanL2 Bj u.grad) := hcubeENN
    _ ≤ ENNReal.ofReal D *
        (ENNReal.ofReal ((Real.sqrt ((2 : ℝ) ^ d) / (2 : ℝ) ^ q.length) *
          Real.sqrt (integralAverage B0 (fun y => vecNormSq (u.grad y)))) +
          ENNReal.ofReal κ * quadraticBallMaximal F x) :=
      mul_le_mul_right hcomp' _
    _ = ENNReal.ofReal
          ((D * Real.sqrt ((2 : ℝ) ^ d) / (2 : ℝ) ^ q.length) *
            Real.sqrt (integralAverage B0 (fun y => vecNormSq (u.grad y)))) +
        ENNReal.ofReal (D * κ) * quadraticBallMaximal F x := by
      rw [mul_add, ← ENNReal.ofReal_mul hD,
        ← mul_assoc (ENNReal.ofReal D) (ENNReal.ofReal κ),
        ← ENNReal.ofReal_mul hD]
      congr 2
      ring

end

end PDE
