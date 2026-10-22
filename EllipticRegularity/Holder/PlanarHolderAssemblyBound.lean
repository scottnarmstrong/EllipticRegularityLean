module

public import EllipticRegularity.Holder.PlanarHolderAssemblyGlue
public import PDEFoundation.Regularity.HolderLocalToGlobal

/-! # Global Hölder and supremum bounds on the half unit ball -/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- A fixed axis cube of half-side `1/8` lies in the half unit Euclidean ball. -/
private theorem referenceCube_subset_halfBall :
    centeredAxisCube (0 : Vec 2) (1 / 8) ⊆
      euclideanBall (0 : Vec 2) (1 / 2) := by
  have hsqrt : Real.sqrt (2 : ℕ) ≤ 2 := by
    have hsq : Real.sqrt (2 : ℕ) ^ 2 = 2 := by norm_num
    nlinarith [Real.sqrt_nonneg (2 : ℕ)]
  have hrad : 2 * Real.sqrt (2 : ℕ) * (1 / 8 : ℝ) ≤ 1 / 2 := by
    calc
      _ ≤ 2 * 2 * (1 / 8 : ℝ) := by gcongr
      _ = 1 / 2 := by norm_num
  exact (centeredAxisCube_subset_euclideanBall
    (by norm_num : 0 < 2) (0 : Vec 2)
    (by norm_num : (0 : ℝ) < 1 / 8)).trans
      (euclideanBall_mono (by positivity) hrad)

/-- Local Euclidean Hölder control with a fixed threshold globalizes on the
convex half unit ball at a numerical cost independent of the exponent. -/
theorem planarHolder_global_of_local
    {v : Vec 2 → ℝ} {α L : ℝ}
    (hα : 0 < α) (hαone : α ≤ 1) (hL : 0 ≤ L)
    (hlocal : ∀ x ∈ euclideanBall (0 : Vec 2) (1 / 2),
      ∀ y ∈ euclideanBall (0 : Vec 2) (1 / 2),
      ‖x - y‖ < planarHolderPatchRadius →
      |v x - v y| ≤ L * vecEuclideanNorm (x - y) ^ α) :
    ∀ x ∈ euclideanBall (0 : Vec 2) (1 / 2),
      ∀ y ∈ euclideanBall (0 : Vec 2) (1 / 2),
        |v x - v y| ≤
          (4096 * L) * vecEuclideanNorm (x - y) ^ α := by
  let S : Set (Vec 2) := euclideanBall (0 : Vec 2) (1 / 2)
  have hroot : 0 ≤ Real.sqrt (2 : ℕ) := Real.sqrt_nonneg _
  have hrootLe : Real.sqrt (2 : ℕ) ≤ 2 := by
    have hsq : Real.sqrt (2 : ℕ) ^ 2 = 2 := by norm_num
    nlinarith
  have hrootPow : Real.sqrt (2 : ℕ) ^ α ≤ 2 := by
    calc
      Real.sqrt (2 : ℕ) ^ α ≤ (2 : ℝ) ^ α :=
        Real.rpow_le_rpow hroot hrootLe hα.le
      _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hαone
      _ = 2 := by norm_num
  have hlocalSup : ∀ x ∈ S, ∀ y ∈ S,
      ‖x - y‖ ≤ planarHolderPatchRadius / 2 →
      |v x - v y| ≤ (2 * L) * ‖x - y‖ ^ α := by
    intro x hx y hy hxy
    have hδ : 0 < planarHolderPatchRadius := by
      norm_num [planarHolderPatchRadius, planarHolderRootRadius]
    have hxy' : ‖x - y‖ < planarHolderPatchRadius := by linarith
    have hloc := hlocal x hx y hy hxy'
    have hpow := Real.rpow_le_rpow
      (vecEuclideanNorm_nonneg (x - y))
      (vecEuclideanNorm_le_sqrt_natCast_mul_norm (x - y)) hα.le
    calc
      |v x - v y| ≤ L * vecEuclideanNorm (x - y) ^ α := hloc
      _ ≤ L * (Real.sqrt (2 : ℕ) * ‖x - y‖) ^ α :=
        mul_le_mul_of_nonneg_left hpow hL
      _ = (L * Real.sqrt (2 : ℕ) ^ α) * ‖x - y‖ ^ α := by
        rw [Real.mul_rpow hroot (norm_nonneg _)]
        ring
      _ ≤ (2 * L) * ‖x - y‖ ^ α := by
        exact mul_le_mul_of_nonneg_right
          (by simpa only [mul_comm] using
            mul_le_mul_of_nonneg_left hrootPow hL)
          (Real.rpow_nonneg (norm_nonneg _) _)
  have hglobalSup := abs_sub_le_of_localHolder_on_convex
    (S := S) (D := 1) (ρ := planarHolderPatchRadius / 2)
    (N := 2048) (α := α) (K := 2 * L)
    (convex_euclideanBall (0 : Vec 2) (1 / 2))
    (fun x hx y hy => norm_sub_le_one_of_mem_euclideanBall_half hx hy)
    hα (mul_nonneg (by norm_num) hL) (by norm_num)
    (by norm_num [planarHolderPatchRadius, planarHolderRootRadius])
    hlocalSup
  intro x hx y hy
  have hsup := hglobalSup x hx y hy
  have hpow : ‖x - y‖ ^ α ≤ vecEuclideanNorm (x - y) ^ α :=
    Real.rpow_le_rpow (norm_nonneg _) (norm_le_vecEuclideanNorm _) hα.le
  calc
    |v x - v y| ≤ 2048 * (2 * L) * ‖x - y‖ ^ α := hsup
    _ ≤ 4096 * L * vecEuclideanNorm (x - y) ^ α := by
      have hcoeff : 0 ≤ 4096 * L := mul_nonneg (by norm_num) hL
      nlinarith [mul_le_mul_of_nonneg_left hpow hcoeff]

/-- An a.e.-equal global representative with a Hölder bound has a pointwise
supremum bound from the `L²` mass on the unit ball. -/
theorem planarHolder_sup_bound_of_globalHolder
    {u : H1Function (euclideanBall (0 : Vec 2) 1)}
    {v : Vec 2 → ℝ} {α H : ℝ}
    (hα : 0 < α) (hH : 0 ≤ H)
    (hEq : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec 2) (1 / 2)),
      v x = u.toFun x)
    (hHolder : ∀ x ∈ euclideanBall (0 : Vec 2) (1 / 2),
      ∀ y ∈ euclideanBall (0 : Vec 2) (1 / 2),
        |v x - v y| ≤ H * vecEuclideanNorm (x - y) ^ α) :
    ∀ x ∈ euclideanBall (0 : Vec 2) (1 / 2),
      |v x| ≤
        4 * Real.sqrt (∫ z in euclideanBall (0 : Vec 2) 1,
          u.toFun z ^ 2) + H := by
  let U : Set (Vec 2) := euclideanBall (0 : Vec 2) 1
  let S : Set (Vec 2) := euclideanBall (0 : Vec 2) (1 / 2)
  let Q : Set (Vec 2) := centeredAxisCube (0 : Vec 2) (1 / 8)
  let L : ℝ := ∫ z in U, u.toFun z ^ 2
  have hQsub : Q ⊆ S := referenceCube_subset_halfBall
  have hSsub : S ⊆ U := euclideanBall_mono (by norm_num) (by norm_num)
  have hQpos : 0 < volume Q := volume_centeredAxisCube_pos _ (by norm_num)
  have hQtop : volume Q ≠ ∞ := volume_centeredAxisCube_ne_top _ _
  have huniv : (volumeOn Q) Set.univ = volume Q := by
    rw [Measure.restrict_apply'
      (isOpen_centeredAxisCube (0 : Vec 2) (1 / 8)).measurableSet]
    simp only [Set.univ_inter, Q]
  let : IsFiniteMeasure (volumeOn Q) := isFiniteMeasure_restrict.mpr hQtop
  have hsqU : IntegrableOn (fun z => u.toFun z ^ 2) U := by
    simpa [pow_two] using
      (integrableOn_mul_of_memL2On (U := U) u.memL2 u.memL2)
  have hsqQ : Integrable (fun z => u.toFun z ^ 2) (volumeOn Q) :=
    hsqU.mono_set (hQsub.trans hSsub)
  have hEqQ : v =ᵐ[volumeOn Q] u.toFun :=
    ae_restrict_of_ae_restrict_of_subset hQsub hEq
  have hbad : (volumeOn Q) {z | v z ≠ u.toFun z} = 0 := by
    exact ae_iff.mp hEqQ
  have hN : (volumeOn Q)
      ({z | v z ≠ u.toFun z} ∪ Qᶜ) = 0 := by
    apply measure_union_null hbad
    rw [Measure.restrict_apply'
      (isOpen_centeredAxisCube (0 : Vec 2) (1 / 8)).measurableSet]
    change volume (Qᶜ ∩ Q) = 0
    simp
  have hμne : (volumeOn Q) Set.univ ≠ 0 := by
    rw [huniv]
    exact hQpos.ne'
  obtain ⟨y, hyN, hyAvg⟩ :=
    exists_notMem_null_le_average
      (μ := volumeOn Q) (f := fun z => u.toFun z ^ 2)
      (Measure.measure_univ_ne_zero.mp hμne) hsqQ hN
  have hyQ : y ∈ Q := by
    by_contra hy
    exact hyN (Or.inr hy)
  have hyEq : v y = u.toFun y := by
    by_contra hne
    exact hyN (Or.inl hne)
  have hyS : y ∈ S := hQsub hyQ
  have hvolQ : (volume Q).toReal = 1 / 16 := by
    simpa only [Q] using
      (show (volume (centeredAxisCube (0 : Vec 2) (1 / 8))).toReal = 1 / 16 by
        rw [volume_centeredAxisCube_toReal (0 : Vec 2)
          (by norm_num : (0 : ℝ) ≤ 1 / 8)]
        norm_num)
  have hAvg : (⨍ z, u.toFun z ^ 2 ∂volumeOn Q) =
      16 * ∫ z in Q, u.toFun z ^ 2 := by
    rw [average_eq]
    simp only [Measure.real, smul_eq_mul]
    rw [huniv]
    rw [hvolQ]
    norm_num
  have hL : 0 ≤ L := integral_nonneg fun z => sq_nonneg (u.toFun z)
  have hQle : (∫ z in Q, u.toFun z ^ 2) ≤ L :=
    setIntegral_mono_set hsqU
      (Filter.Eventually.of_forall fun z => sq_nonneg (u.toFun z))
      (Filter.Eventually.of_forall fun z hz => hSsub (hQsub hz))
  have hySq : u.toFun y ^ 2 ≤ 16 * L := by
    rw [hAvg] at hyAvg
    exact hyAvg.trans (mul_le_mul_of_nonneg_left hQle (by norm_num))
  have hyAbs : |v y| ≤ 4 * Real.sqrt L := by
    rw [hyEq]
    have hright : 0 ≤ 4 * Real.sqrt L :=
      mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
    apply (sq_le_sq₀ (abs_nonneg _) hright).mp
    rw [mul_pow, Real.sq_sqrt hL, sq_abs]
    nlinarith [hySq]
  intro x hx
  have hdist : vecEuclideanNorm (x - y) ≤ 1 := by
    have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt
      (by norm_num : (0 : ℝ) < 1 / 2)).1 hx
    have hy' := (mem_euclideanBall_iff_vecEuclideanNorm_lt
      (by norm_num : (0 : ℝ) < 1 / 2)).1 hyS
    simp only [sub_zero] at hx' hy'
    have htri := vecEuclideanNorm_add_le x (-y)
    have hneg : vecEuclideanNorm (-y) = vecEuclideanNorm y :=
      vecEuclideanNorm_neg y
    simpa only [sub_zero, sub_eq_add_neg, hneg] using
      (htri.trans (by linarith only [hx', hy', hneg]))
  have hpow : vecEuclideanNorm (x - y) ^ α ≤ 1 := by
    simpa using
      Real.rpow_le_rpow (vecEuclideanNorm_nonneg _) hdist hα.le
  have hxy := hHolder x hx y hyS
  calc
    |v x| = |(v x - v y) + v y| := by congr 1; ring
    _ ≤ |v x - v y| + |v y| := abs_add_le _ _
    _ ≤ H * vecEuclideanNorm (x - y) ^ α + 4 * Real.sqrt L :=
      add_le_add hxy hyAbs
    _ ≤ 4 * Real.sqrt L + H := by
      have := mul_le_mul_of_nonneg_left hpow hH
      linarith

end

end PDE
