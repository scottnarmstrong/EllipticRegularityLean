/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.CauchyDef
public import EllipticRegularity.Parabolic.WeakSlice.Product
public import PDEFoundation.Sobolev.Cutoff.Ball

/-! # Spatial cutoffs for the whole-space Cauchy energy identity -/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Energy

open MeasureTheory Set PDE.Parabolic.WeakSlice

/-- A spatial cutoff equal to one on radius `R`, supported in radius `2R`, with gradient
bound `32/R`. -/
noncomputable def cauchySpatialCutoff {d : ℕ} (R : ℝ) (hR : 0 < R) :
    QuantitativeSmoothCutoff (euclideanBall (0 : Vec d) R)
      (euclideanBall (0 : Vec d) (2 * R)) (32 / R) := by
  have hRout : R < 2 * R := by linarith
  have hc := quantitativeBallCutoff (0 : Vec d) hR.le hRout
  have hconst : 32 / (2 * R - R) = 32 / R := by
    congr 1
    ring
  simpa only [hconst] using hc

/-- A time independent spatial cutoff, viewed as a parabolic cutoff on `[s,T]`. -/
noncomputable def cauchyParabolicCutoff {d : ℕ} (s T R : ℝ) (hR : 0 < R) :
    ParCutoff (univ : Set (Vec d)) (Icc s T) := by
  let ζ : Vec d → ℝ := (cauchySpatialCutoff R hR).toFun
  have hζall : ContDiff ℝ (⊤ : ℕ∞) ζ := (cauchySpatialCutoff R hR).smooth
  have hζ : ContDiff ℝ 1 ζ := hζall.of_le (by norm_num)
  refine ⟨fun z => (1 : ℝ) * ζ z.1, ?_, ?_⟩
  · exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ))).comp contDiff_snd |>.mul
      (hζ.comp contDiff_fst)
  · refine ⟨tsupport ζ ×ˢ Icc s T,
      (cauchySpatialCutoff R hR).hasCompactSupport.isCompact.prod isCompact_Icc,
      ?_, ?_⟩
    · exact Set.prod_mono (subset_univ _) subset_rfl
    · rintro ⟨x, t⟩ ⟨-, ht⟩ hnot
      have hxnot : x ∉ tsupport ζ := by
        intro hx
        exact hnot ⟨hx, ht⟩
      have hζx : ζ x = 0 := image_eq_zero_of_notMem_tsupport hxnot
      simp [hζx]

theorem cauchyParabolicCutoff_nonneg_le_one {d : ℕ} (s T R : ℝ)
    (hR : 0 < R) (z : Vec d × ℝ) :
    0 ≤ (cauchyParabolicCutoff s T R hR).toFun z ∧
      (cauchyParabolicCutoff s T R hR).toFun z ≤ 1 := by
  change 0 ≤ (1 : ℝ) * (cauchySpatialCutoff R hR).toFun z.1 ∧
    (1 : ℝ) * (cauchySpatialCutoff R hR).toFun z.1 ≤ 1
  simpa only [one_mul] using ⟨(cauchySpatialCutoff R hR).nonneg z.1,
    (cauchySpatialCutoff R hR).le_one z.1⟩

theorem cauchyParabolicCutoff_eq_one {d : ℕ} (s T R : ℝ)
    (hR : 0 < R) {x : Vec d} (hx : x ∈ euclideanBall 0 R) {t : ℝ} :
    (cauchyParabolicCutoff s T R hR).toFun (x, t) = 1 := by
  change (1 : ℝ) * (cauchySpatialCutoff R hR).toFun x = 1
  rw [one_mul]
  exact (cauchySpatialCutoff R hR).eq_one_on_inner x hx

theorem cauchyParabolicCutoff_timeDeriv_eq_zero {d : ℕ} (s T R : ℝ)
    (hR : 0 < R) (x : Vec d) (t : ℝ) :
    parTimeDeriv (cauchyParabolicCutoff s T R hR).toFun (x, t) = 0 := by
  change parTimeDeriv
      (fun z : Vec d × ℝ => (1 : ℝ) * (cauchySpatialCutoff R hR).toFun z.1) (x, t) = 0
  rw [parTimeDeriv_prod (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ)))
    ((cauchySpatialCutoff R hR).smooth.of_le (by norm_num))]
  simp

theorem cauchyParabolicCutoff_spatialGrad_bound {d : ℕ} (s T R : ℝ)
    (hR : 0 < R) (x : Vec d) (t : ℝ) :
    vecEuclideanNorm
        (parSpaceGrad (cauchyParabolicCutoff s T R hR).toFun (x, t)) ≤ 32 / R := by
  change vecEuclideanNorm (parSpaceGrad
      (fun z : Vec d × ℝ => (1 : ℝ) * (cauchySpatialCutoff R hR).toFun z.1) (x, t)) ≤ 32 / R
  rw [parSpaceGrad_prod (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ)))
    ((cauchySpatialCutoff R hR).smooth.of_le (by norm_num))]
  simp only [one_smul]
  have hgrad : spaceGradC1 (cauchySpatialCutoff R hR).toFun x =
      classicalGradient (cauchySpatialCutoff R hR).toFun x := by
    ext i
    rfl
  rw [hgrad]
  simpa only [one_smul] using (cauchySpatialCutoff R hR).gradient_bound x

end PDE.Parabolic.Cauchy.Energy
