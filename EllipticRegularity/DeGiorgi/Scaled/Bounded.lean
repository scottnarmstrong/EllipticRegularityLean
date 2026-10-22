module

public import EllipticRegularity.DeGiorgi.Scaled.LocalMax
public import EllipticRegularity.DeGiorgi.LogPackage.Defs
public import EllipticRegularity.DeGiorgi.MoserIter.Hypotheses

/-!
# Local boundedness on `B_{3/4}` and the rescaled `L^∞` estimate on `B_{1/8}(y)`

Two corollaries of the scaled local maximum principle
(`PDE.DGNMScaled.exists_scaled_localMax_constant`):

* `locMaxBall`: the hypothesis `LocMaxBallHyp` of the logarithmic package;
* `subsolutionBounded`: the hypothesis `SubsolutionBoundedHyp` of the Moser iteration,
  obtained from `ρ = 1/4` balls and a countable cover of `B_{3/4}`.
-/

@[expose] public section

namespace PDE.DGNMScaled

open PDE MeasureTheory

variable {d : ℕ}

/-- `B_r(y) ⊆ B_R(0)` when `‖y‖ + r ≤ R`. -/
theorem euclideanBall_subset_of_norm_add_le {y : Vec d} {r R : ℝ} (hr : 0 < r)
    (h : vecEuclideanNorm y + r ≤ R) : euclideanBall y r ⊆ euclideanBall (0 : Vec d) R := by
  intro x hx
  have hR : 0 < R := lt_of_lt_of_le (add_pos_of_nonneg_of_pos (by
    unfold vecEuclideanNorm; exact Real.sqrt_nonneg _) hr) h
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hr] at hx
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR, sub_zero]
  have := vecEuclideanNorm_add_le (x - y) y
  rw [sub_add_cancel] at this
  linarith

theorem ofReal_inv_pow_quarter_rpow (d : ℕ) :
    ENNReal.ofReal ((((1 : ℝ) / 4) ^ d)⁻¹) ^ ((1 : ℝ) / 2) = ENNReal.ofReal (2 ^ d) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  congr 1
  have h : (((1 : ℝ) / 4) ^ d)⁻¹ = ((2 : ℝ) ^ d) ^ 2 := by
    rw [one_div, inv_pow, inv_inv, ← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [← Real.sqrt_eq_rpow, h, Real.sqrt_sq (by positivity)]

/-- The local maximum principle on the balls `B_{1/8}(y) ⊆ B_{1/4}(y) ⊆ B_1`. -/
theorem locMaxBall (d : ℕ) (hd : 3 ≤ d) : PDE.DGNMLog.LocMaxBallHyp d := by
  obtain ⟨C, hC0, hC⟩ := exists_scaled_localMax_constant d hd
  refine ⟨C * 2 ^ d, by positivity, fun Λ a ha hEll w hsub y hy => ?_⟩
  have hball : euclideanBall y (1 / 4) ⊆ euclideanBall (0 : Vec d) 1 :=
    euclideanBall_subset_of_norm_add_le (by norm_num) hy.le
  have h := hC (isOpen_euclideanBall _ _) Λ a ha hEll w hsub y (1 / 4) (by norm_num) hball
  rw [ofReal_inv_pow_quarter_rpow, show (1 / 4 : ℝ) / 2 = 1 / 8 by norm_num] at h
  refine h.trans (le_of_eq ?_)
  rw [show C * 2 ^ d * Λ ^ ((d : ℝ) / 4) = 2 ^ d * (C * Λ ^ ((d : ℝ) / 4)) by ring,
    ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ d)]
  ring

/-- Subsolutions on `B_1` are essentially bounded above on `B_{3/4}`. -/
theorem subsolutionBounded (d : ℕ) (hd : 3 ≤ d) : PDE.DGNMMoser.SubsolutionBoundedHyp d := by
  intro Λ a ha hEll u hsub
  obtain ⟨C, hC0, hC⟩ := exists_scaled_localMax_constant d hd
  set K : ENNReal := ENNReal.ofReal (C * Λ ^ ((d : ℝ) / 4)) *
    (ENNReal.ofReal ((((1 : ℝ) / 4) ^ d)⁻¹) ^ ((1 : ℝ) / 2) *
      eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1))) with hK
  have hKtop : K ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top) ?_)
    exact u.memL2.eLpNorm_ne_top
  have hloc : ∀ x ∈ euclideanBall (0 : Vec d) (3 / 4),
      ∀ᵐ y ∂volumeOn (euclideanBall x (1 / 8)), u.toFun y ≤ K.toReal := by
    intro x hx
    have hx' : vecEuclideanNorm x < 3 / 4 := by
      have := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num : (0:ℝ) < 3 / 4)).1 hx
      simpa using this
    have hball : euclideanBall x (1 / 4) ⊆ euclideanBall (0 : Vec d) 1 :=
      euclideanBall_subset_of_norm_add_le (by norm_num) (by linarith)
    have h := hC (isOpen_euclideanBall _ _) Λ a ha hEll u hsub x (1 / 4) (by norm_num) hball
    rw [show (1 / 4 : ℝ) / 2 = 1 / 8 by norm_num] at h
    have h2 : essSup (fun y => ENNReal.ofReal (u.toFun y))
        (volumeOn (euclideanBall x (1 / 8))) ≤ K := by
      refine h.trans ?_
      rw [hK]
      gcongr
      exact Measure.restrict_mono hball le_rfl
    filter_upwards [ENNReal.ae_le_essSup (μ := volumeOn (euclideanBall x (1 / 8)))
      (fun y => ENNReal.ofReal (u.toFun y))] with y hy
    exact (ENNReal.ofReal_le_iff_le_toReal hKtop).1 (hy.trans h2)
  obtain ⟨t, htsub, htc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun x => euclideanBall x (1 / 8)) (s := euclideanBall (0 : Vec d) (3 / 4))
    (fun x hx => mem_nhdsWithin_of_mem_nhds
      ((isOpen_euclideanBall _ _).mem_nhds (center_mem_euclideanBall x (by norm_num))))
  refine ⟨K.toReal, ?_⟩
  have hall : ∀ᵐ y ∂volumeOn (⋃ x ∈ t, euclideanBall x (1 / 8)), u.toFun y ≤ K.toReal :=
    (ae_restrict_biUnion_iff _ htc _).2 fun x hx => hloc x (htsub hx)
  exact ae_restrict_of_ae_restrict_of_subset hcover hall

end PDE.DGNMScaled
