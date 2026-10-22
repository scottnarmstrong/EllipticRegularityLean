module

public import EllipticRegularity.DeGiorgi.Assembly.SupBound
public import EllipticRegularity.DeGiorgi.Assembly.Gluing

/-!
# Pointwise Harnack inequality for the continuous representative

Consequence of the Harnack inequality (on the level of essential extrema) for a continuous
representative `v` of a solution, applied to `c + s v` on balls `B_r(x) ⊆ B_{3/4}`.
-/

@[expose] public section

open scoped ENNReal Pointwise

namespace PDE.DGNMAssembly

open MeasureTheory Filter

variable {d : ℕ}

theorem ball_subset_three_quarters {x : Vec d} {r : ℝ} (hx : x ∈ euclideanBall (0 : Vec d) (1 / 2))
    (hr : 0 < r) (hr4 : r ≤ 1 / 4) :
    euclideanBall x r ⊆ euclideanBall (0 : Vec d) (3 / 4) := by
  apply euclideanBall_subset_of_center_norm_add_le hr (by norm_num)
  have := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hx
  rw [sub_zero] at this ⊢
  linarith

theorem ball_three_quarters_subset_unit :
    euclideanBall (0 : Vec d) (3 / 4) ⊆ euclideanBall (0 : Vec d) 1 :=
  euclideanBall_mono (by norm_num) (by norm_num)

/-- Pointwise Harnack inequality on balls for a continuous representative. -/
theorem harnack_pointwise (d : ℕ) (hH : HarnackConcl d) (hSol : SolAffineTransfer d) :
    ∃ CH : ℝ, ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) 0 →
      ∀ v : Vec d → ℝ, ContinuousOn v (euclideanBall (0 : Vec d) (3 / 4)) →
      v =ᵐ[volumeOn (euclideanBall (0 : Vec d) (3 / 4))] u.toFun →
      ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ, 0 < r → r ≤ 1 / 4 →
      ∀ s c : ℝ, (s = 1 ∨ s = -1) → (∀ y ∈ euclideanBall x r, 0 < c + s * v y) →
      ∀ y ∈ euclideanBall x (r / 2), ∀ z ∈ euclideanBall x (r / 2),
        c + s * v y ≤ Real.exp (CH * Real.sqrt Λ) * (c + s * v z) := by
  obtain ⟨CH, hCH, hHq⟩ := hH
  refine ⟨CH, ?_⟩
  intro Λ a hmeas hell u hsol v hvc hvu x hx r hr hr4 s c hs hpos y hy z hz
  have hsub34 := ball_subset_three_quarters hx hr hr4
  have hsub : euclideanBall x r ⊆ euclideanBall (0 : Vec d) 1 :=
    hsub34.trans ball_three_quarters_subset_unit
  obtain ⟨ut, hut, hsolt⟩ := hSol Λ a hmeas hell x r hr hsub u hsol s c
  obtain ⟨hmeast, hellt⟩ := coeff_comp_aff hmeas hell x hr hsub
  have hutfun : ut.toFun = fun y => c + s * u.toFun (x + r • y) := funext hut
  -- a.e. equality `v = u` on the ball
  have hvuB : ∀ᵐ w ∂(volumeOn (euclideanBall x r)), v w = u.toFun w :=
    ae_mono (Measure.restrict_mono hsub34 le_rfl) hvu
  have hpost : ∀ᵐ y ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < ut.toFun y := by
    have h2 := (ae_ball_comp_aff_iff x hr (one_pos : (0 : ℝ) < 1)
      (fun w => 0 < c + s * u.toFun w)).2 (by
        rw [mul_one]
        have hmem : ∀ᵐ w ∂(volumeOn (euclideanBall x r)), w ∈ euclideanBall x r :=
          ae_restrict_mem (isOpen_euclideanBall _ _).measurableSet
        filter_upwards [hvuB, hmem] with w hw1 hw2
        rw [← hw1]; exact hpos w hw2)
    rw [hutfun]; exact h2
  have hHarn := hHq Λ _ hmeast hellt ut hpost hsolt
  -- the continuous representative of `ut` on `B_{1/2}`
  set vt : Vec d → ℝ := fun y => c + s * v (x + r • y) with hvt
  have hmapsto : ∀ y ∈ euclideanBall (0 : Vec d) (1 / 2), x + r • y ∈ euclideanBall (0 : Vec d) (3 / 4) := by
    intro y hy
    apply hsub34
    have := (aff_mem_ball_iff x y hr (by norm_num : (0 : ℝ) < 1 / 2)).2 hy
    exact euclideanBall_mono (by positivity) (by nlinarith) this
  have hcontaff : Continuous fun y : Vec d => x + r • y := by fun_prop
  have hvtc : ContinuousOn vt (euclideanBall (0 : Vec d) (1 / 2)) :=
    continuousOn_const.add (continuousOn_const.mul (hvc.comp hcontaff.continuousOn hmapsto))
  have hvtae : (fun w => ENNReal.ofReal (vt w)) =ᵐ[volumeOn (euclideanBall (0 : Vec d) (1 / 2))]
      fun w => ENNReal.ofReal (ut.toFun w) := by
    have h3 := (ae_ball_comp_aff_iff x hr (by norm_num : (0 : ℝ) < 1 / 2)
      (fun w => v w = u.toFun w)).2 (by
        refine ae_mono (Measure.restrict_mono ?_ le_rfl) hvu
        exact (euclideanBall_mono (by positivity) (by nlinarith)).trans hsub34)
    filter_upwards [h3] with w hw
    rw [hutfun]
    simp only [hvt]
    rw [hw]
  -- transport the points
  have hy' : r⁻¹ • (y - x) ∈ euclideanBall (0 : Vec d) (1 / 2) := by
    rw [← aff_mem_ball_iff x _ hr (by norm_num : (0 : ℝ) < 1 / 2)]
    have : x + r • (r⁻¹ • (y - x)) = y := by
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]; abel
    rw [this, show r * (1 / 2) = r / 2 by ring]; exact hy
  have hz' : r⁻¹ • (z - x) ∈ euclideanBall (0 : Vec d) (1 / 2) := by
    rw [← aff_mem_ball_iff x _ hr (by norm_num : (0 : ℝ) < 1 / 2)]
    have : x + r • (r⁻¹ • (z - x)) = z := by
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]; abel
    rw [this, show r * (1 / 2) = r / 2 by ring]; exact hz
  have h1 := ofReal_le_essSup_of_cont (isOpen_euclideanBall (0 : Vec d) (1 / 2))
    (subset_refl _) hvtc hvtae hy'
  have h2 := essInf_le_ofReal_of_cont (isOpen_euclideanBall (0 : Vec d) (1 / 2))
    (subset_refl _) hvtc hvtae hz'
  have hyx : x + r • (r⁻¹ • (y - x)) = y := by
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]; abel
  have hzx : x + r • (r⁻¹ • (z - x)) = z := by
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]; abel
  have hvty : vt (r⁻¹ • (y - x)) = c + s * v y := by simp only [hvt, hyx]
  have hvtz : vt (r⁻¹ • (z - x)) = c + s * v z := by simp only [hvt, hzx]
  have hzpos : 0 < c + s * v z := hpos z (euclideanBall_mono (by positivity) (by linarith) hz)
  have h4 : ENNReal.ofReal (c + s * v y) ≤
      ENNReal.ofReal (Real.exp (CH * Real.sqrt Λ)) * ENNReal.ofReal (c + s * v z) := by
    rw [← hvty] at *
    rw [← hvtz] at *
    exact h1.trans (hHarn.trans (by gcongr))
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le] at h4
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.exp_pos _).le hzpos.le)).1 h4

end PDE.DGNMAssembly
