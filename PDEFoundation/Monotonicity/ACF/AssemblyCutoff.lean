module

public import PDEFoundation.Monotonicity.ACF.SliceMain
public import PDEFoundation.Monotonicity.ACF.WeightedMain
public import PDEFoundation.Monotonicity.ACF.AssemblyEigen
public import PDEFoundation.Sobolev.H1.Product
public import PDEFoundation.Sobolev.Cutoff.Ball

/-!
# ACF-A: the slice Rayleigh bound for a function continuous only on the ball

`acf_slice_rayleigh_interface` assumes global continuity.  For `u` continuous on the open ball
`B_R` we multiply by a smooth cutoff equal to `1` on `B_{R'}` (`R' < R`) and supported in `B_R`,
apply the slice theorem on `(0, R')` and let `R' ↑ R` along a countable exhaustion.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace PDE

namespace ACFAssembly

noncomputable section

variable {d : ℕ}

/-- A.e. statements on `(0, R')` for all `R' < R` give the a.e. statement on `(0, R)`. -/
theorem ae_Ioo_of_exhaustion {R : ℝ} (hR : 0 < R) {P : ℝ → Prop}
    (h : ∀ R' : ℝ, 0 < R' → R' < R → ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R')), P r) :
    ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)), P r := by
  have hU : Ioo (0 : ℝ) R = ⋃ n : ℕ, Ioo (0 : ℝ) (R * (((n : ℝ) + 1) / ((n : ℝ) + 2))) := by
    ext r
    simp only [mem_Ioo, mem_iUnion]
    constructor
    · rintro ⟨h0, h1⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (R / (R - r))
      refine ⟨n, h0, ?_⟩
      have hRr : 0 < R - r := by linarith
      have h2 : R / (R - r) < (n : ℝ) + 2 := by linarith
      rw [div_lt_iff₀ hRr] at h2
      have h3 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      rw [mul_div_assoc', lt_div_iff₀ h3]
      nlinarith only [h2, h3]
    · rintro ⟨n, h0, h1⟩
      refine ⟨h0, lt_of_lt_of_le h1 ?_⟩
      have h3 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      rw [mul_div_assoc']
      rw [div_le_iff₀ h3]
      nlinarith only [hR, h3]
  rw [hU, ae_restrict_iUnion_iff]
  intro n
  refine h _ (by positivity) ?_
  have h3 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  rw [mul_div_assoc', div_lt_iff₀ h3]
  nlinarith only [hR, h3]

theorem classicalGradient_eq_zero_of_eventuallyEq_one {f : Vec d → ℝ} {x : Vec d}
    (h : f =ᶠ[nhds x] fun _ => 1) : classicalGradient f x = 0 := by
  funext i
  rw [classicalGradient_apply, h.fderiv_eq]
  simp

/-- The global-continuity cutoff of `u`. -/
def cutoffH1 {R : ℝ} (u : H1Function (euclideanBall (0 : Vec d) R)) {R' : ℝ}
    (hR' : 0 < R') (hRR' : R' < R) : H1Function (euclideanBall (0 : Vec d) R') :=
  (u.mulContDiffHasCompactSupport
    (canonicalBallCutoff_smooth (0 : Vec d) hR'.le hRR')
    (canonicalBallCutoff_hasCompactSupport hR'.le hRR')).restrict
    (isOpen_euclideanBall _ _) (euclideanBall_mono hR'.le hRR'.le)

theorem cutoffH1_toFun {R : ℝ} (u : H1Function (euclideanBall (0 : Vec d) R)) {R' : ℝ}
    (hR' : 0 < R') (hRR' : R' < R) :
    (cutoffH1 u hR' hRR').toFun =
      fun x => canonicalBallCutoff (0 : Vec d) R' R x * u.toFun x := by
  unfold cutoffH1
  simp only [H1Function.restrict_toFun, H1Function.mulContDiffHasCompactSupport_toFun]

theorem cutoffH1_grad {R : ℝ} (u : H1Function (euclideanBall (0 : Vec d) R)) {R' : ℝ}
    (hR' : 0 < R') (hRR' : R' < R) :
    (cutoffH1 u hR' hRR').grad =
      fun x => canonicalBallCutoff (0 : Vec d) R' R x • u.grad x +
        u.toFun x • classicalGradient (canonicalBallCutoff (0 : Vec d) R' R) x := by
  unfold cutoffH1
  simp only [H1Function.restrict_grad, H1Function.mulContDiffHasCompactSupport_grad]

theorem cutoffH1_toFun_eq {R : ℝ} (u : H1Function (euclideanBall (0 : Vec d) R))
    {R' : ℝ} (hR' : 0 < R') (hRR' : R' < R) {x : Vec d} (hx : x ∈ euclideanBall (0 : Vec d) R') :
    (cutoffH1 u hR' hRR').toFun x = u.toFun x := by
  rw [cutoffH1_toFun]
  show canonicalBallCutoff (0 : Vec d) R' R x * u.toFun x = u.toFun x
  rw [canonicalBallCutoff_eq_one_on_inner hR'.le hRR' hx, one_mul]

theorem cutoffH1_grad_eq {R : ℝ} (u : H1Function (euclideanBall (0 : Vec d) R))
    {R' : ℝ} (hR' : 0 < R') (hRR' : R' < R) {x : Vec d} (hx : x ∈ euclideanBall (0 : Vec d) R') :
    (cutoffH1 u hR' hRR').grad x = u.grad x := by
  rw [cutoffH1_grad]
  have h1 : canonicalBallCutoff (0 : Vec d) R' R =ᶠ[nhds x] fun _ => 1 := by
    filter_upwards [(isOpen_euclideanBall (0 : Vec d) R').mem_nhds hx] with y hy
    exact canonicalBallCutoff_eq_one_on_inner hR'.le hRR' hy
  simp only [canonicalBallCutoff_eq_one_on_inner hR'.le hRR' hx, one_smul,
    classicalGradient_eq_zero_of_eventuallyEq_one h1, smul_zero, add_zero]

theorem continuous_cutoffH1 {R : ℝ} (u : H1Function (euclideanBall (0 : Vec d) R))
    (hcont : ContinuousOn u.toFun (euclideanBall (0 : Vec d) R)) {R' : ℝ}
    (hR' : 0 < R') (hRR' : R' < R) : Continuous (cutoffH1 u hR' hRR').toFun := by
  rw [cutoffH1_toFun]
  have hη : Continuous (canonicalBallCutoff (0 : Vec d) R' R) :=
    (canonicalBallCutoff_smooth (0 : Vec d) hR'.le hRR').continuous
  refine continuous_iff_continuousAt.2 fun x => ?_
  by_cases hx : x ∈ euclideanBall (0 : Vec d) R
  · exact hη.continuousAt.mul
      (hcont.continuousAt ((isOpen_euclideanBall (0 : Vec d) R).mem_nhds hx))
  · have hxt : x ∉ tsupport (canonicalBallCutoff (0 : Vec d) R' R) := fun h =>
      hx (canonicalBallCutoff_tsupport_subset_outer hR'.le hRR' h)
    rw [notMem_tsupport_iff_eventuallyEq] at hxt
    have : (fun y => canonicalBallCutoff (0 : Vec d) R' R y * u.toFun y) =ᶠ[nhds x]
        fun _ => 0 := by
      filter_upwards [hxt] with y hy
      simp [hy]
    exact (continuousAt_const.congr this.symm)

theorem nonneg_cutoffH1 {R : ℝ} (u : H1Function (euclideanBall (0 : Vec d) R))
    (hnn : ∀ x ∈ euclideanBall (0 : Vec d) R, 0 ≤ u.toFun x) {R' : ℝ}
    (hR' : 0 < R') (hRR' : R' < R) (x : Vec d) : 0 ≤ (cutoffH1 u hR' hRR').toFun x := by
  rw [cutoffH1_toFun]
  by_cases hx : x ∈ euclideanBall (0 : Vec d) R
  · exact mul_nonneg (canonicalBallCutoff_nonneg _ _ _ _) (hnn x hx)
  · have : canonicalBallCutoff (0 : Vec d) R' R x = 0 := by
      by_contra h
      exact hx (canonicalBallCutoff_tsupport_subset_outer hR'.le hRR'
        (subset_tsupport _ (Function.mem_support.2 h)))
    simp [this]

end

end ACFAssembly

end PDE
