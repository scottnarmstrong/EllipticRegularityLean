module

public import EllipticRegularity.Parabolic.SliceEstimate.SliceTest
public import EllipticRegularity.Parabolic.SliceEstimate.WeakC1
public import EllipticRegularity.Parabolic.SliceEstimate.Cutoff
public import EllipticRegularity.Parabolic.Energy.Bridge

/-!
# Step 2: the mollified weak gradient of `φ² v`
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Slice

open MeasureTheory Set Filter Topology Metric PDE PDE.Parabolic PDE.Parabolic.Energy

variable {d : ℕ}

theorem fderiv_space_slice (φ : Vec d × ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (y : Vec d) (τ : ℝ)
    (i : Fin d) :
    fderiv ℝ (fun y => φ (y, τ)) y (basisVec i) = parSpaceGrad φ (y, τ) i := by
  have h1 : HasFDerivAt φ (fderiv ℝ φ (y, τ)) (y, τ) :=
    ((hφ.differentiable (by simp)) (y, τ)).hasFDerivAt
  have h2 : HasFDerivAt (fun y : Vec d => ((y, τ) : Vec d × ℝ))
      ((ContinuousLinearMap.id ℝ (Vec d)).prod 0) y :=
    (hasFDerivAt_id y).prodMk (hasFDerivAt_const τ y)
  have h3 : fderiv ℝ (fun y => φ (y, τ)) y =
      (fderiv ℝ φ (y, τ)).comp ((ContinuousLinearMap.id ℝ (Vec d)).prod 0) :=
    (h1.comp y h2).fderiv
  rw [h3]
  unfold parSpaceGrad
  simp

theorem contDiff_slice (φ : Vec d × ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (τ : ℝ) :
    ContDiff ℝ 1 fun y : Vec d => φ (y, τ) :=
  hφ.comp (contDiff_id.prodMk contDiff_const)

/-- The test function `y ↦ k_a(x - y) φ(y,τ)²`. -/
noncomputable def testFn (a : ℝ) (x : Vec d) (φ : Vec d × ℝ → ℝ) (τ : ℝ) : Vec d → ℝ :=
  fun y => kern a (x - y) * φ (y, τ) ^ 2

theorem testFn_contDiff (a : ℝ) (x : Vec d) (φ : Vec d × ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (τ : ℝ) :
    ContDiff ℝ 1 (testFn a x φ τ) :=
  (zeta_contDiff_one a x).mul ((contDiff_slice φ hφ τ).pow 2)

theorem testFn_eq_zero {a : ℝ} (ha : 0 < a) {x y : Vec d} (hy : y ∉ closedBall x a)
    (φ : Vec d × ℝ → ℝ) (τ : ℝ) : testFn a x φ τ y = 0 := by
  have := zeta_eq_zero ha hy
  simp only [zeta] at this
  simp [testFn, this]

theorem testFn_hasCompactSupport {a : ℝ} (ha : 0 < a) (x : Vec d) (φ : Vec d × ℝ → ℝ) (τ : ℝ) :
    HasCompactSupport (testFn a x φ τ) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x a) fun y hy => by
    by_contra h; exact hy (testFn_eq_zero ha h φ τ)

theorem testFn_tsupport_subset {a : ℝ} (ha : 0 < a) (x : Vec d) (φ : Vec d × ℝ → ℝ) (τ : ℝ) :
    tsupport (testFn a x φ τ) ⊆ closedBall x a := by
  refine closure_minimal (fun y hy => ?_) isClosed_closedBall
  by_contra h
  exact hy (testFn_eq_zero ha h φ τ)

theorem fderiv_testFn (a : ℝ) (x : Vec d) (φ : Vec d × ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (τ : ℝ)
    (y : Vec d) (i : Fin d) :
    fderiv ℝ (testFn a x φ τ) y (basisVec i) =
      -fderiv ℝ (kern a) (x - y) (basisVec i) * φ (y, τ) ^ 2 +
        kern a (x - y) * (2 * φ (y, τ) * parSpaceGrad φ (y, τ) i) := by
  have h1 : HasFDerivAt (zeta a x) (fderiv ℝ (zeta a x) y) y :=
    (((zeta_contDiff_one a x).differentiable (by simp)) y).hasFDerivAt
  have h2 : HasFDerivAt (fun y : Vec d => φ (y, τ) ^ 2)
      ((2 * φ (y, τ)) • fderiv ℝ (fun y => φ (y, τ)) y) y := by
    have := (((contDiff_slice φ hφ τ).differentiable (by simp)) y).hasFDerivAt.pow 2
    simpa using this
  have h3 : HasFDerivAt (fun y => zeta a x y * φ (y, τ) ^ 2)
      (zeta a x y • (2 * φ (y, τ)) • fderiv ℝ (fun y => φ (y, τ)) y +
        φ (y, τ) ^ 2 • fderiv ℝ (zeta a x) y) y := h1.mul h2
  have : testFn a x φ τ = fun y => zeta a x y * φ (y, τ) ^ 2 := rfl
  rw [this, h3.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul,
    fderiv_zeta, fderiv_space_slice φ hφ y τ i]
  simp [zeta]
  ring


/-- The mollified weak gradient of `φ² v` at a fixed time. -/
theorem psi_weak_identity
    (v : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (φ : ParCutoff (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    {K S : Set (Vec d)} {δ0 : ℝ} (hδ0 : 0 < δ0) (hKc : IsCompact K)
    (hcU : cthickening (2 * δ0) K ⊆ euclideanBall (0 : Vec d) 1)
    (hφ0 : ∀ x ∈ euclideanBall (0 : Vec d) 1, x ∉ K → ∀ τ ∈ Ioc (-1 : ℝ) 0,
      φ.toFun (x, τ) = 0)
    (hSc : IsCompact S) (hSB : S ⊆ euclideanBall (0 : Vec d) 1) (hKS : cthickening δ0 K ⊆ S)
    {a : ℝ} (ha0 : 0 < a) (haδ : a ≤ δ0) {τ : ℝ} (hτJ : τ ∈ Ioc (-1 : ℝ) 0)
    (hτ : HasWeakGradientOn (euclideanBall (0 : Vec d) 1) (parSlice v.toFun τ)
      (parSlice v.grad τ))
    (hv1 : Integrable (fun y => v.toFun (y, τ)) (volume.restrict S))
    (hv2 : ∀ i, Integrable (fun y => v.grad (y, τ) i) (volume.restrict S)) (x : Vec d) (i : Fin d) :
    ∫ y in S, kern a (x - y) * (φ.toFun (y, τ) ^ 2 * v.grad (y, τ) i +
        2 * φ.toFun (y, τ) * v.toFun (y, τ) * parSpaceGrad φ.toFun (y, τ) i) =
      ∫ y in S, fderiv ℝ (kern a) (x - y) (basisVec i) * (φ.toFun (y, τ) ^ 2 * v.toFun (y, τ)) := by
  have hU : IsOpen (euclideanBall (0 : Vec d) 1) := isOpen_euclideanBall _ _
  have hSm : MeasurableSet S := hSc.measurableSet
  have hKS' : K ⊆ S := (self_subset_cthickening K).trans hKS
  have hvan : ∀ y ∈ euclideanBall (0 : Vec d) 1, y ∉ K → φ.toFun (y, τ) = 0 := fun y hy hyK =>
    hφ0 y hy hyK τ hτJ
  by_cases hball : closedBall x a ⊆ euclideanBall (0 : Vec d) 1
  · have htsK : tsupport (testFn a x φ.toFun τ) ⊆ K := by
      refine closure_minimal (fun y hy => ?_) hKc.isClosed
      by_contra hyK
      have hyB : y ∈ euclideanBall (0 : Vec d) 1 := by
        by_contra hyB
        have : testFn a x φ.toFun τ y = 0 := testFn_eq_zero ha0 (fun hm => hyB (hball hm)) _ _
        exact hy this
      exact hy (by simp [testFn, hvan y hyB hyK])
    have h := weak_partial_C1 hU (hτ i) (testFn_contDiff a x φ.toFun φ.contDiff τ)
      (testFn_hasCompactSupport ha0 x φ.toFun τ)
      ((testFn_tsupport_subset ha0 x φ.toFun τ).trans hball) hSc hSB hδ0
      ((cthickening_subset_of_subset δ0 htsK).trans hKS) hv1 (hv2 i)
    simp only [parSlice] at h
    -- cut to `S`
    have hcut : ∀ f : Vec d → ℝ, (∀ y ∈ euclideanBall (0 : Vec d) 1, y ∉ K → f y = 0) →
        ∫ y in euclideanBall (0 : Vec d) 1, f y = ∫ y in S, f y := by
      intro f hf
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hSB fun y hy => ?_
      exact hf y hy.1 (fun hyK => hy.2 (hKS' hyK))
    simp only [fderiv_testFn a x φ.toFun φ.contDiff τ _ i] at h
    simp only [testFn] at h
    rw [hcut _ (fun y hy hyK => by simp [hvan y hy hyK]),
      hcut _ (fun y hy hyK => by simp [hvan y hy hyK])] at h
    -- the pieces
    have hbd2 : ∀ {g h : Vec d → ℝ}, Integrable g (volume.restrict S) → Continuous h →
        Integrable (fun y => g y * h y) (volume.restrict S) := by
      intro g h hg hh
      obtain ⟨C, hC⟩ := hSc.exists_bound_of_continuousOn hh.continuousOn
      exact hg.mul_bdd hh.aestronglyMeasurable (c := C)
        ((ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall fun y hy => hC y hy))
    have hφc : Continuous fun y : Vec d => φ.toFun (y, τ) := (contDiff_slice φ.toFun φ.contDiff τ).continuous
    have hdφ : Continuous fun y : Vec d => parSpaceGrad φ.toFun (y, τ) i :=
      ((φ.contDiff.continuous_fderiv one_ne_zero).clm_apply continuous_const).comp
        (continuous_id.prodMk continuous_const)
    have hk0 : Continuous fun y : Vec d => kern a (x - y) := (kern_continuous a).comp
      (continuous_const.sub continuous_id)
    have hk1 : Continuous fun y : Vec d => fderiv ℝ (kern a) (x - y) (basisVec i) :=
      (kern_fderiv_continuous a (basisVec i)).comp (continuous_const.sub continuous_id)
    have iA : Integrable (fun y => v.toFun (y, τ) * (-fderiv ℝ (kern a) (x - y) (basisVec i) *
        φ.toFun (y, τ) ^ 2)) (volume.restrict S) := hbd2 hv1 ((hk1.neg).mul (hφc.pow 2))
    have iB : Integrable (fun y => v.toFun (y, τ) * (kern a (x - y) *
        (2 * φ.toFun (y, τ) * parSpaceGrad φ.toFun (y, τ) i))) (volume.restrict S) :=
      hbd2 hv1 (hk0.mul ((continuous_const.mul hφc).mul hdφ))
    have iC : Integrable (fun y => v.grad (y, τ) i * (kern a (x - y) * φ.toFun (y, τ) ^ 2))
        (volume.restrict S) := hbd2 (hv2 i) (hk0.mul (hφc.pow 2))
    have hsplit : ∫ y in S, v.toFun (y, τ) * (-fderiv ℝ (kern a) (x - y) (basisVec i) *
        φ.toFun (y, τ) ^ 2 + kern a (x - y) * (2 * φ.toFun (y, τ) *
          parSpaceGrad φ.toFun (y, τ) i)) =
        (∫ y in S, v.toFun (y, τ) * (-fderiv ℝ (kern a) (x - y) (basisVec i) *
          φ.toFun (y, τ) ^ 2)) + ∫ y in S, v.toFun (y, τ) * (kern a (x - y) *
            (2 * φ.toFun (y, τ) * parSpaceGrad φ.toFun (y, τ) i)) := by
      rw [← integral_add iA iB]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only; ring
    rw [hsplit] at h
    have eA : ∫ y in S, v.toFun (y, τ) * (-fderiv ℝ (kern a) (x - y) (basisVec i) *
        φ.toFun (y, τ) ^ 2) =
        -∫ y in S, fderiv ℝ (kern a) (x - y) (basisVec i) * (φ.toFun (y, τ) ^ 2 * v.toFun (y, τ)) := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only; ring
    have eB : ∫ y in S, v.toFun (y, τ) * (kern a (x - y) *
        (2 * φ.toFun (y, τ) * parSpaceGrad φ.toFun (y, τ) i)) =
        ∫ y in S, kern a (x - y) * (2 * φ.toFun (y, τ) * v.toFun (y, τ) *
          parSpaceGrad φ.toFun (y, τ) i) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only; ring
    have eC : ∫ y in S, v.grad (y, τ) i * (kern a (x - y) * φ.toFun (y, τ) ^ 2) =
        ∫ y in S, kern a (x - y) * (φ.toFun (y, τ) ^ 2 * v.grad (y, τ) i) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only; ring
    have iR : Integrable (fun y => kern a (x - y) * (φ.toFun (y, τ) ^ 2 * v.grad (y, τ) i))
        (volume.restrict S) :=
      iC.congr (Filter.Eventually.of_forall fun y => by simp only; ring)
    have iQ : Integrable (fun y => kern a (x - y) * (2 * φ.toFun (y, τ) * v.toFun (y, τ) *
        parSpaceGrad φ.toFun (y, τ) i)) (volume.restrict S) :=
      iB.congr (Filter.Eventually.of_forall fun y => by simp only; ring)
    have hLHS : ∫ y in S, kern a (x - y) * (φ.toFun (y, τ) ^ 2 * v.grad (y, τ) i +
        2 * φ.toFun (y, τ) * v.toFun (y, τ) * parSpaceGrad φ.toFun (y, τ) i) =
        (∫ y in S, kern a (x - y) * (φ.toFun (y, τ) ^ 2 * v.grad (y, τ) i)) +
          ∫ y in S, kern a (x - y) * (2 * φ.toFun (y, τ) * v.toFun (y, τ) *
            parSpaceGrad φ.toFun (y, τ) i) := by
      rw [← integral_add iR iQ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only; ring
    rw [hLHS]
    rw [eA, eB, eC] at h
    linarith [h]
  · -- the ball sticks out of the unit ball: both sides vanish
    have hzero : ∀ y ∈ K, ‖x - y‖ ≤ a → False := by
      intro y hy hxy
      apply hball
      intro z hz
      apply hcU
      refine mem_cthickening_of_dist_le z y (2 * δ0) K hy ?_
      have h1 : dist z x ≤ a := mem_closedBall.1 hz
      have h2 : dist x y ≤ a := by rw [dist_eq_norm]; exact hxy
      have := dist_triangle z x y
      linarith
    have hk0 : ∀ y ∈ K, kern a (x - y) = 0 := fun y hy => by
      by_contra h
      exact hzero y hy (not_lt.mp fun hlt => h (kern_eq_zero_of_lt_norm ha0 hlt))
    have hk1 : ∀ y ∈ K, fderiv ℝ (kern a) (x - y) (basisVec i) = 0 := fun y hy => by
      by_contra h
      exact hzero y hy (not_lt.mp fun hlt => h (by
        rw [fderiv_kern_eq_zero_of_lt_norm ha0 hlt]; rfl))
    have hL : ∫ y in S, kern a (x - y) * (φ.toFun (y, τ) ^ 2 * v.grad (y, τ) i +
        2 * φ.toFun (y, τ) * v.toFun (y, τ) * parSpaceGrad φ.toFun (y, τ) i) = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
      by_cases hyK : y ∈ K
      · rw [hk0 y hyK, zero_mul]
      · rw [hvan y (hSB hy) hyK]; simp
    have hR : ∫ y in S, fderiv ℝ (kern a) (x - y) (basisVec i) *
        (φ.toFun (y, τ) ^ 2 * v.toFun (y, τ)) = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
      by_cases hyK : y ∈ K
      · rw [hk1 y hyK, zero_mul]
      · rw [hvan y (hSB hy) hyK]; simp
    rw [hL, hR]

end PDE.Parabolic.Slice
