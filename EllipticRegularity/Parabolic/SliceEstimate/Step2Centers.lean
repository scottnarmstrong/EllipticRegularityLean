module

public import EllipticRegularity.Parabolic.SliceEstimate.Step2Weak
public import EllipticRegularity.Parabolic.SliceEstimate.CenterEq
public import EllipticRegularity.Parabolic.SliceEstimate.VSlice

/-!
# Step 2: the equation at mollifier centers
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Slice

open MeasureTheory Set Filter Topology Metric PDE PDE.Parabolic PDE.Parabolic.Energy
  PDE.Parabolic.WeakSlice

variable {d : ℕ}

/-- The mollifier centered at `y`: `x ↦ k_a(x - y)`. -/
noncomputable def xi (a : ℝ) (y : Vec d) : Vec d → ℝ := fun x => kern a (x - y)

theorem xi_contDiff_one (a : ℝ) (y : Vec d) : ContDiff ℝ 1 (xi a y) :=
  ((kern_smooth (d := d) a).comp (contDiff_id.sub contDiff_const)).of_le (by exact_mod_cast le_top)

theorem xi_eq_zero {a : ℝ} (ha : 0 < a) {y x : Vec d} (hx : x ∉ closedBall y a) :
    xi a y x = 0 := by
  apply kern_eq_zero_of_lt_norm ha
  rw [mem_closedBall, dist_eq_norm, not_le] at hx
  exact hx

theorem xi_hasCompactSupport {a : ℝ} (ha : 0 < a) (y : Vec d) : HasCompactSupport (xi a y) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall y a) fun x hx => by
    by_contra h; exact hx (xi_eq_zero ha h)

theorem xi_tsupport_subset {a : ℝ} (ha : 0 < a) (y : Vec d) : tsupport (xi a y) ⊆ closedBall y a := by
  refine closure_minimal (fun x hx => ?_) isClosed_closedBall
  by_contra h
  exact hx (xi_eq_zero ha h)

theorem fderiv_xi (a : ℝ) (y x e : Vec d) :
    fderiv ℝ (xi a y) x e = fderiv ℝ (kern a) (x - y) e := by
  have h1 : HasFDerivAt (kern (d := d) a) (fderiv ℝ (kern a) (x - y)) (x - y) :=
    (((kern_smooth (d := d) a).differentiable (by simp)) (x - y)).hasFDerivAt
  have h2 : HasFDerivAt (fun x : Vec d => x - y) (ContinuousLinearMap.id ℝ (Vec d)) x :=
    (hasFDerivAt_id x).sub_const y
  have h3 : fderiv ℝ (xi a y) x = fderiv ℝ (kern a) (x - y) ∘L (ContinuousLinearMap.id ℝ (Vec d)) :=
    (h1.comp x h2).fderiv
  rw [h3]; simp

/-- The pairing of the equation of `u` with the mollifier centered at `y`. -/
noncomputable def PF (a₀ : Vec d → Mat d)
    (u v : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)) (S : Set (Vec d))
    (a : ℝ) (y : Vec d) (τ : ℝ) : ℝ :=
  (∫ x in S, v.toFun (x, τ) * kern a (x - y)) +
    ∑ i, ∫ x in S, matVecMul (a₀ x) (u.grad (x, τ)) i * fderiv ℝ (kern a) (x - y) (basisVec i)

/-- The equation at a center, for a.e. time (at times with integrable flux slices). -/
theorem centers_ae {lam Lam : ℝ} {a₀ : Vec d → Mat d}
    (ha : IsParabolicCoeff lam Lam (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (u v : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hu : IsParabolicWeakSolution (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u)
    (hv : ∀ ψ : ParTestFunction (euclideanBall (0 : Vec d) 1) (interior (Ioc (-1 : ℝ) 0)),
      ∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, v.toFun z * ψ.toFun z =
        -∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
          u.toFun z * parTimeDeriv ψ.toFun z)
    {S : Set (Vec d)} (_hSm : MeasurableSet S) (hSB : S ⊆ euclideanBall (0 : Vec d) 1)
    {a : ℝ} (ha0 : 0 < a) {y : Vec d} (hy : closedBall y a ⊆ S) {p : ℝ}
    (hp : p ∈ Ioc (-1 : ℝ) 0) (hp0 : p < 0) :
    ∀ᵐ τ ∂(volume.restrict (Ioc p 0)),
      (∀ i, Integrable (fun x => matVecMul (a₀ x) (u.grad (x, τ)) i) (volume.restrict S)) →
      Integrable (fun x => v.toFun (x, τ)) (volume.restrict S) →
      PF a₀ u v S a y τ = 0 := by
  have hU : IsOpen (euclideanBall (0 : Vec d) 1) := isOpen_euclideanBall _ _
  have hI : (Ioc (-1 : ℝ) 0).OrdConnected := ordConnected_Ioc
  have hξU : tsupport (xi a y) ⊆ euclideanBall (0 : Vec d) 1 :=
    (xi_tsupport_subset ha0 y).trans (hy.trans hSB)
  have h0 : (0 : ℝ) ∈ Ioc (-1 : ℝ) 0 := ⟨by norm_num, le_rfl⟩
  filter_upwards [equation_ae hU hI ha u v hu hv (xi_contDiff_one a y) (xi_hasCompactSupport ha0 y)
    hξU hp h0 hp0] with τ hτ hF hv1
  have hcut : ∀ f : Vec d → ℝ, (∀ x ∈ euclideanBall (0 : Vec d) 1, x ∉ closedBall y a → f x = 0) →
      ∫ x in euclideanBall (0 : Vec d) 1, f x = ∫ x in S, f x := by
    intro f hf
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hSB fun x hx => ?_
    exact hf x hx.1 (fun h => hx.2 (hy h))
  have e1 : ∫ x in euclideanBall (0 : Vec d) 1, v.toFun (x, τ) * xi a y x =
      ∫ x in S, v.toFun (x, τ) * kern a (x - y) := by
    rw [hcut _ (fun x _ hx => by simp [xi_eq_zero ha0 hx])]
    rfl
  have hvec : ∀ x, vecDot (matVecMul (a₀ x) (u.grad (x, τ))) (spaceGradC1 (xi a y) x) =
      ∑ i, matVecMul (a₀ x) (u.grad (x, τ)) i * fderiv ℝ (kern a) (x - y) (basisVec i) := by
    intro x
    simp only [vecDot, spaceGradC1, fderiv_xi]
  obtain ⟨Ci, hCi⟩ : ∃ Ci : Fin d → ℝ, ∀ i z, |fderiv ℝ (kern (d := d) a) z (basisVec i)| ≤ Ci i := by
    have := fun i => kern_fderiv_bound (d := d) ha0 (basisVec i)
    choose C hC using this
    exact ⟨C, hC⟩
  have hint : ∀ i, Integrable (fun x => matVecMul (a₀ x) (u.grad (x, τ)) i *
      fderiv ℝ (kern a) (x - y) (basisVec i)) (volume.restrict S) := fun i =>
    integrable_mul_kern (hF i) (kern_fderiv_continuous a (basisVec i)) (Ci i) (hCi i) y
  have e2 : ∫ x in euclideanBall (0 : Vec d) 1,
      vecDot (matVecMul (a₀ x) (u.grad (x, τ))) (spaceGradC1 (xi a y) x) =
      ∑ i, ∫ x in S, matVecMul (a₀ x) (u.grad (x, τ)) i * fderiv ℝ (kern a) (x - y) (basisVec i) := by
    simp only [hvec]
    rw [hcut _ (fun x _ hx => by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [fderiv_kern_eq_zero_of_lt_norm ha0 (by
        rw [mem_closedBall, dist_eq_norm, not_le] at hx; exact hx)]
      simp),
      integral_finsetSum _ fun i _ => hint i]
  unfold PF
  rw [← e1, ← e2]
  exact hτ


theorem continuous_PF {a₀ : Vec d → Mat d}
    (u v : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)) {S : Set (Vec d)}
    {a : ℝ} (ha0 : 0 < a) (τ : ℝ)
    (hv : Integrable (fun x => v.toFun (x, τ)) (volume.restrict S))
    (hF : ∀ i, Integrable (fun x => matVecMul (a₀ x) (u.grad (x, τ)) i) (volume.restrict S)) :
    Continuous fun y => PF a₀ u v S a y τ := by
  obtain ⟨C0, hC0⟩ := kern_bound (d := d) ha0
  obtain ⟨Ci, hCi⟩ : ∃ Ci : Fin d → ℝ, ∀ i z, |fderiv ℝ (kern (d := d) a) z (basisVec i)| ≤ Ci i := by
    have := fun i => kern_fderiv_bound (d := d) ha0 (basisVec i)
    choose C hC using this
    exact ⟨C, hC⟩
  unfold PF
  refine (continuous_kernel_pair hv (kern_continuous a) C0 hC0).add
    (continuous_finsetSum _ fun i _ => ?_)
  exact continuous_kernel_pair (hF i) (kern_fderiv_continuous a (basisVec i)) (Ci i) (hCi i)

/-- The equation at all centers of a compact set, for a.e. time. -/
theorem all_centers_ae {lam Lam : ℝ} {a₀ : Vec d → Mat d}
    (ha : IsParabolicCoeff lam Lam (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (u v : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hu : IsParabolicWeakSolution (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u)
    (hv : ∀ ψ : ParTestFunction (euclideanBall (0 : Vec d) 1) (interior (Ioc (-1 : ℝ) 0)),
      ∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, v.toFun z * ψ.toFun z =
        -∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
          u.toFun z * parTimeDeriv ψ.toFun z)
    {S 𝒦 : Set (Vec d)} (hSm : MeasurableSet S) (hSB : S ⊆ euclideanBall (0 : Vec d) 1)
    {a : ℕ → ℝ} (ha0 : ∀ n, 0 < a n) (hball : ∀ n, ∀ y ∈ 𝒦, closedBall y (a n) ⊆ S)
    {p : ℝ} (hp : p ∈ Ioc (-1 : ℝ) 0) (hp0 : p < 0) :
    ∀ᵐ τ ∂(volume.restrict (Ioc p 0)),
      (∀ i, Integrable (fun x => matVecMul (a₀ x) (u.grad (x, τ)) i) (volume.restrict S)) →
      Integrable (fun x => v.toFun (x, τ)) (volume.restrict S) →
      ∀ n, ∀ y ∈ 𝒦, PF a₀ u v S (a n) y τ = 0 := by
  obtain ⟨Dc, hDc, hDcc, h𝒦Dc⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace 𝒦).exists_countable_dense_subset
  have h1 : ∀ n, ∀ y ∈ Dc, ∀ᵐ τ ∂(volume.restrict (Ioc p 0)),
      (∀ i, Integrable (fun x => matVecMul (a₀ x) (u.grad (x, τ)) i) (volume.restrict S)) →
      Integrable (fun x => v.toFun (x, τ)) (volume.restrict S) →
      PF a₀ u v S (a n) y τ = 0 := fun n y hy =>
    centers_ae ha u v hu hv hSm hSB (ha0 n) (hball n y (hDc hy)) hp hp0
  have h2 := (ae_all_iff (ι := ℕ)).2 fun n => (ae_ball_iff hDcc).2 (h1 n)
  filter_upwards [h2] with τ hτ hF hv' n y hy
  have hcont := continuous_PF (a₀ := a₀) u v (ha0 n) τ hv' hF
  have hclosed : IsClosed {y | PF a₀ u v S (a n) y τ = 0} := isClosed_eq hcont continuous_const
  have hsub : Dc ⊆ {y | PF a₀ u v S (a n) y τ = 0} := fun y hy => hτ n y hy hF hv'
  exact (closure_minimal hsub hclosed) (h𝒦Dc hy)

end PDE.Parabolic.Slice
