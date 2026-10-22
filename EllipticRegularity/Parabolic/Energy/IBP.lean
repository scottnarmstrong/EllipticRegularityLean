module

public import EllipticRegularity.Parabolic.Energy.Fubini

/-!
# Integration by parts in `x` at fixed time
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Energy

open MeasureTheory Set Filter Topology Metric PDE

variable {d : ℕ}

namespace Data

variable (D : Data d)

theorem mem_cthickening_two {a : ℝ} (haδ : a ≤ D.δ0) {x y : Vec d} (hy : y ∈ D.K1)
    (hxy : ‖x - y‖ ≤ a) : x ∈ cthickening (2 * D.δ0) D.K := by
  have hy' : y ∈ ⋃ p ∈ D.K, closedBall p D.δ0 := by
    rw [← D.hK.cthickening_eq_biUnion_closedBall D.hδ0.le]; exact hy
  simp only [mem_iUnion] at hy'
  obtain ⟨p, hp, hyp⟩ := hy'
  refine mem_cthickening_of_dist_le x p (2 * D.δ0) D.K hp ?_
  calc dist x p ≤ dist x y + dist y p := dist_triangle _ _ _
    _ ≤ a + D.δ0 := add_le_add (by rwa [dist_eq_norm]) (by simpa using hyp)
    _ ≤ 2 * D.δ0 := by linarith

theorem v_eq_zero_of_far {a : ℝ} (ha : 0 < a) (haδ : a ≤ D.δ0) {x : Vec d}
    (hx : x ∉ cthickening (2 * D.δ0) D.K) (τ : ℝ) : D.v a (x, τ) = 0 := by
  unfold v mollT
  refine moll_eq_zero ha fun y hy => ?_
  have : y ∉ D.K1 := fun hyK => hx (D.mem_cthickening_two haδ hyK hy)
  simp [this]

theorem g_vanishes {a : ℝ} (ha : 0 < a) (haδ : a ≤ D.δ0) {τ : ℝ} (hτ : τ ∈ Icc D.s D.t)
    {x : Vec d} (hx : x ∉ D.K) : D.φ (x, τ) ^ 2 * D.v a (x, τ) = 0 := by
  by_cases h2 : x ∈ cthickening (2 * D.δ0) D.K
  · rw [D.hφK x τ hτ h2 hx]; simp
  · rw [D.v_eq_zero_of_far ha haδ h2]; simp

theorem fderiv_phi_slice (σ : ℝ) (x : Vec d) (i : Fin d) :
    fderiv ℝ (fun x => D.φ (x, σ)) x (basisVec i) = parSpaceGrad D.φ (x, σ) i := by
  have h1 : HasFDerivAt D.φ (fderiv ℝ D.φ (x, σ)) (x, σ) :=
    ((D.hφ.differentiable (by simp)) (x, σ)).hasFDerivAt
  have h2 : HasFDerivAt (fun x : Vec d => ((x, σ) : Vec d × ℝ))
      (ContinuousLinearMap.inl ℝ (Vec d) ℝ) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const σ x)
  have h3 : fderiv ℝ (fun x : Vec d => D.φ (x, σ)) x =
      fderiv ℝ D.φ (x, σ) ∘L ContinuousLinearMap.inl ℝ (Vec d) ℝ := (h1.comp x h2).fderiv
  rw [h3]
  rfl

theorem contDiff_phi_slice (σ : ℝ) : ContDiff ℝ 1 fun x : Vec d => D.φ (x, σ) :=
  D.hφ.comp (contDiff_id.prodMk contDiff_const)

theorem fderiv_v_apply {a : ℝ} (ha : 0 < a) {σ : ℝ} (hσ : σ ∈ Icc D.s D.t) {x : Vec d}
    (i : Fin d)
    (hDu : ∫ y in D.K1, fderiv ℝ (kern a) (x - y) (basisVec i) * D.u (y, σ) =
      ∫ y in D.K1, kern a (x - y) * D.Du (y, σ) i) :
    fderiv ℝ (fun x => D.v a (x, σ)) x (basisVec i) = mollT a D.K1 (fun z => D.Du z i) (x, σ) := by
  have h1 : fderiv ℝ (wholeSpaceMollify a (D.K1.indicator fun y => D.u (y, σ))) x (basisVec i) =
      ∫ y, fderiv ℝ (kern a) (x - y) (basisVec i) * (D.K1.indicator fun y => D.u (y, σ)) y :=
    moll_fderiv_apply ha ((D.slice_memLp hσ).locallyIntegrable (by norm_num)) x (basisVec i)
  have h2 : ∫ y, fderiv ℝ (kern a) (x - y) (basisVec i) *
      (D.K1.indicator fun y => D.u (y, σ)) y =
      ∫ y in D.K1, fderiv ℝ (kern a) (x - y) (basisVec i) * D.u (y, σ) := by
    rw [← integral_indicator D.K1_measurable]
    congr 1; funext y
    by_cases hy : y ∈ D.K1 <;> simp [hy]
  have h3 : mollT a D.K1 (fun z => D.Du z i) (x, σ) =
      ∫ y in D.K1, kern a (x - y) * D.Du (y, σ) i := by
    rw [mollT_eq, ← integral_indicator D.K1_measurable]
    congr 1; funext y
    by_cases hy : y ∈ D.K1 <;> simp [hy]
  change fderiv ℝ (wholeSpaceMollify a (D.K1.indicator fun y => D.u (y, σ))) x (basisVec i) = _
  rw [h1, h2, hDu, h3]

theorem fderiv_g_apply {a : ℝ} (ha : 0 < a) {σ : ℝ} (hσ : σ ∈ Icc D.s D.t) (x e : Vec d) :
    fderiv ℝ (fun x => D.φ (x, σ) ^ 2 * D.v a (x, σ)) x e =
      D.φ (x, σ) ^ 2 * fderiv ℝ (fun x => D.v a (x, σ)) x e +
        2 * D.φ (x, σ) * D.v a (x, σ) * fderiv ℝ (fun x => D.φ (x, σ)) x e := by
  have hφd : HasFDerivAt (fun x => D.φ (x, σ)) (fderiv ℝ (fun x => D.φ (x, σ)) x) x :=
    (((D.contDiff_phi_slice σ).differentiable (by simp)) x).hasFDerivAt
  have hvd : HasFDerivAt (fun x => D.v a (x, σ)) (fderiv ℝ (fun x => D.v a (x, σ)) x) x :=
    ((((D.v_contDiff ha hσ).of_le (by exact_mod_cast le_top) :
      ContDiff ℝ 1 fun x => D.v a (x, σ)).differentiable (by simp)) x).hasFDerivAt
  have := (hφd.pow 2).mul hvd
  rw [show (fun x => D.φ (x, σ) ^ 2 * D.v a (x, σ)) =
      ((fun x => D.φ (x, σ) ^ 2) * fun x => D.v a (x, σ)) from rfl, this.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Integration by parts of the term `φ² v D̂` at a fixed time. -/
theorem ibp_slice {a : ℝ} (ha : 0 < a) (haδ : a ≤ D.δ0) {σ : ℝ} (hσ : σ ∈ Icc D.s D.t)
    (hGσ : ∀ i, Integrable (fun y => D.G (y, σ) i) (volume.restrict D.K1))
    (hDu : ∀ x ∈ D.K, ∀ i, ∫ y in D.K1, fderiv ℝ (kern a) (x - y) (basisVec i) * D.u (y, σ) =
      ∫ y in D.K1, kern a (x - y) * D.Du (y, σ) i) :
    ∫ x in D.K, D.H2 a (x, σ) =
      -∫ x in D.K, ∑ i, mollT a D.K1 (fun z => D.G z i) (x, σ) *
        (D.φ (x, σ) ^ 2 * mollT a D.K1 (fun z => D.Du z i) (x, σ) +
          2 * D.φ (x, σ) * D.v a (x, σ) * parSpaceGrad D.φ (x, σ) i) := by
  set f : Fin d → Vec d → ℝ := fun i => D.K1.indicator fun y => D.G (y, σ) i with hf
  have hfint : ∀ i, Integrable (f i) volume := fun i =>
    (integrable_indicator_iff D.K1_measurable).2 (hGσ i)
  have hmG : ∀ i x, mollT a D.K1 (fun z => D.G z i) (x, σ) = wholeSpaceMollify a (f i) x :=
    fun i x => rfl
  set g : Vec d → ℝ := fun x => D.φ (x, σ) ^ 2 * D.v a (x, σ) with hg
  have hvC : ContDiff ℝ 1 (fun x => D.v a (x, σ)) :=
    (D.v_contDiff ha hσ).of_le (by exact_mod_cast le_top)
  have hgC : ContDiff ℝ 1 g := ((D.contDiff_phi_slice σ).pow 2).mul hvC
  have hgK : ∀ x, x ∉ D.K → g x = 0 := fun x hx => D.g_vanishes ha haδ hσ hx
  have hDh : ∀ x, D.Dh a x σ = ∑ i, fderiv ℝ (wholeSpaceMollify a (f i)) x (basisVec i) := by
    intro x
    unfold Dh
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [moll_fderiv_apply ha (hfint i).locallyIntegrable x (basisVec i),
        ← integral_indicator D.K1_measurable]
      congr 1; funext y
      by_cases hy : y ∈ D.K1 <;> simp [hf, hy, mul_comm]
    · intro i _
      obtain ⟨C, hC⟩ := kern_fderiv_bound (d := d) ha (basisVec i)
      refine Integrable.mul_bdd (hGσ i) (c := C) ?_ (Filter.Eventually.of_forall fun y => ?_)
      · exact ((kern_fderiv_continuous a (basisVec i)).comp
          (continuous_const.sub continuous_id)).aestronglyMeasurable
      · simpa using hC (x - y)
  have hlocf : ∀ i, LocallyIntegrable (f i) volume := fun i => (hfint i).locallyIntegrable
  have hint := fun i => ibp_moll_integrable ha D.hK hgC hgK (hlocf i) (basisVec i)
  -- step 1: pass to the whole space
  have hz1 : ∀ x, x ∉ D.K →
      (∑ i, g x * fderiv ℝ (wholeSpaceMollify a (f i)) x (basisVec i)) = 0 := by
    intro x hx
    rw [← Finset.mul_sum, hgK x hx, zero_mul]
  have e1 : ∫ x in D.K, D.H2 a (x, σ) =
      ∫ x, ∑ i, g x * fderiv ℝ (wholeSpaceMollify a (f i)) x (basisVec i) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz1]
    refine setIntegral_congr_fun D.K_measurable fun x _ => ?_
    simp only [H2, hDh, ← Finset.mul_sum, hg, mul_assoc]
  rw [e1, integral_finsetSum _ fun i _ => (hint i).1]
  have e2 : ∀ i, ∫ x, g x * fderiv ℝ (wholeSpaceMollify a (f i)) x (basisVec i) =
      -∫ x, fderiv ℝ g x (basisVec i) * wholeSpaceMollify a (f i) x :=
    fun i => ibp_moll ha D.hK hgC hgK (hlocf i) (basisVec i)
  simp only [e2]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun i _ => (hint i).2]
  congr 1
  have hz2 : ∀ x, x ∉ D.K →
      (∑ i, fderiv ℝ g x (basisVec i) * wholeSpaceMollify a (f i) x) = 0 := by
    intro x hx
    simp [fderiv_eq_zero_of_forall_compl D.hK.isClosed hgK hx]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz2]
  refine setIntegral_congr_fun D.K_measurable fun x hx => Finset.sum_congr rfl fun i _ => ?_
  have h1 := D.fderiv_g_apply ha hσ x (basisVec i)
  have h2 := D.fderiv_v_apply ha hσ (x := x) i (hDu x hx i)
  rw [D.fderiv_phi_slice σ x i] at h1
  rw [h2] at h1
  change fderiv ℝ (fun x => D.φ (x, σ) ^ 2 * D.v a (x, σ)) x (basisVec i) *
    wholeSpaceMollify a (f i) x = _
  rw [h1, ← hmG]
  ring

end Data
