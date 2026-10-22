module

public import EllipticRegularity.Parabolic.ParabolicDef
public import PDEFoundation.Sobolev.Inequalities.SobolevWholeSpaceMollify

/-!
# Spatial mollification: derivative formulas, supports, integration by parts

For `a > 0` write `kern a` for the scaled unit kernel (smooth, nonnegative, unit mass, supported in
the closed ball of radius `a` for the sup norm) and `wholeSpaceMollify a f = kern a ⋆ f`.  This
module records the pointwise formulas needed for the energy identity.
-/

@[expose] public section

namespace PDE.Parabolic.Energy

open MeasureTheory Convolution Set

variable {d : ℕ}

/-- The scaled unit mollifier kernel. -/
noncomputable abbrev kern (a : ℝ) : Vec d → ℝ :=
  scaledConvexApproxKernel unitConvexApproxKernel a

theorem kern_smooth (a : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (kern (d := d) a) :=
  contDiff_scaledConvexApproxKernel isConvexApproxKernel_unitConvexApproxKernel a

theorem kern_contDiff_one (a : ℝ) : ContDiff ℝ 1 (kern (d := d) a) :=
  (kern_smooth a).of_le (by exact_mod_cast le_top)

theorem kern_continuous (a : ℝ) : Continuous (kern (d := d) a) :=
  (kern_smooth a).continuous

theorem kern_hasCompactSupport {a : ℝ} (ha : 0 < a) : HasCompactSupport (kern (d := d) a) :=
  hasCompactSupport_scaledConvexApproxKernel
    (isConvexApproxKernel_unitConvexApproxKernel (d := d)).compactSupport ha

theorem kern_nonneg {a : ℝ} (ha : 0 < a) (y : Vec d) : 0 ≤ kern a y :=
  scaledConvexApproxKernel_nonneg isConvexApproxKernel_unitConvexApproxKernel ha y

theorem integral_kern {a : ℝ} (ha : 0 < a) : ∫ y, kern (d := d) a y = 1 :=
  integral_scaledConvexApproxKernel isConvexApproxKernel_unitConvexApproxKernel ha

theorem kern_eq_zero_of_lt_norm {a : ℝ} (ha : 0 < a) {y : Vec d} (hy : a < ‖y‖) :
    kern a y = 0 :=
  scaledUnitKernel_eq_zero_of_lt_norm ha hy

/-- The directional derivative of the kernel is continuous. -/
theorem kern_fderiv_continuous (a : ℝ) (e : Vec d) :
    Continuous fun z => fderiv ℝ (kern (d := d) a) z e :=
  ((kern_smooth a).continuous_fderiv (by simp)).clm_apply continuous_const

theorem kern_fderiv_hasCompactSupport {a : ℝ} (ha : 0 < a) (e : Vec d) :
    HasCompactSupport fun z => fderiv ℝ (kern (d := d) a) z e :=
  ((kern_hasCompactSupport ha).fderiv (𝕜 := ℝ)).comp_left
    (g := fun L : Vec d →L[ℝ] ℝ => L e) (by simp)

theorem kern_bound {a : ℝ} (ha : 0 < a) : ∃ C : ℝ, ∀ y : Vec d, |kern a y| ≤ C := by
  obtain ⟨C, hC⟩ := (kern_continuous (d := d) a).bounded_above_of_compact_support
    (kern_hasCompactSupport ha)
  exact ⟨C, fun y => by simpa using hC y⟩

theorem kern_fderiv_bound {a : ℝ} (ha : 0 < a) (e : Vec d) :
    ∃ C : ℝ, ∀ y : Vec d, |fderiv ℝ (kern (d := d) a) y e| ≤ C := by
  obtain ⟨C, hC⟩ := (kern_fderiv_continuous (d := d) a e).bounded_above_of_compact_support
    (kern_fderiv_hasCompactSupport ha e)
  exact ⟨C, fun y => by simpa using hC y⟩

/-! ### The mollification as an integral -/

theorem moll_eq (a : ℝ) (f : Vec d → ℝ) (x : Vec d) :
    wholeSpaceMollify a f x = ∫ y, kern a (x - y) * f y := by
  simp only [wholeSpaceMollify]
  rw [convolution_eq_swap]
  rfl

theorem moll_hasFDerivAt {a : ℝ} (ha : 0 < a) {f : Vec d → ℝ}
    (hf : LocallyIntegrable f volume) (x : Vec d) :
    HasFDerivAt (wholeSpaceMollify a f)
      (((fderiv ℝ (kern a)) ⋆[ContinuousLinearMap.precompL (Vec d)
        (ContinuousLinearMap.lsmul ℝ ℝ), volume] f) x) x :=
  (kern_hasCompactSupport ha).hasFDerivAt_convolution_left _ (kern_contDiff_one a) hf x

theorem moll_fderiv_apply {a : ℝ} (ha : 0 < a) {f : Vec d → ℝ}
    (hf : LocallyIntegrable f volume) (x e : Vec d) :
    fderiv ℝ (wholeSpaceMollify a f) x e = ∫ y, fderiv ℝ (kern a) (x - y) e * f y := by
  rw [(moll_hasFDerivAt ha hf x).fderiv]
  have hk' : HasCompactSupport (fderiv ℝ (kern (d := d) a)) :=
    (kern_hasCompactSupport ha).fderiv (𝕜 := ℝ)
  have hkc : Continuous (fderiv ℝ (kern (d := d) a)) :=
    (kern_smooth a).continuous_fderiv (by simp)
  have hex := hk'.convolutionExists_left
    (ContinuousLinearMap.precompL (Vec d) (ContinuousLinearMap.lsmul ℝ ℝ)) hkc hf x
  rw [convolution_def]
  have := (ContinuousLinearMap.apply ℝ ℝ e).integral_comp_comm hex
  simp only [ContinuousLinearMap.apply_apply] at this
  rw [← this]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← integral_sub_left_eq_self _ volume x]
  simp only [sub_sub_cancel]

theorem moll_contDiff {a : ℝ} (ha : 0 < a) {f : Vec d → ℝ} (hf : LocallyIntegrable f volume) :
    ContDiff ℝ (⊤ : ℕ∞) (wholeSpaceMollify a f) := by
  have := (kern_hasCompactSupport (d := d) ha).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) (n := ⊤) (kern_smooth a) hf
  exact this

theorem moll_eq_zero {a : ℝ} (ha : 0 < a) {f : Vec d → ℝ} {x : Vec d}
    (hf : ∀ y, ‖x - y‖ ≤ a → f y = 0) : wholeSpaceMollify a f x = 0 := by
  rw [moll_eq]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : a < ‖x - y‖
  · simp [kern_eq_zero_of_lt_norm ha hy]
  · simp [hf y (not_lt.mp hy)]

theorem ibp_moll_integrable {a : ℝ} (ha : 0 < a) {K : Set (Vec d)} (hK : IsCompact K)
    {g : Vec d → ℝ} (hg : ContDiff ℝ 1 g) (hgK : ∀ x, x ∉ K → g x = 0) {f : Vec d → ℝ}
    (hf : LocallyIntegrable f volume) (e : Vec d) :
    Integrable (fun x => g x * fderiv ℝ (wholeSpaceMollify a f) x e) ∧
      Integrable (fun x => fderiv ℝ g x e * wholeSpaceMollify a f x) := by
  have hhs : ContDiff ℝ (⊤ : ℕ∞) (wholeSpaceMollify a f) := moll_contDiff ha hf
  have hh1 : ContDiff ℝ 1 (wholeSpaceMollify a f) := hhs.of_le (by exact_mod_cast le_top)
  have hgc : HasCompactSupport g :=
    HasCompactSupport.of_support_subset_isCompact hK (fun x hx => by
      by_contra hxK; exact hx (hgK x hxK))
  have hg'c : HasCompactSupport fun x => fderiv ℝ g x e :=
    (hgc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Vec d →L[ℝ] ℝ => L e) (by simp)
  have hg'cont : Continuous fun x => fderiv ℝ g x e :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hh'cont : Continuous fun x => fderiv ℝ (wholeSpaceMollify a f) x e :=
    (hh1.continuous_fderiv (by simp)).clm_apply continuous_const
  exact ⟨(hg.continuous.mul hh'cont).integrable_of_hasCompactSupport hgc.mul_right,
    (hg'cont.mul hh1.continuous).integrable_of_hasCompactSupport hg'c.mul_right⟩

theorem fderiv_eq_zero_of_forall_compl {K : Set (Vec d)} (hK : IsClosed K) {g : Vec d → ℝ}
    (hgK : ∀ x, x ∉ K → g x = 0) {x : Vec d} (hx : x ∉ K) : fderiv ℝ g x = 0 := by
  have : g =ᶠ[nhds x] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hK.isOpen_compl.mem_nhds hx) fun y hy => hgK y hy
  rw [this.fderiv_eq]
  simp

/-- Integration by parts of a compactly supported `C¹` function against a mollification. -/
theorem ibp_moll {a : ℝ} (ha : 0 < a) {K : Set (Vec d)} (hK : IsCompact K) {g : Vec d → ℝ}
    (hg : ContDiff ℝ 1 g) (hgK : ∀ x, x ∉ K → g x = 0) {f : Vec d → ℝ}
    (hf : LocallyIntegrable f volume) (e : Vec d) :
    ∫ x, g x * fderiv ℝ (wholeSpaceMollify a f) x e =
      -∫ x, fderiv ℝ g x e * wholeSpaceMollify a f x := by
  set h := wholeSpaceMollify a f with hh
  have hhs : ContDiff ℝ (⊤ : ℕ∞) h := moll_contDiff ha hf
  have hh1 : ContDiff ℝ 1 h := hhs.of_le (by exact_mod_cast le_top)
  have hgc : HasCompactSupport g :=
    HasCompactSupport.of_support_subset_isCompact hK (fun x hx => by
      by_contra hxK; exact hx (hgK x hxK))
  have hg'c : HasCompactSupport fun x => fderiv ℝ g x e :=
    (hgc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Vec d →L[ℝ] ℝ => L e) (by simp)
  have hg'cont : Continuous fun x => fderiv ℝ g x e :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hh'cont : Continuous fun x => fderiv ℝ h x e :=
    (hh1.continuous_fderiv (by simp)).clm_apply continuous_const
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_ ?_ ?_
  · exact (hg'cont.mul hh1.continuous).integrable_of_hasCompactSupport hg'c.mul_right
  · exact (hg.continuous.mul hh'cont).integrable_of_hasCompactSupport hgc.mul_right
  · exact (hg.continuous.mul hh1.continuous).integrable_of_hasCompactSupport hgc.mul_right
  · intro x _; exact (hg.differentiable (by simp)) x
  · intro x _; exact (hh1.differentiable (by simp)) x

end PDE.Parabolic.Energy
