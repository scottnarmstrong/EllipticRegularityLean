module

public import EllipticRegularity.Parabolic.SliceEstimate.KernelFubini
public import EllipticRegularity.Parabolic.Energy.Mollifier

/-!
# The equation tested with a mollified function, at a fixed time

If the equation `∫ v ξ_y + ∫ F·∇ξ_y = 0` holds for all mollifier centers `y` in a set `𝒦`, it holds
for the mollification of any integrable `ψ` supported in `𝒦` whose mollified gradient is `g`.
-/

@[expose] public section

namespace PDE.Parabolic.Slice

open MeasureTheory Set PDE PDE.Parabolic.Energy

variable {d : ℕ}

theorem integrable_mul_kern {S : Set (Vec d)} {f : Vec d → ℝ}
    (hf : Integrable f (volume.restrict S)) {k : Vec d → ℝ} (hk : Continuous k) (C : ℝ)
    (hkb : ∀ x, |k x| ≤ C) (y : Vec d) :
    Integrable (fun x => f x * k (x - y)) (volume.restrict S) := by
  refine hf.mul_bdd (c := C) ((hk.comp (continuous_id.sub continuous_const)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  simpa [Real.norm_eq_abs] using hkb (x - y)

theorem continuous_kernel_conv {S : Set (Vec d)} {g : Vec d → ℝ}
    (hg : Integrable g (volume.restrict S)) {k : Vec d → ℝ} (hk : Continuous k) (C : ℝ)
    (hkb : ∀ x, |k x| ≤ C) : Continuous fun x => ∫ y in S, k (x - y) * g y := by
  refine continuous_of_dominated (bound := fun y => C * |g y|) ?_ ?_ ?_ ?_
  · intro x
    exact ((hk.comp (continuous_const.sub continuous_id)).aestronglyMeasurable).mul
      hg.aestronglyMeasurable
  · intro x
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hkb _) (abs_nonneg _)
  · exact hg.norm.const_mul C
  · exact Filter.Eventually.of_forall fun y => (hk.comp (continuous_id.sub continuous_const)).mul
      continuous_const

theorem continuous_kernel_pair {S : Set (Vec d)} {f : Vec d → ℝ}
    (hf : Integrable f (volume.restrict S)) {k : Vec d → ℝ} (hk : Continuous k) (C : ℝ)
    (hkb : ∀ x, |k x| ≤ C) : Continuous fun y => ∫ x in S, f x * k (x - y) := by
  refine continuous_of_dominated (bound := fun x => |f x| * C) ?_ ?_ ?_ ?_
  · intro y
    exact hf.aestronglyMeasurable.mul
      ((hk.comp (continuous_id.sub continuous_const)).aestronglyMeasurable)
  · intro y
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hkb _) (abs_nonneg _)
  · exact hf.norm.mul_const C
  · exact Filter.Eventually.of_forall fun x => continuous_const.mul
      (hk.comp (continuous_const.sub continuous_id))


/-- The equation at all mollifier centers implies the equation for the mollification. -/
theorem slice_test_identity {S 𝒦 : Set (Vec d)} (hS : IsCompact S) {a : ℝ} (ha : 0 < a)
    {f ψ : Vec d → ℝ} {F g : Fin d → Vec d → ℝ}
    (hf : Integrable f (volume.restrict S)) (hF : ∀ i, Integrable (F i) (volume.restrict S))
    (hψ : Integrable ψ (volume.restrict S)) (hg : ∀ i, Integrable (g i) (volume.restrict S))
    (hψ0 : ∀ y ∈ S, y ∉ 𝒦 → ψ y = 0)
    (hweak : ∀ i x, ∫ y in S, kern a (x - y) * g i y =
      ∫ y in S, fderiv ℝ (kern a) (x - y) (basisVec i) * ψ y)
    (hP : ∀ y ∈ 𝒦, ∫ x in S, (f x * kern a (x - y) +
      ∑ i, F i x * fderiv ℝ (kern a) (x - y) (basisVec i)) = 0) :
    ∫ x in S, (f x * (∫ y in S, kern a (x - y) * ψ y) +
      ∑ i, F i x * (∫ y in S, kern a (x - y) * g i y)) = 0 := by
  have hSfin : volume S < ⊤ := hS.measure_lt_top
  obtain ⟨C0, hC0⟩ := kern_bound (d := d) ha
  obtain ⟨Ci, hCi⟩ : ∃ Ci : Fin d → ℝ, ∀ i y, |fderiv ℝ (kern (d := d) a) y (basisVec i)| ≤ Ci i := by
    have := fun i => kern_fderiv_bound (d := d) ha (basisVec i)
    choose C hC using this
    exact ⟨C, hC⟩
  have hk0 : Continuous fun p : Vec d × Vec d => kern a (p.1 - p.2) :=
    (kern_continuous a).comp (continuous_fst.sub continuous_snd)
  have hki : ∀ i, Continuous fun p : Vec d × Vec d =>
      fderiv ℝ (kern (d := d) a) (p.1 - p.2) (basisVec i) := fun i =>
    (kern_fderiv_continuous a (basisVec i)).comp (continuous_fst.sub continuous_snd)
  -- the inner integrals as continuous bounded functions
  have hΨc : Continuous fun x => ∫ y in S, kern a (x - y) * ψ y :=
    continuous_kernel_conv hψ (kern_continuous a) C0 hC0
  have hGc : ∀ i, Continuous fun x => ∫ y in S, kern a (x - y) * g i y := fun i =>
    continuous_kernel_conv (hg i) (kern_continuous a) C0 hC0
  have hint0 : Integrable (fun x => f x * (∫ y in S, kern a (x - y) * ψ y)) (volume.restrict S) := by
    obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hΨc.continuousOn
    refine hf.mul_bdd hΨc.aestronglyMeasurable (c := B) ?_
    exact (ae_restrict_iff' hS.measurableSet).2 (Filter.Eventually.of_forall fun x hx => hB x hx)
  have hinti : ∀ i, Integrable (fun x => F i x * (∫ y in S, kern a (x - y) * g i y))
      (volume.restrict S) := fun i => by
    obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn (hGc i).continuousOn
    refine (hF i).mul_bdd (hGc i).aestronglyMeasurable (c := B) ?_
    exact (ae_restrict_iff' hS.measurableSet).2 (Filter.Eventually.of_forall fun x hx => hB x hx)
  rw [integral_add hint0 (integrable_finsetSum _ fun i _ => hinti i),
    integral_finsetSum _ fun i _ => hinti i]
  -- Fubini for each term
  have e0 := kernel_fubini (μ := volume) (S := S) hSfin hf hψ hk0 C0 hC0
  have ei : ∀ i, ∫ x in S, F i x * (∫ y in S, kern a (x - y) * g i y) =
      ∫ y in S, ψ y * (∫ x in S, F i x * fderiv ℝ (kern a) (x - y) (basisVec i)) := fun i => by
    have := kernel_fubini (μ := volume) (S := S) hSfin (hF i) hψ (hki i) (Ci i) (hCi i)
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hweak i x]
  rw [e0]
  simp only [ei]
  -- combine
  have hcomb : ∀ y : Vec d, ψ y * (∫ x in S, f x * kern a (x - y)) +
      ∑ i, ψ y * (∫ x in S, F i x * fderiv ℝ (kern a) (x - y) (basisVec i)) =
      ψ y * ∫ x in S, (f x * kern a (x - y) +
        ∑ i, F i x * fderiv ℝ (kern a) (x - y) (basisVec i)) := by
    intro y
    rw [integral_add (integrable_mul_kern hf (kern_continuous a) C0 hC0 y)
      (integrable_finsetSum _ fun i _ => integrable_mul_kern (hF i)
        (kern_fderiv_continuous a (basisVec i)) (Ci i) (hCi i) y),
      integral_finsetSum _ fun i _ => integrable_mul_kern (hF i)
        (kern_fderiv_continuous a (basisVec i)) (Ci i) (hCi i) y]
    rw [mul_add, Finset.mul_sum]
  have hfy : Continuous fun y => ∫ x in S, f x * kern a (x - y) :=
    continuous_kernel_pair hf (kern_continuous a) C0 hC0
  have hFy : ∀ i, Continuous fun y => ∫ x in S, F i x * fderiv ℝ (kern a) (x - y) (basisVec i) :=
    fun i => continuous_kernel_pair (hF i) (kern_fderiv_continuous a (basisVec i)) (Ci i) (hCi i)
  have hpsi : ∀ {h : Vec d → ℝ}, Continuous h → Integrable (fun y => ψ y * h y) (volume.restrict S) :=
    fun {h} hh => by
      obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hh.continuousOn
      refine hψ.mul_bdd hh.aestronglyMeasurable (c := B) ?_
      exact (ae_restrict_iff' hS.measurableSet).2 (Filter.Eventually.of_forall fun x hx => hB x hx)
  have hlhs : (∫ y in S, ψ y * (∫ x in S, f x * kern a (x - y))) +
      ∑ i, ∫ y in S, ψ y * (∫ x in S, F i x * fderiv ℝ (kern a) (x - y) (basisVec i)) =
      ∫ y in S, ψ y * ∫ x in S, (f x * kern a (x - y) +
        ∑ i, F i x * fderiv ℝ (kern a) (x - y) (basisVec i)) := by
    have h1 : ∑ i, ∫ y in S, ψ y * (∫ x in S, F i x * fderiv ℝ (kern a) (x - y) (basisVec i)) =
        ∫ y in S, ∑ i, ψ y * (∫ x in S, F i x * fderiv ℝ (kern a) (x - y) (basisVec i)) :=
      (integral_finsetSum _ fun i _ => hpsi (hFy i)).symm
    rw [h1, ← integral_add (hpsi hfy) (integrable_finsetSum _ fun i _ => hpsi (hFy i))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact hcomb y
  rw [hlhs]
  refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
  by_cases hyK : y ∈ 𝒦
  · rw [hP y hyK, mul_zero]
  · rw [hψ0 y hy hyK, zero_mul]


theorem integrable_mul_cont {S : Set (Vec d)} (hS : IsCompact S) {g h : Vec d → ℝ}
    (hg : Integrable g (volume.restrict S)) (hh : Continuous h) :
    Integrable (fun y => g y * h y) (volume.restrict S) := by
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hh.continuousOn
  exact hg.mul_bdd hh.aestronglyMeasurable (c := C)
    ((ae_restrict_iff' hS.measurableSet).2 (Filter.Eventually.of_forall fun y hy => hC y hy))

end PDE.Parabolic.Slice
