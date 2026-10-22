module

public import PDEFoundation.Sobolev.Ch4.LipschitzProduct
public import PDEFoundation.Sobolev.Ch4.Compact
public import PDEFoundation.Sobolev.H1.ZeroBoundaryLimit

/-!
# Zero boundary values: Lipschitz multipliers

* `ofMemH10` upgrades representative-level membership `MemH10 U f.toFun` to an `H10Function`
  whose underlying `H1Function` is exactly `f`.
* `mulLipH10`: a compactly supported (in `U`) bounded Lipschitz multiplier times an `H¹(U)`
  function is in `H¹₀(U)`.
* `mulLipOfH10`: a bounded Lipschitz multiplier times an `H¹₀(U)` function is in `H¹₀(U)`.
-/

@[expose] public section

open scoped ENNReal Topology
open MeasureTheory Set Filter

namespace PDE.Ch4Infra

variable {d : ℕ} {U : Set (Vec d)}

/-- Upgrade `MemH10 U f.toFun` to an `H10Function` with the same `H1Function` representatives. -/
noncomputable def ofMemH10 (hU : IsOpen U) (f : H1Function U) (h : MemH10 U f.toFun) :
    H10Function U := by
  classical
  let v := Classical.choose h
  have hv : v.toH1Function.toFun = f.toFun := Classical.choose_spec h
  have hgrad : ∀ i, (fun x => v.toH1Function.grad x i) =ᵐ[volumeOn U] (fun x => f.grad x i) := by
    intro i
    refine HasWeakPartialDerivOn.ae_eq hU
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((v.toH1Function.gradMemL2 i).locallyIntegrable (by norm_num)))
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((f.gradMemL2 i).locallyIntegrable (by norm_num))) ?_ (f.hasWeakPartialDerivOn i)
    have := v.toH1Function.hasWeakPartialDerivOn i
    rwa [hv] at this
  exact
    { toH1Function := f
      approx := v.approx
      approx_smooth := v.approx_smooth
      approx_hasCompactSupport := v.approx_hasCompactSupport
      approx_support_subset := v.approx_support_subset
      tendsto_approx := by simpa [hv] using v.tendsto_approx
      tendsto_approx_grad := fun i => by
        have := v.tendsto_approx_grad i
        refine this.congr fun n => eLpNorm_congr_ae ?_
        filter_upwards [hgrad i] with x hx
        rw [hx] }

@[simp] theorem ofMemH10_toH1Function (hU : IsOpen U) (f : H1Function U) (h : MemH10 U f.toFun) :
    (ofMemH10 hU f h).toH1Function = f := rfl

/-- A compactly supported (in `U`), bounded Lipschitz multiplier times an `H¹(U)` function is in
`H¹₀(U)`; the underlying `H¹` function is `mulLip`. -/
noncomputable def mulLipH10 (hU : IsOpen U) (u : H1Function U) {L M : ℝ} {η : Vec d → ℝ}
    (hη : EucLip L η) (hL : 0 ≤ L) (hM : ∀ x, |η x| ≤ M) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ U) : H10Function U :=
  toH10OfCompact hU (mulLip hU u hη hL hM) hηU hηc
    (fun x _ hx => by simp [image_eq_zero_of_notMem_tsupport hx])

@[simp] theorem mulLipH10_toH1Function (hU : IsOpen U) (u : H1Function U) {L M : ℝ}
    {η : Vec d → ℝ} (hη : EucLip L η) (hL : 0 ≤ L) (hM : ∀ x, |η x| ≤ M)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    (mulLipH10 hU u hη hL hM hηc hηU).toH1Function = mulLip hU u hη hL hM := rfl

/-! ### Continuity of the Lipschitz product in `H¹` -/

theorem eLpNorm_mulLip_sub_value_le (hU : IsOpen U) (u v : H1Function U) {L M : ℝ}
    {η : Vec d → ℝ} (hη : EucLip L η) (hL : 0 ≤ L) (hM : ∀ x, |η x| ≤ M) :
    eLpNorm (fun x => (mulLip hU u hη hL hM).toFun x - (mulLip hU v hη hL hM).toFun x) 2
        (volumeOn U) ≤
      ENNReal.ofReal M * eLpNorm (fun x => u.toFun x - v.toFun x) 2 (volumeOn U) := by
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    ((mulLip_memL2 u hη hL hM).aestronglyMeasurable.sub
      (mulLip_memL2 v hη hL hM).aestronglyMeasurable) (Eventually.of_forall fun x => ?_) 2
  show ‖η x * u.toFun x - η x * v.toFun x‖ ≤ M * ‖u.toFun x - v.toFun x‖
  rw [← mul_sub, norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)

theorem eLpNorm_mulLip_sub_grad_le (hU : IsOpen U) (u v : H1Function U) {L M : ℝ}
    {η : Vec d → ℝ} (hη : EucLip L η) (hL : 0 ≤ L) (hM : ∀ x, |η x| ≤ M) (i : Fin d) :
    eLpNorm (fun x => (mulLip hU u hη hL hM).grad x i - (mulLip hU v hη hL hM).grad x i) 2
        (volumeOn U) ≤
      ENNReal.ofReal M * eLpNorm (fun x => u.grad x i - v.grad x i) 2 (volumeOn U) +
        ENNReal.ofReal L * eLpNorm (fun x => u.toFun x - v.toFun x) 2 (volumeOn U) := by
  have hMnn : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set Dη : Vec d → ℝ := fun x => fderiv ℝ η x (basisVec i) with hDη
  have hDm : AEStronglyMeasurable Dη (volumeOn U) :=
    (EucLip.aestronglyMeasurable_partialDeriv i).mono_measure Measure.restrict_le_self
  have hDb : ∀ᵐ x ∂(volumeOn U), ‖Dη x‖ ≤ L := ae_restrict_of_ae (hη.ae_abs_partialDeriv_le hL i)
  have heq : (fun x => (mulLip hU u hη hL hM).grad x i - (mulLip hU v hη hL hM).grad x i) =
      (fun x => η x * (u.grad x i - v.grad x i)) +
        fun x => (u.toFun x - v.toFun x) * Dη x := by
    funext x
    simp [hDη, classicalGradient]
    ring
  have hg : AEStronglyMeasurable (fun x => u.grad x i - v.grad x i) (volumeOn U) :=
    (u.grad_memL2 i).aestronglyMeasurable.sub (v.grad_memL2 i).aestronglyMeasurable
  have hv : AEStronglyMeasurable (fun x => u.toFun x - v.toFun x) (volumeOn U) :=
    u.memL2.aestronglyMeasurable.sub v.memL2.aestronglyMeasurable
  have h1 : AEStronglyMeasurable (fun x => η x * (u.grad x i - v.grad x i)) (volumeOn U) :=
    (hη.continuous hL).aestronglyMeasurable.mul hg
  have h2 : AEStronglyMeasurable (fun x => (u.toFun x - v.toFun x) * Dη x) (volumeOn U) :=
    hv.mul hDm
  rw [heq]
  refine (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (add_le_add ?_ ?_)
  · refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul h1 (Eventually.of_forall fun x => ?_) 2
    simp only [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hM x) (abs_nonneg _)
  · refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul h2 ?_ 2
    filter_upwards [hDb] with x hx
    rw [norm_mul, mul_comm L]
    exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)

/-- The Lipschitz product stays in `H¹₀`: `η u ∈ H¹₀(U)` for `u ∈ H¹₀(U)` and bounded
Lipschitz `η`. -/
theorem memH10_mulLip (hU : IsOpen U) (u : H10Function U) {L M : ℝ} {η : Vec d → ℝ}
    (hη : EucLip L η) (hL : 0 ≤ L) (hM : ∀ x, |η x| ≤ M) :
    MemH10 U (mulLip hU u.toH1Function hη hL hM).toFun := by
  let φ : ℕ → H10Function U := fun n =>
    H10Function.ofContDiff hU (u.approx_smooth n) (u.approx_hasCompactSupport n)
      (u.approx_support_subset n)
  have hφfun : ∀ n, (φ n).toH1Function.toFun = u.approx n := fun n => rfl
  have hφgrad : ∀ n i x, (φ n).toH1Function.grad x i = fderiv ℝ (u.approx n) x (basisVec i) :=
    fun n i x => rfl
  have hval : Tendsto (fun n => eLpNorm (fun x => u.toH1Function.toFun x - (φ n).toH1Function.toFun x)
      2 (volumeOn U)) atTop (𝓝 0) :=
    u.tendsto_approx.congr fun n => eLpNorm_sub_swap _ _
  have hgr : ∀ i, Tendsto (fun n => eLpNorm (fun x => u.toH1Function.grad x i -
      (φ n).toH1Function.grad x i) 2 (volumeOn U)) atTop (𝓝 0) := fun i =>
    (u.tendsto_approx_grad i).congr fun n => eLpNorm_sub_swap _ _
  refine memH10_of_tendsto_H1 hU (mulLip hU u.toH1Function hη hL hM)
    (fun n => mulLip hU (φ n).toH1Function hη hL hM) (fun n => ?_) ?_ (fun i => ?_)
  · exact ⟨toH10OfCompact hU (mulLip hU (φ n).toH1Function hη hL hM)
      (u.approx_support_subset n) (u.approx_hasCompactSupport n)
      (fun x _ hx => by simp [mulLip, hφfun, image_eq_zero_of_notMem_tsupport hx]), rfl⟩
  · have hb : Tendsto (fun n => ENNReal.ofReal M * eLpNorm (fun x => u.toH1Function.toFun x -
        (φ n).toH1Function.toFun x) 2 (volumeOn U)) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hval (Or.inr ENNReal.ofReal_ne_top)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun n => bot_le)
      (fun n => eLpNorm_mulLip_sub_value_le hU _ _ hη hL hM)
  · have hb1 : Tendsto (fun n => ENNReal.ofReal M * eLpNorm (fun x => u.toH1Function.grad x i -
        (φ n).toH1Function.grad x i) 2 (volumeOn U)) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul (hgr i) (Or.inr ENNReal.ofReal_ne_top)
    have hb2 : Tendsto (fun n => ENNReal.ofReal L * eLpNorm (fun x => u.toH1Function.toFun x -
        (φ n).toH1Function.toFun x) 2 (volumeOn U)) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hval (Or.inr ENNReal.ofReal_ne_top)
    have hb := hb1.add hb2
    rw [add_zero] at hb
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun n => bot_le)
      (fun n => eLpNorm_mulLip_sub_grad_le hU _ _ hη hL hM i)

/-- `H¹₀`-valued Lipschitz product. -/
noncomputable def mulLipOfH10 (hU : IsOpen U) (u : H10Function U) {L M : ℝ} {η : Vec d → ℝ}
    (hη : EucLip L η) (hL : 0 ≤ L) (hM : ∀ x, |η x| ≤ M) : H10Function U :=
  ofMemH10 hU (mulLip hU u.toH1Function hη hL hM) (memH10_mulLip hU u hη hL hM)

end PDE.Ch4Infra
