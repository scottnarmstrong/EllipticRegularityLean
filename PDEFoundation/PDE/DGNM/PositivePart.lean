module

public import PDEFoundation.PDE.DGNM.ClassAlgebra
public import PDEFoundation.PDE.DGNM.ProductTest
public import PDEFoundation.Sobolev.H1.DerivedTruncations

/-!
# Positive parts of subsolutions (manuscript Lemma 4.10)

If `w` is subharmonic then so is `(w - k)₊` for every level `k`.

Following the manuscript, for `ε > 0` let
`η_ε = min{(w-k)₊/ε, 1} = ε⁻¹ ((w-k)₊ - (w-k-ε)₊) ∈ H¹`, so that
`0 ≤ η_ε ≤ 1` and `∇η_ε = ε⁻¹ 1_{k < w ≤ k+ε} ∇w`. Testing the inequality for
`w` with `ψ η_ε` (`ψ` a nonnegative smooth test) gives
`∫ η_ε a∇w·∇ψ ≤ -∫ ψ a∇w·∇η_ε ≤ 0`, and dominated convergence as `ε → 0`
gives `∫ a∇(w-k)₊·∇ψ ≤ 0`.
-/

@[expose] public section

namespace PDE

namespace DGNM

open MeasureTheory Filter Topology

variable {d : ℕ} {U : Set (Vec d)} {Λ : ℝ} {a : CoeffField d}

/-- The manuscript's truncation `min{(w-k)₊/ε, 1}` as an `H¹` function. -/
noncomputable def levelRamp (hU : IsOpenBoundedConvexDomain U) (w : H1Function U)
    (k ε : ℝ) : H1Function U :=
  ε⁻¹ • (w.positivePartSubConst hU k - w.positivePartSubConst hU (k + ε))

theorem levelRamp_toFun (hU : IsOpenBoundedConvexDomain U) (w : H1Function U)
    (k ε : ℝ) (x : Vec d) :
    (levelRamp hU w k ε).toFun x =
      ε⁻¹ * (max (w x - k) 0 - max (w x - (k + ε)) 0) :=
  rfl

theorem levelRamp_grad (hU : IsOpenBoundedConvexDomain U) (w : H1Function U)
    (k ε : ℝ) (x : Vec d) :
    (levelRamp hU w k ε).grad x =
      ε⁻¹ • ({y | k < w y}.indicator w.grad x -
        {y | k + ε < w y}.indicator w.grad x) :=
  rfl

theorem levelRamp_nonneg (hU : IsOpenBoundedConvexDomain U) (w : H1Function U)
    (k : ℝ) {ε : ℝ} (hε : 0 < ε) (x : Vec d) :
    0 ≤ (levelRamp hU w k ε).toFun x := by
  rw [levelRamp_toFun]
  apply mul_nonneg (inv_nonneg.mpr hε.le)
  have : max (w x - (k + ε)) 0 ≤ max (w x - k) 0 :=
    max_le_max (by linarith) le_rfl
  linarith

theorem levelRamp_le_one (hU : IsOpenBoundedConvexDomain U) (w : H1Function U)
    (k : ℝ) {ε : ℝ} (hε : 0 < ε) (x : Vec d) :
    (levelRamp hU w k ε).toFun x ≤ 1 := by
  rw [levelRamp_toFun]
  have hdiff : max (w x - k) 0 - max (w x - (k + ε)) 0 ≤ ε := by
    rcases le_total (w x - k) 0 with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]
      linarith
    · rw [max_eq_left h]
      have := le_max_left (w x - (k + ε)) 0
      linarith
  calc ε⁻¹ * (max (w x - k) 0 - max (w x - (k + ε)) 0) ≤ ε⁻¹ * ε :=
        mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr hε.le)
    _ = 1 := inv_mul_cancel₀ hε.ne'

/-- Pointwise limit of the ramps: `η_ε(x) → 1_{w > k}(x)`. -/
theorem tendsto_levelRamp (hU : IsOpenBoundedConvexDomain U) (w : H1Function U)
    (k : ℝ) (x : Vec d) :
    Tendsto (fun n : ℕ => (levelRamp hU w k (1 / ((n : ℝ) + 1))).toFun x) atTop
      (𝓝 ({y | k < w y}.indicator (fun _ => (1 : ℝ)) x)) := by
  by_cases hx : k < w x
  · have hmem : x ∈ {y | k < w y} := hx
    rw [Set.indicator_of_mem hmem]
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hεpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hεle : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
    rw [levelRamp_toFun, max_eq_left (by linarith), max_eq_left (by linarith)]
    field_simp
    ring
  · have hmem : x ∉ {y | k < w y} := hx
    rw [Set.indicator_of_notMem hmem]
    apply tendsto_const_nhds.congr'
    filter_upwards with n
    have hεpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    rw [levelRamp_toFun, max_eq_right (by linarith [not_lt.mp hx]),
      max_eq_right (by linarith [not_lt.mp hx])]
    ring

/-- The ramp gradient tested against the flux is nonnegative. -/
theorem vecDot_flux_levelRamp_grad_nonneg (hU : IsOpenBoundedConvexDomain U)
    (w : H1Function U) (k : ℝ) {ε : ℝ} (hε : 0 < ε) {A : Mat d}
    (hA : IsEllipticMatrix 1 Λ A) (x : Vec d) :
    0 ≤ vecDot (matVecMul A (w.grad x)) ((levelRamp hU w k ε).grad x) := by
  rw [levelRamp_grad, vecDot_smul_right]
  apply mul_nonneg (inv_nonneg.mpr hε.le)
  have hE : 0 ≤ vecDot (matVecMul A (w.grad x)) (w.grad x) := by
    rw [vecDot_comm]
    exact vecDot_matVecMul_self_nonneg hA _
  by_cases h1 : k + ε < w x
  · have h0 : k < w x := by linarith
    have hm0 : x ∈ {y | k < w y} := h0
    have hm1 : x ∈ {y | k + ε < w y} := h1
    rw [Set.indicator_of_mem hm0, Set.indicator_of_mem hm1, sub_self,
      vecDot_zero_right]
  · have hm1 : x ∉ {y | k + ε < w y} := h1
    rw [Set.indicator_of_notMem hm1, sub_zero]
    by_cases h0 : k < w x
    · have hm0 : x ∈ {y | k < w y} := h0
      rw [Set.indicator_of_mem hm0]
      exact hE
    · have hm0 : x ∉ {y | k < w y} := h0
      rw [Set.indicator_of_notMem hm0, vecDot_zero_right]

/-- **Manuscript Lemma 4.10.** If `w` is subharmonic (predicate, a.e.
measurable elliptic coefficients), then `(w - k)₊` is subharmonic for every
level `k`. -/
theorem subharmonicOn_positivePartSubConst (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {w : H1Function U} (hsub : IsWeakDivergenceFormSubharmonicOn a U w) (k : ℝ) :
    IsWeakDivergenceFormSubharmonicOn a U (w.positivePartSubConst hU k) := by
  rw [subharmonicOn_iff]
  intro φ hφ
  have hflux := memVectorL2On_matVecMul_of_aemeasurable hU.measurableSet ha hEll
    w.gradMemL2
  have hfluxInt : IntegrableOn
      (fun x => vecDot (matVecMul (a x) (w.grad x)) (φ.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2On hflux φ.grad_memVectorL2On
  -- the tested flux of `(w-k)₊`
  have hpp : (fun x => vecDot (matVecMul (a x)
      ((w.positivePartSubConst hU k).grad x)) (φ.grad x)) =
      fun x => {y | k < w y}.indicator (fun _ => (1 : ℝ)) x *
        vecDot (matVecMul (a x) (w.grad x)) (φ.grad x) := by
    funext x
    rw [H1Function.positivePartSubConst_grad]
    dsimp only
    by_cases hx : k < w x
    · have hm : x ∈ {y | k < w y} := hx
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, one_mul]
    · have hm : x ∉ {y | k < w y} := hx
      rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, matVecMul_zero',
        vecDot_zero_left, zero_mul]
  have hppInt : IntegrableOn (fun x => vecDot (matVecMul (a x)
      ((w.positivePartSubConst hU k).grad x)) (φ.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2On
      (memVectorL2On_matVecMul_of_aemeasurable hU.measurableSet ha hEll
        (w.positivePartSubConst hU k).gradMemL2) φ.grad_memVectorL2On
  refine ⟨hppInt, ?_⟩
  rw [hpp]
  -- ε-approximation
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hεdef
  have hεpos : ∀ n, 0 < ε n := fun n => by positivity
  have hmem : ∀ᵐ x ∂volumeOn U, x ∈ U :=
    (ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall fun _ hx => hx)
  have hstep : ∀ n, ∫ x in U, (levelRamp hU w k (ε n)).toFun x *
      vecDot (matVecMul (a x) (w.grad x)) (φ.grad x) ≤ 0 := by
    intro n
    obtain ⟨h1, h2, hle⟩ := subharmonic_productTest hU ha hEll hsub
      (levelRamp hU w k (ε n))
      (Eventually.of_forall fun x => levelRamp_nonneg hU w k (hεpos n) x)
      φ.contDiff φ.hasCompactSupport φ.tsupport_subset hφ
    have hfirst : 0 ≤ ∫ x in U, φ x *
        vecDot (matVecMul (a x) (w.grad x)) ((levelRamp hU w k (ε n)).grad x) := by
      apply integral_nonneg_of_ae
      filter_upwards [hmem] with x hx
      exact mul_nonneg (hφ x)
        (vecDot_flux_levelRamp_grad_nonneg hU w k (hεpos n) (hEll x hx) x)
    change (∫ x in U, φ x * vecDot (matVecMul (a x) (w.grad x))
        ((levelRamp hU w k (ε n)).grad x)) +
      ∫ x in U, (levelRamp hU w k (ε n)).toFun x *
        vecDot (matVecMul (a x) (w.grad x)) (φ.grad x) ≤ 0 at hle
    linarith
  have hlim : Tendsto (fun n => ∫ x in U, (levelRamp hU w k (ε n)).toFun x *
      vecDot (matVecMul (a x) (w.grad x)) (φ.grad x)) atTop
      (𝓝 (∫ x in U, {y | k < w y}.indicator (fun _ => (1 : ℝ)) x *
        vecDot (matVecMul (a x) (w.grad x)) (φ.grad x))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => |vecDot (matVecMul (a x) (w.grad x)) (φ.grad x)|) ?_ hfluxInt.abs ?_ ?_
    · intro n
      have hmeas : AEStronglyMeasurable (levelRamp hU w k (ε n)).toFun (volumeOn U) :=
        (levelRamp hU w k (ε n)).memL2.aestronglyMeasurable
      exact hmeas.mul hfluxInt.aestronglyMeasurable
    · intro n
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul]
      have h0 := levelRamp_nonneg hU w k (hεpos n) x
      have h1 := levelRamp_le_one hU w k (hεpos n) x
      rw [abs_of_nonneg h0]
      exact mul_le_of_le_one_left (abs_nonneg _) h1
    · filter_upwards with x
      exact (tendsto_levelRamp hU w k x).mul_const _
  exact le_of_tendsto' hlim hstep

/-- For a superharmonic `u`, the negative part `(k - u)₊` is subharmonic. -/
theorem subharmonicOn_negativePartConstSub (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u) (k : ℝ) :
    IsWeakDivergenceFormSubharmonicOn a U (u.negativePartConstSub hU k) :=
  subharmonicOn_positivePartSubConst hU ha hEll (subharmonicOn_neg hsuper) (-k)

end DGNM

end PDE
