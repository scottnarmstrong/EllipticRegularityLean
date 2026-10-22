module

public import PDEFoundation.PDE.Ch4.CaccioppoliEnergy
public import PDEFoundation.PDE.DGNM.PositivePart

/-!
# Positive parts of subsolutions on bounded open sets (manuscript Lemma 4.10)

If `w` is subharmonic on a bounded open set `U` then so is `(w - k)₊` for every level `k`.
Open-set version of `PDE.DGNM.subharmonicOn_positivePartSubConst`; the ramp `η_ε` is built from
`positivePartOpen` and the smooth test `ψ` is handled by the Lipschitz product test.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory Filter Topology

namespace PDE.Ch4Infra

variable {d : ℕ} {U : Set (Vec d)} {Λ : ℝ} {a : CoeffField d}

/-- The ramp `min{(w-k)₊/ε, 1}` as an `H¹` function on a bounded open set. -/
noncomputable def levelRampOpen (hU : IsOpen U) (hfin : volume U ≠ ⊤) (w : H1Function U)
    (k ε : ℝ) : H1Function U :=
  ε⁻¹ • (positivePartOpen hU w k (memL2On_positivePart_of_finite w hfin k) -
    positivePartOpen hU w (k + ε) (memL2On_positivePart_of_finite w hfin (k + ε)))

theorem levelRampOpen_toFun (hU : IsOpen U) (hfin : volume U ≠ ⊤) (w : H1Function U)
    (k ε : ℝ) (x : Vec d) :
    (levelRampOpen hU hfin w k ε).toFun x =
      ε⁻¹ * (max (w.toFun x - k) 0 - max (w.toFun x - (k + ε)) 0) := rfl

theorem levelRampOpen_grad (hU : IsOpen U) (hfin : volume U ≠ ⊤) (w : H1Function U)
    (k ε : ℝ) (x : Vec d) :
    (levelRampOpen hU hfin w k ε).grad x =
      ε⁻¹ • ({y | k < w.toFun y}.indicator w.grad x -
        {y | k + ε < w.toFun y}.indicator w.grad x) := rfl

theorem levelRampOpen_nonneg (hU : IsOpen U) (hfin : volume U ≠ ⊤) (w : H1Function U)
    (k : ℝ) {ε : ℝ} (hε : 0 < ε) (x : Vec d) :
    0 ≤ (levelRampOpen hU hfin w k ε).toFun x := by
  rw [levelRampOpen_toFun]
  apply mul_nonneg (inv_nonneg.mpr hε.le)
  have : max (w.toFun x - (k + ε)) 0 ≤ max (w.toFun x - k) 0 :=
    max_le_max (by linarith) le_rfl
  linarith

theorem levelRampOpen_le_one (hU : IsOpen U) (hfin : volume U ≠ ⊤) (w : H1Function U)
    (k : ℝ) {ε : ℝ} (hε : 0 < ε) (x : Vec d) :
    (levelRampOpen hU hfin w k ε).toFun x ≤ 1 := by
  rw [levelRampOpen_toFun]
  have hdiff : max (w.toFun x - k) 0 - max (w.toFun x - (k + ε)) 0 ≤ ε := by
    rcases le_total (w.toFun x - k) 0 with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]
      linarith
    · rw [max_eq_left h]
      have := le_max_left (w.toFun x - (k + ε)) 0
      linarith
  calc ε⁻¹ * (max (w.toFun x - k) 0 - max (w.toFun x - (k + ε)) 0) ≤ ε⁻¹ * ε :=
        mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr hε.le)
    _ = 1 := inv_mul_cancel₀ hε.ne'

theorem tendsto_levelRampOpen (hU : IsOpen U) (hfin : volume U ≠ ⊤) (w : H1Function U)
    (k : ℝ) (x : Vec d) :
    Tendsto (fun n : ℕ => (levelRampOpen hU hfin w k (1 / ((n : ℝ) + 1))).toFun x) atTop
      (𝓝 ({y | k < w.toFun y}.indicator (fun _ => (1 : ℝ)) x)) := by
  by_cases hx : k < w.toFun x
  · have hmem : x ∈ {y | k < w.toFun y} := hx
    rw [Set.indicator_of_mem hmem]
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hεpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hεle : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
    rw [levelRampOpen_toFun, max_eq_left (by linarith), max_eq_left (by linarith)]
    field_simp
    ring
  · have hmem : x ∉ {y | k < w.toFun y} := hx
    rw [Set.indicator_of_notMem hmem]
    apply tendsto_const_nhds.congr'
    filter_upwards with n
    have hεpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    rw [levelRampOpen_toFun, max_eq_right (by linarith [not_lt.mp hx]),
      max_eq_right (by linarith [not_lt.mp hx])]
    ring

theorem vecDot_flux_levelRampOpen_grad_nonneg (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (w : H1Function U) (k : ℝ) {ε : ℝ} (hε : 0 < ε) {A : Mat d}
    (hA : IsEllipticMatrix 1 Λ A) (x : Vec d) :
    0 ≤ vecDot (matVecMul A (w.grad x)) ((levelRampOpen hU hfin w k ε).grad x) := by
  rw [levelRampOpen_grad, DGNM.vecDot_smul_right]
  apply mul_nonneg (inv_nonneg.mpr hε.le)
  have hE : 0 ≤ vecDot (matVecMul A (w.grad x)) (w.grad x) := by
    rw [vecDot_comm]
    exact DGNM.vecDot_matVecMul_self_nonneg hA _
  by_cases h1 : k + ε < w.toFun x
  · have h0 : k < w.toFun x := by linarith
    have hm0 : x ∈ {y | k < w.toFun y} := h0
    have hm1 : x ∈ {y | k + ε < w.toFun y} := h1
    rw [Set.indicator_of_mem hm0, Set.indicator_of_mem hm1, sub_self,
      DGNM.vecDot_zero_right]
  · have hm1 : x ∉ {y | k + ε < w.toFun y} := h1
    rw [Set.indicator_of_notMem hm1, sub_zero]
    by_cases h0 : k < w.toFun x
    · have hm0 : x ∈ {y | k < w.toFun y} := h0
      rw [Set.indicator_of_mem hm0]
      exact hE
    · have hm0 : x ∉ {y | k < w.toFun y} := h0
      rw [Set.indicator_of_notMem hm0, DGNM.vecDot_zero_right]

/-- **Manuscript Lemma 4.10, bounded open sets.** If `w` is subharmonic then `(w - k)₊` is
subharmonic for every level `k`. -/
theorem subharmonicOn_positivePart_open (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {w : H1Function U} (hsub : IsWeakDivergenceFormSubharmonicOn a U w) (k : ℝ) :
    IsWeakDivergenceFormSubharmonicOn a U
      (positivePartOpen hU w k (memL2On_positivePart_of_finite w hfin k)) := by
  rw [DGNM.subharmonicOn_iff]
  intro φ hφ
  have hflux := DGNM.memVectorL2On_matVecMul_of_aemeasurable hU.measurableSet ha hEll
    w.gradMemL2
  have hfluxInt : IntegrableOn
      (fun x => vecDot (matVecMul (a x) (w.grad x)) (φ.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2On hflux φ.grad_memVectorL2On
  set v := positivePartOpen hU w k (memL2On_positivePart_of_finite w hfin k) with hv
  have hpp : (fun x => vecDot (matVecMul (a x) (v.grad x)) (φ.grad x)) =
      fun x => {y | k < w.toFun y}.indicator (fun _ => (1 : ℝ)) x *
        vecDot (matVecMul (a x) (w.grad x)) (φ.grad x) := by
    funext x
    change vecDot (matVecMul (a x) ({y | k < w.toFun y}.indicator w.grad x)) (φ.grad x) = _
    by_cases hx : k < w.toFun x
    · have hm : x ∈ {y | k < w.toFun y} := hx
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, one_mul]
    · have hm : x ∉ {y | k < w.toFun y} := hx
      rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, DGNM.matVecMul_zero',
        DGNM.vecDot_zero_left, zero_mul]
  have hppInt : IntegrableOn (fun x => vecDot (matVecMul (a x) (v.grad x)) (φ.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2On
      (DGNM.memVectorL2On_matVecMul_of_aemeasurable hU.measurableSet ha hEll v.gradMemL2)
      φ.grad_memVectorL2On
  refine ⟨hppInt, ?_⟩
  rw [hpp]
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hεdef
  have hεpos : ∀ n, 0 < ε n := fun n => by positivity
  have hmem : ∀ᵐ x ∂volumeOn U, x ∈ U :=
    (ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall fun _ hx => hx)
  -- Lipschitz data of the smooth test function
  obtain ⟨Kφ, hKφ0, hKφ⟩ := EucLip.of_contDiff_hasCompactSupport
    (φ.contDiff.of_le (by simp)) φ.hasCompactSupport
  obtain ⟨Bφ, hBφ⟩ := φ.contDiff.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hBφ' : ∀ x, |φ x| ≤ Bφ := fun x => by simpa using hBφ x
  have hstep : ∀ n, ∫ x in U, (levelRampOpen hU hfin w k (ε n)).toFun x *
      vecDot (matVecMul (a x) (w.grad x)) (φ.grad x) ≤ 0 := by
    intro n
    obtain ⟨h1, h2, hle⟩ := subharmonic_productTest_lip hU hfin ha hEll hsub
      (levelRampOpen hU hfin w k (ε n))
      (Eventually.of_forall fun x => levelRampOpen_nonneg hU hfin w k (hεpos n) x)
      hKφ hKφ0 hBφ' φ.hasCompactSupport φ.tsupport_subset hφ
    have hfirst : 0 ≤ ∫ x in U, φ x *
        vecDot (matVecMul (a x) (w.grad x)) ((levelRampOpen hU hfin w k (ε n)).grad x) := by
      apply integral_nonneg_of_ae
      filter_upwards [hmem] with x hx
      exact mul_nonneg (hφ x)
        (vecDot_flux_levelRampOpen_grad_nonneg hU hfin w k (hεpos n) (hEll x hx) x)
    change (∫ x in U, φ x * vecDot (matVecMul (a x) (w.grad x))
        ((levelRampOpen hU hfin w k (ε n)).grad x)) +
      ∫ x in U, (levelRampOpen hU hfin w k (ε n)).toFun x *
        vecDot (matVecMul (a x) (w.grad x)) (classicalGradient φ x) ≤ 0 at hle
    have hgrad : ∀ x, classicalGradient φ x = φ.grad x := fun x => rfl
    simp only [hgrad] at hle
    linarith
  have hlim : Tendsto (fun n => ∫ x in U, (levelRampOpen hU hfin w k (ε n)).toFun x *
      vecDot (matVecMul (a x) (w.grad x)) (φ.grad x)) atTop
      (𝓝 (∫ x in U, {y | k < w.toFun y}.indicator (fun _ => (1 : ℝ)) x *
        vecDot (matVecMul (a x) (w.grad x)) (φ.grad x))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => |vecDot (matVecMul (a x) (w.grad x)) (φ.grad x)|) ?_ hfluxInt.abs ?_ ?_
    · intro n
      have hmeas : AEStronglyMeasurable (levelRampOpen hU hfin w k (ε n)).toFun (volumeOn U) :=
        (levelRampOpen hU hfin w k (ε n)).memL2.aestronglyMeasurable
      exact hmeas.mul hfluxInt.aestronglyMeasurable
    · intro n
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul]
      have h0 := levelRampOpen_nonneg hU hfin w k (hεpos n) x
      have h1 := levelRampOpen_le_one hU hfin w k (hεpos n) x
      rw [abs_of_nonneg h0]
      exact mul_le_of_le_one_left (abs_nonneg _) h1
    · filter_upwards with x
      exact (tendsto_levelRampOpen hU hfin w k x).mul_const _
  exact le_of_tendsto' hlim hstep

/-- For a superharmonic `u` on a bounded open set, `(k - u)₊ = (-u - (-k))₊` is subharmonic. -/
theorem subharmonicOn_negativePart_open (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u) (k : ℝ) :
    IsWeakDivergenceFormSubharmonicOn a U
      (positivePartOpen hU (-u) (-k) (memL2On_positivePart_of_finite (-u) hfin (-k))) :=
  subharmonicOn_positivePart_open hU hfin ha hEll (DGNM.subharmonicOn_neg hsuper) (-k)

end PDE.Ch4Infra
