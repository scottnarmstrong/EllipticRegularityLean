module

public import PDEFoundation.Monotonicity.ACF.WeightedTestIneq

/-!
# Removing the regularization: `ε → 0`

Dominated convergence for the right-hand side `½ ∫ u² T_ε(|x|²)` and Fatou's lemma for the
left-hand side `∫ Ψ_ε(|x|²) |∇u|²` give

`∫⁻ ofReal (|x|^{2-d} Z(|x|²) |∇u|²) ≤ ofReal (½ ∫ u² T_0(|x|²))`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace PDE

noncomputable section

variable {r k κ ε : ℝ}

theorem tendsto_acfQ {s : ℝ} (hs : 0 < s) :
    Tendsto (fun ε => acfQ κ ε s) (𝓝 0) (𝓝 (acfQ κ 0 s)) := by
  have : ContinuousAt (fun ε : ℝ => acfQ κ ε s) 0 := by
    unfold acfQ
    exact (continuousAt_const.add (continuousAt_id.pow 2)).rpow_const
      (Or.inl (by simpa using hs.ne'))
  exact this.tendsto

theorem tendsto_acfQ1 {s : ℝ} (hs : 0 < s) :
    Tendsto (fun ε => acfQ1 κ ε s) (𝓝 0) (𝓝 (acfQ1 κ 0 s)) := by
  have : ContinuousAt (fun ε : ℝ => acfQ1 κ ε s) 0 := by
    unfold acfQ1
    exact continuousAt_const.mul ((continuousAt_const.add (continuousAt_id.pow 2)).rpow_const
      (Or.inl (by simpa using hs.ne')))
  exact this.tendsto

theorem tendsto_acfT {d : ℕ} {s : ℝ} (hs : 0 < s) :
    Tendsto (fun ε => acfT d r k ε s) (𝓝 0) (𝓝 (acfT d r k 0 s)) := by
  unfold acfT
  exact (tendsto_const_nhds.mul ((tendsto_const_nhds.mul (tendsto_acfQ hs)).add
    (tendsto_const_nhds.mul (tendsto_acfQ1 hs)))).add
    ((tendsto_const_nhds.mul (tendsto_acfQ hs)).mul tendsto_const_nhds)

/-- Uniform bound for `T_ε` on `s ≥ 0`. -/
theorem abs_acfT_le {d : ℕ} (hd : 2 ≤ d) (hr : 0 < r) (hk : 0 < k) {C1 C2 : ℝ}
    (hC1 : ∀ s, |deriv (acfCut r k) s| ≤ C1) (hC2 : ∀ s, |deriv (deriv (acfCut r k)) s| ≤ C2)
    {ε s : ℝ} (hε : ε ≠ 0) (hs : 0 ≤ s) :
    |acfT d r k ε s| ≤ C1 * ((2 * d + 8 * acfKappa d) * (r ^ 2) ^ (-acfKappa d)) +
      4 * (r + k) ^ 2 * (r ^ 2) ^ (-acfKappa d) * C2 := by
  have hε2 : 0 < ε ^ 2 := by positivity
  have hC1' : 0 ≤ C1 := (abs_nonneg _).trans (hC1 0)
  have hC2' : 0 ≤ C2 := (abs_nonneg _).trans (hC2 0)
  have hκ := acfKappa_nonneg (d := d) hd
  have hQm : 0 ≤ (r ^ 2) ^ (-acfKappa d) := Real.rpow_nonneg (by positivity) _
  by_cases hcase : s < r ^ 2 ∨ (r + k) ^ 2 < s
  · rw [acfT_eq_zero hr hk hcase, abs_zero]
    have : 0 ≤ C1 * ((2 * d + 8 * acfKappa d) * (r ^ 2) ^ (-acfKappa d)) := by positivity
    have : 0 ≤ 4 * (r + k) ^ 2 * (r ^ 2) ^ (-acfKappa d) * C2 := by positivity
    linarith
  · rw [not_or, not_lt, not_lt] at hcase
    obtain ⟨hs1, hs2⟩ := hcase
    have hpos : 0 < s + ε ^ 2 := by linarith
    have hQpos := acfQ_pos (κ := acfKappa d) hpos
    have hQle : acfQ (acfKappa d) ε s ≤ (r ^ 2) ^ (-acfKappa d) := by
      unfold acfQ
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have hQ1nonpos : acfQ1 (acfKappa d) ε s ≤ 0 := by
      unfold acfQ1
      have := Real.rpow_nonneg hpos.le (-acfKappa d - 1)
      nlinarith
    have hmul := acfQ1_mul_self_eq (κ := acfKappa d) hpos
    have hsQ1 : s * acfQ1 (acfKappa d) ε s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs hQ1nonpos
    have hsQ1' : -(acfKappa d) * acfQ (acfKappa d) ε s ≤ s * acfQ1 (acfKappa d) ε s := by
      nlinarith
    have hdd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hA : |2 * d * acfQ (acfKappa d) ε s + 8 * s * acfQ1 (acfKappa d) ε s| ≤
        (2 * d + 8 * acfKappa d) * (r ^ 2) ^ (-acfKappa d) := by
      rw [abs_le]
      constructor
      · nlinarith
      · nlinarith
    have hB : |4 * s * acfQ (acfKappa d) ε s * deriv (deriv (acfCut r k)) s| ≤
        4 * (r + k) ^ 2 * (r ^ 2) ^ (-acfKappa d) * C2 := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * s * acfQ (acfKappa d) ε s)]
      have hs3 : s ≤ (r + k) ^ 2 := hs2
      exact mul_le_mul (mul_le_mul (by linarith) hQle hQpos.le (by positivity)) (hC2 s)
        (abs_nonneg _) (by positivity)
    unfold acfT
    calc |deriv (acfCut r k) s * (2 * d * acfQ (acfKappa d) ε s +
            8 * s * acfQ1 (acfKappa d) ε s) +
          4 * s * acfQ (acfKappa d) ε s * deriv (deriv (acfCut r k)) s|
        ≤ |deriv (acfCut r k) s * (2 * d * acfQ (acfKappa d) ε s +
            8 * s * acfQ1 (acfKappa d) ε s)| +
          |4 * s * acfQ (acfKappa d) ε s * deriv (deriv (acfCut r k)) s| := abs_add_le _ _
      _ ≤ C1 * ((2 * d + 8 * acfKappa d) * (r ^ 2) ^ (-acfKappa d)) +
          4 * (r + k) ^ 2 * (r ^ 2) ^ (-acfKappa d) * C2 := by
        refine add_le_add ?_ hB
        rw [abs_mul]
        exact mul_le_mul (hC1 s) hA (abs_nonneg _) hC1'

theorem exists_bound_deriv_acfCut (hr : 0 < r) (hk : 0 < k) :
    (∃ C1 : ℝ, ∀ s, |deriv (acfCut r k) s| ≤ C1) ∧
      ∃ C2 : ℝ, ∀ s, |deriv (deriv (acfCut r k)) s| ≤ C2 := by
  have h0 : ContDiff ℝ (⊤ : ℕ∞) (acfCut r k) := contDiff_acfCut hr hk
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (deriv (acfCut r k)) := (contDiff_infty_iff_deriv.mp h0).2
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv (acfCut r k))) := (contDiff_infty_iff_deriv.mp h1).2
  have hcs1 : HasCompactSupport (deriv (acfCut r k)) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := r ^ 2) (b := (r + k) ^ 2)) ?_
    intro s hs
    rw [mem_Icc, not_and_or, not_le, not_le] at hs
    rcases hs with hs | hs
    · exact deriv_acfCut_eq_zero_of_lt hr hk hs
    · exact deriv_acfCut_eq_zero_of_gt hk hs
  have hcs2 : HasCompactSupport (deriv (deriv (acfCut r k))) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := r ^ 2) (b := (r + k) ^ 2)) ?_
    intro s hs
    rw [mem_Icc, not_and_or, not_le, not_le] at hs
    rcases hs with hs | hs
    · exact deriv_deriv_acfCut_eq_zero_of_lt hr hk hs
    · exact deriv_deriv_acfCut_eq_zero_of_gt hk hs
  obtain ⟨C1, hC1⟩ := h1.continuous.norm.bounded_above_of_compact_support hcs1.norm
  obtain ⟨C2, hC2⟩ := h2.continuous.norm.bounded_above_of_compact_support hcs2.norm
  exact ⟨⟨C1, fun s => by simpa using hC1 s⟩, ⟨C2, fun s => by simpa using hC2 s⟩⟩

/-- The right-hand side converges as `ε → 0` (along `ε_n = 1/(n+1)`). -/
theorem tendsto_acfT_integral {d : ℕ} (hd : 3 ≤ d) {R : ℝ} (hr : 0 < r) (hk : 0 < k)
    (u : H1Function (euclideanBall (0 : Vec d) R))
    (hcont : ContinuousOn u.toFun (euclideanBall (0 : Vec d) R)) :
    Tendsto (fun n : ℕ => ∫ x in euclideanBall (0 : Vec d) R,
        u.toFun x ^ 2 * acfT d r k (1 / ((n : ℝ) + 1)) (vecNormSq x)) atTop
      (𝓝 (∫ x in euclideanBall (0 : Vec d) R, u.toFun x ^ 2 * acfT d r k 0 (vecNormSq x))) := by
  obtain ⟨⟨C1, hC1⟩, ⟨C2, hC2⟩⟩ := exists_bound_deriv_acfCut hr hk
  set B : ℝ := C1 * ((2 * d + 8 * acfKappa d) * (r ^ 2) ^ (-acfKappa d)) +
    4 * (r + k) ^ 2 * (r ^ 2) ^ (-acfKappa d) * C2 with hB
  have hεt : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hu2 : IntegrableOn (fun x => u.toFun x ^ 2) (euclideanBall (0 : Vec d) R) :=
    (show MemLp u.toFun 2 (volume.restrict (euclideanBall (0 : Vec d) R)) from
      u.memL2).integrable_sq
  have hmeas : MeasurableSet (euclideanBall (0 : Vec d) R) :=
    (isOpen_euclideanBall (0 : Vec d) R).measurableSet
  refine tendsto_integral_of_dominated_convergence (fun x => B * u.toFun x ^ 2) ?_
    (hu2.const_mul B) ?_ ?_
  · intro n
    have hε0 : (1 / ((n : ℝ) + 1)) ≠ 0 := by positivity
    have hT : Continuous (fun x : Vec d => acfT d r k (1 / ((n : ℝ) + 1)) (vecNormSq x)) :=
      (continuousOn_acfT hr hk hε0).comp_continuous continuous_vecNormSq
        (fun x => vecNormSq_nonneg x)
    exact (((hcont.pow 2).mul hT.continuousOn)).aestronglyMeasurable hmeas
  · intro n
    refine Filter.Eventually.of_forall fun x => ?_
    have hε0 : (1 / ((n : ℝ) + 1)) ≠ 0 := by positivity
    have := abs_acfT_le (d := d) (by omega) hr hk hC1 hC2 hε0 (vecNormSq_nonneg x)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    rw [mul_comm B]
    exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
  · refine Filter.Eventually.of_forall fun x => ?_
    by_cases hcase : vecNormSq x < r ^ 2 ∨ (r + k) ^ 2 < vecNormSq x
    · simp only [acfT_eq_zero hr hk hcase, mul_zero]
      exact tendsto_const_nhds
    · rw [not_or, not_lt, not_lt] at hcase
      have hpos : 0 < vecNormSq x := lt_of_lt_of_le (by positivity) hcase.1
      exact ((tendsto_acfT (d := d) (r := r) (k := k) hpos).comp hεt).const_mul _

/-- **The limit inequality.** -/
theorem acfLimit_inequality {d : ℕ} (hd : 3 ≤ d) {R : ℝ} (hr : 0 < r) (hk : 0 < k)
    (hrk : r + k < R) (u : H1Function (euclideanBall (0 : Vec d) R))
    (hcont : ContinuousOn u.toFun (euclideanBall (0 : Vec d) R))
    (hnonneg : ∀ x ∈ euclideanBall (0 : Vec d) R, 0 ≤ u.toFun x)
    (hsub : IsWeakDivergenceFormSubharmonicOn (fun _ => (1 : Mat d))
      (euclideanBall (0 : Vec d) R) u) :
    ∫⁻ x in euclideanBall (0 : Vec d) R,
        ENNReal.ofReal (acfQ (acfKappa d) 0 (vecNormSq x) * acfCut r k (vecNormSq x) *
          vecNormSq (u.grad x)) ≤
      ENNReal.ofReal ((1 / 2) * ∫ x in euclideanBall (0 : Vec d) R,
        u.toFun x ^ 2 * acfT d r k 0 (vecNormSq x)) := by
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hε
  have hεpos : ∀ n, 0 < ε n := fun n => by simp only [hε]; positivity
  have hεt : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hκpos : acfKappa d ≠ 0 := by
    unfold acfKappa
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    intro h
    linarith
  set f : ℕ → Vec d → ENNReal := fun n x =>
    ENNReal.ofReal (acfPsi (acfKappa d) r k (ε n) (vecNormSq x) * vecNormSq (u.grad x)) with hf
  have htest := fun n => acfTest_inequality hd hr hk hrk (hεpos n) u hcont hnonneg hsub
  have hf_meas : ∀ n, AEMeasurable (f n) (volume.restrict (euclideanBall (0 : Vec d) R)) :=
    fun n => ((htest n).1.aestronglyMeasurable.aemeasurable).ennreal_ofReal
  have hf_le : ∀ n, ∫⁻ x in euclideanBall (0 : Vec d) R, f n x ≤
      ENNReal.ofReal ((1 / 2) * ∫ x in euclideanBall (0 : Vec d) R,
        u.toFun x ^ 2 * acfT d r k (ε n) (vecNormSq x)) := by
    intro n
    have hnn : 0 ≤ᵐ[volume.restrict (euclideanBall (0 : Vec d) R)]
        fun x => acfPsi (acfKappa d) r k (ε n) (vecNormSq x) * vecNormSq (u.grad x) :=
      Filter.Eventually.of_forall fun x =>
        mul_nonneg (acfPsi_nonneg (hεpos n).ne' (vecNormSq_nonneg x)) (vecNormSq_nonneg _)
    rw [← ofReal_integral_eq_lintegral_ofReal (htest n).1 hnn]
    exact ENNReal.ofReal_le_ofReal (htest n).2
  have hpt : ∀ x : Vec d, ENNReal.ofReal (acfQ (acfKappa d) 0 (vecNormSq x) *
      acfCut r k (vecNormSq x) * vecNormSq (u.grad x)) ≤ liminf (fun n => f n x) atTop := by
    intro x
    rcases (vecNormSq_nonneg x).eq_or_lt with h0 | hpos
    · have : acfQ (acfKappa d) 0 (vecNormSq x) = 0 := by
        unfold acfQ
        rw [← h0]
        simpa using Real.zero_rpow (neg_ne_zero.mpr hκpos)
      rw [this]; simp
    · have hfn : ∀ n, f n x = ENNReal.ofReal (acfQ (acfKappa d) (ε n) (vecNormSq x) *
          acfCut r k (vecNormSq x) * vecNormSq (u.grad x)) := by
        intro n
        have hth : acfTheta (ε n) (vecNormSq x) = 1 :=
          acfTheta_eq_one (by have h1 := sq_nonneg (ε n); have h2 := vecNormSq_nonneg x; linarith)
            (hεpos n).ne'
        simp only [hf, acfPsi, hth, mul_one]
      have hlim : Tendsto (fun n => f n x) atTop (𝓝 (ENNReal.ofReal
          (acfQ (acfKappa d) 0 (vecNormSq x) * acfCut r k (vecNormSq x) *
            vecNormSq (u.grad x)))) := by
        simp only [hfn]
        refine ENNReal.tendsto_ofReal ?_
        exact (((tendsto_acfQ hpos).comp hεt).mul_const _).mul_const _
      exact (hlim.liminf_eq).ge
  have hI := tendsto_acfT_integral hd hr hk u hcont
  calc ∫⁻ x in euclideanBall (0 : Vec d) R, ENNReal.ofReal (acfQ (acfKappa d) 0 (vecNormSq x) *
          acfCut r k (vecNormSq x) * vecNormSq (u.grad x))
      ≤ ∫⁻ x in euclideanBall (0 : Vec d) R, liminf (fun n => f n x) atTop :=
        lintegral_mono hpt
    _ ≤ liminf (fun n => ∫⁻ x in euclideanBall (0 : Vec d) R, f n x) atTop :=
        lintegral_liminf_le' hf_meas
    _ ≤ liminf (fun n => ENNReal.ofReal ((1 / 2) * ∫ x in euclideanBall (0 : Vec d) R,
          u.toFun x ^ 2 * acfT d r k (ε n) (vecNormSq x))) atTop :=
        liminf_le_liminf (Filter.Eventually.of_forall hf_le)
    _ = ENNReal.ofReal ((1 / 2) * ∫ x in euclideanBall (0 : Vec d) R,
          u.toFun x ^ 2 * acfT d r k 0 (vecNormSq x)) :=
        (ENNReal.tendsto_ofReal (hI.const_mul (1 / 2))).liminf_eq

end

end PDE
