module

public import PDEFoundation.Sobolev.Inequalities.ConvexSobolevPoincareNormalizedStep2Bounded

/-!
# Step 2: functions vanishing on half of a normalized domain, `1 ≤ p < d`

The bounded case is extended to all nonnegative `v ∈ W^{1,p}(W)` by monotone convergence applied
to the truncations `min (v, n)`.  For `p = 1` the statement is Step 1.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE

variable {d : ℕ} {W : Set (Vec d)}

/-- **Step 2** for `1 < p < d` (Theorem 1.9):
`‖v‖_{L^{p*}(W)} ≤ K_d γ_p ‖∇ v‖_{L^p(W)}`. -/
theorem eLpNormOn_halfZero_le_of_lt (hd : 2 ≤ d) {p : ℝ} (hp : 1 < p) (hpd : p < d)
    (hW : IsOpenBoundedConvexDomain W) (h1 : euclideanBall (0 : Vec d) 1 ⊆ W)
    (hR : W ⊆ euclideanBall (0 : Vec d) (convexNormalizationRadius d))
    (v : W1pFunction W (ENNReal.ofReal p)) (hv0 : ∀ x, 0 ≤ v.toFun x)
    (hhalf : volume W ≤ 2 * volumeOn W {x | v.toFun x = 0}) :
    eLpNormOn W (ENNReal.ofReal (sobolevConjugate d p)) v.toFun ≤
      ENNReal.ofReal (halfZeroConstant d * sobolevGamma d p) *
        euclideanFieldELpNormOn W (ENNReal.ofReal p) v.grad := by
  have hP1 : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  have hPtop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hqs0 : 0 < sobolevConjugate d p := sobolevConjugate_pos (by linarith) hpd
  set qs := sobolevConjugate d p with hqsdef
  set Gp := euclideanFieldELpNormOn W (ENNReal.ofReal p) v.grad with hGp
  set B : ℝ≥0∞ := (ENNReal.ofReal (halfZeroConstant d * sobolevGamma d p) * Gp) ^ qs with hB
  let vn : ℕ → W1pFunction W (ENNReal.ofReal p) := fun n =>
    v.minConst hW hP1 hPtop ((n : ℝ) + 1)
  have hvn_fun : ∀ n x, (vn n).toFun x = min (v.toFun x) ((n : ℝ) + 1) := fun n x => by
    change (v.minConst hW hP1 hPtop ((n : ℝ) + 1)).toFun x = _
    rw [W1pFunction.minConst_toFun]
  have hbound : ∀ n : ℕ, ∫⁻ x, ENNReal.ofReal ((vn n).toFun x) ^ qs ∂(volumeOn W) ≤ B := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hvn0 : ∀ x, 0 ≤ (vn n).toFun x := fun x => by
      rw [hvn_fun]; exact le_min (hv0 x) hn.le
    have hvnle : ∀ x, (vn n).toFun x ≤ (n : ℝ) + 1 := fun x => by
      rw [hvn_fun]; exact min_le_right _ _
    have hsub : {x | v.toFun x = 0} ⊆ {x | (vn n).toFun x = 0} := by
      intro x hx
      have hx' : v.toFun x = 0 := hx
      show (vn n).toFun x = 0
      rw [hvn_fun, hx']
      exact min_eq_left hn.le
    have hhalf' : volume W ≤ 2 * volumeOn W {x | (vn n).toFun x = 0} :=
      hhalf.trans (mul_le_mul' le_rfl (measure_mono hsub))
    refine (lintegral_rpow_le_of_bounded hd hp hpd hW h1 hR (vn n) hvn0 hn hvnle hhalf').trans ?_
    refine ENNReal.rpow_le_rpow (mul_le_mul' le_rfl ?_) hqs0.le
    unfold euclideanFieldELpNormOn eLpNormOn
    refine eLpNorm_mono (aestronglyMeasurable_vecEuclideanNorm_of_coord fun i =>
      ((vn n).grad_memLp i).aestronglyMeasurable) fun x => ?_
    change ‖vecEuclideanNorm ((v.minConst hW hP1 hPtop ((n : ℝ) + 1)).grad x)‖ ≤ _
    rw [W1pFunction.minConst_grad]
    have hnn : 0 ≤ vecEuclideanNorm (v.grad x) := vecEuclideanNorm_nonneg _
    by_cases hx : v.toFun x < (n : ℝ) + 1
    · have hxm : x ∈ {y | v.toFun y < (n : ℝ) + 1} := hx
      simp only [Set.indicator_of_mem hxm, Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _)]
      exact le_rfl
    · have hxm : x ∉ {y | v.toFun y < (n : ℝ) + 1} := hx
      simp only [Set.indicator_of_notMem hxm, Real.norm_eq_abs,
        abs_of_nonneg (vecEuclideanNorm_nonneg _)]
      have h0 : vecEuclideanNorm (0 : Vec d) = 0 := vecEuclideanNorm_eq_zero_iff.2 rfl
      simpa [h0] using hnn
  have hvm : ∀ n, AEMeasurable (fun x => ENNReal.ofReal ((vn n).toFun x) ^ qs) (volumeOn W) :=
    fun n => (ENNReal.measurable_ofReal.comp_aemeasurable
      (vn n).memLp.aestronglyMeasurable.aemeasurable).pow_const _
  have hmono : ∀ x, Monotone fun n : ℕ => ENNReal.ofReal ((vn n).toFun x) ^ qs := by
    intro x m n hmn
    simp only [hvn_fun]
    have : ((m : ℝ) + 1) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
    gcongr
  have hsup : ∀ x, ENNReal.ofReal (v.toFun x) ^ qs =
      ⨆ n : ℕ, ENNReal.ofReal ((vn n).toFun x) ^ qs := by
    intro x
    refine le_antisymm ?_ (iSup_le fun n => ?_)
    · obtain ⟨n, hn⟩ := exists_nat_ge (v.toFun x)
      refine le_iSup_of_le n ?_
      rw [hvn_fun, min_eq_left (by linarith)]
    · rw [hvn_fun]
      gcongr
      exact min_le_left _ _
  have hlim : ∫⁻ x, ENNReal.ofReal (v.toFun x) ^ qs ∂(volumeOn W) ≤ B := by
    simp_rw [hsup]
    rw [lintegral_iSup' hvm (Filter.Eventually.of_forall hmono)]
    exact iSup_le hbound
  have hfin : eLpNormOn W (ENNReal.ofReal qs) v.toFun =
      (∫⁻ x, ENNReal.ofReal (v.toFun x) ^ qs ∂(volumeOn W)) ^ (1 / qs) := by
    unfold eLpNormOn
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hqs0).ne'
      ENNReal.ofReal_ne_top v.memLp.aestronglyMeasurable, ENNReal.toReal_ofReal hqs0.le]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [Real.enorm_eq_ofReal (hv0 x)]
  rw [hfin]
  calc (∫⁻ x, ENNReal.ofReal (v.toFun x) ^ qs ∂(volumeOn W)) ^ (1 / qs)
      ≤ B ^ (1 / qs) := ENNReal.rpow_le_rpow hlim (by positivity)
    _ = _ := by
      rw [hB, ← ENNReal.rpow_mul, mul_one_div_cancel hqs0.ne', ENNReal.rpow_one]

end PDE
