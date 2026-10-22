module

public import PDEFoundation.Sobolev.Inequalities.ConvexSobolevPoincareNormalizedStep2
public import PDEFoundation.Sobolev.Inequalities.ConvexSobolevPoincareNormalizedMedian
public import PDEFoundation.Sobolev.Inequalities.ConvexSobolevPoincareNormalizedMean
public import PDEFoundation.Sobolev.W1p.DerivedTruncations
public import PDEFoundation.Sobolev.W1p.Truncation

/-!
# Step 3: the Sobolev--Poincaré inequality on normalized convex domains

For `B₁ ⊆ W ⊆ B_{R_d}` and `1 ≤ p < d`, every `u ∈ W^{1,p}(W)` satisfies
`‖u - (u)_W‖_{\underline L^{p*}(W)} ≤ C' γ_p ‖∇ u‖_{\underline L^p(W)}`
with `C' = 4 K_d |B_{R_d}|^{1/d}`.  The proof takes a median `m` of `u`, applies Step 2 to the
positive and negative parts of `u - m`, and compares the mean to the median by Hölder's inequality.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE

variable {d : ℕ} {W : Set (Vec d)}

/-- Steps 1 and 2 combined (Theorem 1.9 with `p = 1` from
`#halfzeroOne`): for `1 ≤ p < d`, `‖v‖_{L^{p*}(W)} ≤ K_d γ_p ‖∇ v‖_{L^p(W)}`. -/
theorem eLpNormOn_halfZero_le_of_le (hd : 2 ≤ d) {p : ℝ} (hp : 1 ≤ p) (hpd : p < d)
    (hW : IsOpenBoundedConvexDomain W) (h1 : euclideanBall (0 : Vec d) 1 ⊆ W)
    (hR : W ⊆ euclideanBall (0 : Vec d) (convexNormalizationRadius d))
    (v : W1pFunction W (ENNReal.ofReal p)) (hv0 : ∀ x, 0 ≤ v.toFun x)
    (hhalf : volume W ≤ 2 * volumeOn W {x | v.toFun x = 0}) :
    eLpNormOn W (ENNReal.ofReal (sobolevConjugate d p)) v.toFun ≤
      ENNReal.ofReal (halfZeroConstant d * sobolevGamma d p) *
        euclideanFieldELpNormOn W (ENNReal.ofReal p) v.grad := by
  rcases hp.eq_or_lt with h | h
  · subst h
    have e : ENNReal.ofReal 1 = 1 := ENNReal.ofReal_one
    revert v
    rw [e]
    intro v hv0 hhalf
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hγ : sobolevGamma d 1 = 1 := by
      have : (d : ℝ) - 1 ≠ 0 := by linarith
      unfold sobolevGamma
      field_simp
    rw [hγ, mul_one, ← sobolevOneConjugate_eq_sobolevConjugate_one]
    exact eLpNormOn_halfZero_le hd hW h1 hR v hv0 hhalf
  · exact eLpNormOn_halfZero_le_of_lt hd h hpd hW h1 hR v hv0 hhalf

/-- Pointwise domination of Euclidean gradient magnitudes gives domination of the `L^r` norms. -/
theorem euclideanFieldELpNormOn_mono_of_le {F G : Vec d → Vec d} {r : ℝ≥0∞}
    (hF : ∀ i, AEStronglyMeasurable (fun x => F x i) (volumeOn W))
    (h : ∀ x, vecEuclideanNorm (F x) ≤ vecEuclideanNorm (G x)) :
    euclideanFieldELpNormOn W r F ≤ euclideanFieldELpNormOn W r G := by
  unfold euclideanFieldELpNormOn eLpNormOn
  refine eLpNorm_mono (aestronglyMeasurable_vecEuclideanNorm_of_coord hF) fun x => ?_
  simp only [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _)]
  exact h x

/-- The constant `C' = 4 K_d |B_{R_d}|^{1/d}` of Step 3. -/
noncomputable def normalizedSobolevPoincareConstant (d : ℕ) : ℝ :=
  4 * halfZeroConstant d *
    (volume (euclideanBall (0 : Vec d) (convexNormalizationRadius d))).toReal ^ ((d : ℝ)⁻¹)

/-- **Step 3** (Theorem 1.9): the Sobolev--Poincaré inequality on
a normalized convex domain `B₁ ⊆ W ⊆ B_{R_d}`, `1 ≤ p < d`, with the normalized `L^{p*}` and `L^p`
norms and the constant `C' γ_p`, `C' = 4 K_d |B_{R_d}|^{1/d}`. -/
theorem eLpMeanNormOn_sub_integralAverage_le (hd : 2 ≤ d) {p : ℝ} (hp : 1 ≤ p) (hpd : p < d)
    (hW : IsOpenBoundedConvexDomain W) (h1 : euclideanBall (0 : Vec d) 1 ⊆ W)
    (hR : W ⊆ euclideanBall (0 : Vec d) (convexNormalizationRadius d))
    (u : W1pFunction W (ENNReal.ofReal p)) :
    eLpMeanNormOn W (ENNReal.ofReal (sobolevConjugate d p))
        (fun x => u.toFun x - integralAverage W u.toFun) ≤
      ENNReal.ofReal (normalizedSobolevPoincareConstant d * sobolevGamma d p) *
        euclideanFieldELpMeanNormOn W (ENNReal.ofReal p) u.grad := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hfin := hW.isFiniteMeasure_volumeOn
  have hUPos : 0 < volume W :=
    lt_of_lt_of_le (volume_euclideanBall_pos (0 : Vec d) one_pos) (measure_mono h1)
  have hUTop : volume W < ⊤ := hW.volume_lt_top
  have hP1 : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hPtop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hqs0 : 0 < sobolevConjugate d p := sobolevConjugate_pos (by linarith) hpd
  have hqs1 : 1 ≤ sobolevConjugate d p := by
    have : p ≤ sobolevConjugate d p := by
      unfold sobolevConjugate
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    linarith
  have hq1 : 1 ≤ ENNReal.ofReal (sobolevConjugate d p) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hqs1
  have hγ0 : 0 ≤ sobolevGamma d p := by
    unfold sobolevGamma
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hK0 := halfZeroConstant_nonneg d
  set qs := sobolevConjugate d p with hqsdef
  set γ := sobolevGamma d p with hγdef
  set K := halfZeroConstant d with hKdef
  set V := volume W with hV
  set Gu := euclideanFieldELpNormOn W (ENNReal.ofReal p) u.grad with hGu
  -- a median
  have hum : AEMeasurable u.toFun (volumeOn W) := u.memLp.aestronglyMeasurable.aemeasurable
  have huniv : volumeOn W univ = V := Measure.restrict_apply_univ _
  have hne : volumeOn W ≠ 0 := by
    intro h
    have := huniv
    rw [h] at this
    exact hUPos.ne' (by simpa using this.symm)
  obtain ⟨m, hm1, hm2⟩ := exists_median (volumeOn W) hne hum
  rw [huniv] at hm1 hm2
  let vp := u.positivePartSubConst hW hP1 hPtop m
  let vn := u.negativePartConstSub hW hP1 hPtop m
  have hvp0 : ∀ x, 0 ≤ vp.toFun x := fun x => le_max_right _ _
  have hvn0 : ∀ x, 0 ≤ vn.toFun x := fun x => by
    change 0 ≤ (u.negativePartConstSub hW hP1 hPtop m).toFun x
    rw [W1pFunction.negativePartConstSub_toFun]; exact le_max_right _ _
  have hphalf : V ≤ 2 * volumeOn W {x | vp.toFun x = 0} := by
    refine hm1.trans (mul_le_mul' le_rfl (measure_mono fun x hx => ?_))
    have hx' : u.toFun x ≤ m := hx
    change max (u.toFun x - m) 0 = 0
    exact max_eq_right (by linarith)
  have hnhalf : V ≤ 2 * volumeOn W {x | vn.toFun x = 0} := by
    refine hm2.trans (mul_le_mul' le_rfl (measure_mono fun x hx => ?_))
    have hx' : m ≤ u.toFun x := hx
    show (u.negativePartConstSub hW hP1 hPtop m).toFun x = 0
    rw [W1pFunction.negativePartConstSub_toFun]
    exact max_eq_right (by linarith)
  have hp2 := eLpNormOn_halfZero_le_of_le hd hp hpd hW h1 hR vp hvp0 hphalf
  have hn2 := eLpNormOn_halfZero_le_of_le hd hp hpd hW h1 hR vn hvn0 hnhalf
  have hgp : euclideanFieldELpNormOn W (ENNReal.ofReal p) vp.grad ≤ Gu := by
    refine euclideanFieldELpNormOn_mono_of_le (fun i => (vp.grad_memLp i).aestronglyMeasurable)
      fun x => ?_
    change vecEuclideanNorm ({y | m < u.toFun y}.indicator u.grad x) ≤ _
    by_cases hx : m < u.toFun x
    · rw [Set.indicator_of_mem (show x ∈ {y | m < u.toFun y} from hx)]
    · rw [Set.indicator_of_notMem (show x ∉ {y | m < u.toFun y} from hx)]
      have h0 : vecEuclideanNorm (0 : Vec d) = 0 := vecEuclideanNorm_eq_zero_iff.2 rfl
      simp only [h0]
      exact vecEuclideanNorm_nonneg _
  have hgn : euclideanFieldELpNormOn W (ENNReal.ofReal p) vn.grad ≤ Gu := by
    refine euclideanFieldELpNormOn_mono_of_le (fun i => (vn.grad_memLp i).aestronglyMeasurable)
      fun x => ?_
    change vecEuclideanNorm ((u.negativePartConstSub hW hP1 hPtop m).grad x) ≤ _
    rw [W1pFunction.negativePartConstSub_grad]
    beta_reduce
    by_cases hx : u.toFun x < m
    · rw [Set.indicator_of_mem (show x ∈ {y | u.toFun y < m} from hx)]
      change vecEuclideanNorm (-(u.grad x)) ≤ _
      rw [vecEuclideanNorm_neg]
    · rw [Set.indicator_of_notMem (show x ∉ {y | u.toFun y < m} from hx)]
      have h0 : vecEuclideanNorm (0 : Vec d) = 0 := vecEuclideanNorm_eq_zero_iff.2 rfl
      simp only [h0]
      exact vecEuclideanNorm_nonneg _
  -- `‖u - m‖_{L^{p*}(W)} ≤ 2 K γ ‖∇u‖_{L^p(W)}`
  have hum' : eLpNormOn W (ENNReal.ofReal qs) (fun x => u.toFun x - m) ≤
      2 * (ENNReal.ofReal (K * γ) * Gu) := by
    have hpt : ∀ x, ‖u.toFun x - m‖ ≤ ‖(vp.toFun + vn.toFun) x‖ := by
      intro x
      have e1 : vp.toFun x = max (u.toFun x - m) 0 := rfl
      have e2 : vn.toFun x = max (m - u.toFun x) 0 := by
        change (u.negativePartConstSub hW hP1 hPtop m).toFun x = _
        rw [W1pFunction.negativePartConstSub_toFun]
      have hnn : 0 ≤ (vp.toFun + vn.toFun) x := add_nonneg (hvp0 x) (hvn0 x)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn, Pi.add_apply, e1, e2]
      rcases le_total (u.toFun x - m) 0 with h | h
      · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]; linarith
      · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]; linarith
    calc eLpNormOn W (ENNReal.ofReal qs) (fun x => u.toFun x - m)
        ≤ eLpNormOn W (ENNReal.ofReal qs) (vp.toFun + vn.toFun) := by
          unfold eLpNormOn
          exact eLpNorm_mono (u.memLp.aestronglyMeasurable.sub aestronglyMeasurable_const) hpt
      _ ≤ eLpNormOn W (ENNReal.ofReal qs) vp.toFun + eLpNormOn W (ENNReal.ofReal qs) vn.toFun :=
          eLpNorm_add_le hq1
      _ ≤ ENNReal.ofReal (K * γ) * Gu + ENNReal.ofReal (K * γ) * Gu :=
          add_le_add (hp2.trans (by gcongr)) (hn2.trans (by gcongr))
      _ = 2 * (ENNReal.ofReal (K * γ) * Gu) := (two_mul _).symm
  -- normalized norms
  have hνprob : IsProbabilityMeasure (normalizedVolumeOn W) :=
    isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top hUPos hUTop
  have hGufin : Gu ≠ ⊤ := by
    have h := u.gradMemLp.memLp_vecEuclideanNorm.eLpNorm_ne_top
    exact h
  have hfinm : eLpNormOn W (ENNReal.ofReal qs) (fun x => u.toFun x - m) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGufin)) hum'
  have hVinv : V⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hUPos.ne'
  have hmemν : MemLp (fun x => u.toFun x - m) (ENNReal.ofReal qs) (normalizedVolumeOn W) := by
    have h := eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn hUTop (ENNReal.ofReal qs)
      (fun x => u.toFun x - m)
    change eLpMeanNormOn W (ENNReal.ofReal qs) (fun x => u.toFun x - m) < ⊤
    rw [h]
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg hVinv)
      hfinm.lt_top
  have hmemu : MemLp u.toFun (ENNReal.ofReal qs) (normalizedVolumeOn W) := by
    refine (hmemν.add (memLp_const m)).ae_eq (Filter.Eventually.of_forall fun x => ?_)
    simp
  have hmean := eLpNorm_sub_integral_le (normalizedVolumeOn W) hq1 hmemu m
  rw [integral_normalizedVolumeOn_eq_integralAverage] at hmean
  -- volume exponents
  set b : ℝ := (1 / ENNReal.ofReal p).toReal with hbdef
  set a : ℝ := (1 / ENNReal.ofReal qs).toReal with hadef
  have ha : a = -(d : ℝ)⁻¹ + b := toReal_one_div_ofReal_sobolevConjugate (by linarith) hpd
  have hVpow : V⁻¹ ^ a * V ^ b = V ^ (d : ℝ)⁻¹ := by
    rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg, ← ENNReal.rpow_add _ _ hUPos.ne' hUTop.ne, ha]
    congr 1
    ring
  have hGuEq : Gu = V ^ b * euclideanFieldELpMeanNormOn W (ENNReal.ofReal p) u.grad :=
    euclideanFieldELpNormOn_eq_volume_rpow_mul hUPos hUTop _ _
  set Gm := euclideanFieldELpMeanNormOn W (ENNReal.ofReal p) u.grad with hGm
  set Bball := volume (euclideanBall (0 : Vec d) (convexNormalizationRadius d)) with hBball
  have hR0 : 0 ≤ convexNormalizationRadius d := by
    unfold convexNormalizationRadius; positivity
  have hBfin : Bball ≠ ⊤ := volume_euclideanBall_ne_top _ hR0
  have hconst : ENNReal.ofReal (normalizedSobolevPoincareConstant d * γ) =
      4 * ENNReal.ofReal (K * γ) * Bball ^ ((d : ℝ)⁻¹) := by
    have hB0 : 0 ≤ Bball.toReal ^ ((d : ℝ)⁻¹) := Real.rpow_nonneg ENNReal.toReal_nonneg _
    have h : normalizedSobolevPoincareConstant d * γ =
        4 * (K * γ) * (Bball.toReal ^ ((d : ℝ)⁻¹)) := by
      unfold normalizedSobolevPoincareConstant
      rw [← hKdef]
      ring
    rw [h, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by positivity),
      ENNReal.ofReal_toReal hBfin]
    norm_num
  calc eLpMeanNormOn W (ENNReal.ofReal qs) (fun x => u.toFun x - integralAverage W u.toFun)
      ≤ 2 * eLpMeanNormOn W (ENNReal.ofReal qs) (fun x => u.toFun x - m) := hmean
    _ = 2 * (V⁻¹ ^ a * eLpNormOn W (ENNReal.ofReal qs) (fun x => u.toFun x - m)) := by
        rw [eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn hUTop]
    _ ≤ 2 * (V⁻¹ ^ a * (2 * (ENNReal.ofReal (K * γ) * Gu))) := by gcongr
    _ = 4 * ENNReal.ofReal (K * γ) * (V⁻¹ ^ a * V ^ b) * Gm := by
        rw [hGuEq]; ring
    _ = 4 * ENNReal.ofReal (K * γ) * V ^ (d : ℝ)⁻¹ * Gm := by rw [hVpow]
    _ ≤ 4 * ENNReal.ofReal (K * γ) * Bball ^ ((d : ℝ)⁻¹) * Gm := by
        gcongr
        exact measure_mono hR
    _ = ENNReal.ofReal (normalizedSobolevPoincareConstant d * γ) * Gm := by rw [hconst]

theorem halfZeroConstant_pos (hd : 2 ≤ d) : 0 < halfZeroConstant d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 hdpos
  have hR : 0 < convexNormalizationRadius d := by unfold convexNormalizationRadius; positivity
  have hω : 0 < (volume (euclideanBall (0 : Vec d) 1)).toReal :=
    ENNReal.toReal_pos (volume_euclideanBall_pos 0 one_pos).ne'
      (volume_euclideanBall_ne_top 0 zero_le_one)
  unfold halfZeroConstant halfZeroRieszConstant halfZeroWeakConstant
  positivity

theorem normalizedSobolevPoincareConstant_pos (hd : 2 ≤ d) :
    0 < normalizedSobolevPoincareConstant d := by
  have hR : 0 < convexNormalizationRadius d := by
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 hdpos
    unfold convexNormalizationRadius; positivity
  have hB : 0 < (volume (euclideanBall (0 : Vec d) (convexNormalizationRadius d))).toReal :=
    ENNReal.toReal_pos (volume_euclideanBall_pos 0 hR).ne'
      (volume_euclideanBall_ne_top 0 hR.le)
  have := halfZeroConstant_pos hd
  unfold normalizedSobolevPoincareConstant
  positivity

/-- **Steps 1-3, existential form.** There is a constant depending only on the dimension such that
the Sobolev--Poincaré inequality with normalized norms holds on every normalized convex domain,
for every `1 ≤ p < d`, with the factor `γ_p = p (d - 1) / (d - p)`. -/
theorem exists_normalizedSobolevPoincare_constant (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 1 ≤ p → p < d → ∀ W : Set (Vec d),
      IsOpenBoundedConvexDomain W → euclideanBall (0 : Vec d) 1 ⊆ W →
      W ⊆ euclideanBall (0 : Vec d) (convexNormalizationRadius d) →
      ∀ u : W1pFunction W (ENNReal.ofReal p),
        eLpMeanNormOn W (ENNReal.ofReal (sobolevConjugate d p))
            (fun x => u.toFun x - integralAverage W u.toFun) ≤
          ENNReal.ofReal (C * (p * ((d : ℝ) - 1) / ((d : ℝ) - p))) *
            euclideanFieldELpMeanNormOn W (ENNReal.ofReal p) u.grad :=
  ⟨normalizedSobolevPoincareConstant d, normalizedSobolevPoincareConstant_pos hd,
    fun _ hp hpd _ hW h1 hR u => eLpMeanNormOn_sub_integralAverage_le hd hp hpd hW h1 hR u⟩

end PDE
