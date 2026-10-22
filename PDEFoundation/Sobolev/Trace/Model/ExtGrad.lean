module

public import PDEFoundation.Sobolev.Trace.Model.ExtPointwise

/-!
# Pointwise control of the energy density of the extension

For `t > 0` the sum `|E g|^p + |∇ E g|^p` at `(x, t)` is bounded by
`C₁ · Φ(x, t) + C₂ · Ψ(x, t)` (for `t ≤ 1`, and `0` for `t > 1`), where `Φ` is the ball
oscillation of `g` with weight `t^{-(n+p)}` and `Ψ` is the Jensen average of `|g|^p`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {n : ℕ}

/-- The ball-oscillation majorant `t^{-(n+p)} ∫_{B(x,t)} |g y - g x|^p dy`. -/
noncomputable def extPhi (n : ℕ) (p : ℝ) (g : Vec n → ℝ) (x : Vec n) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (t ^ (-((n : ℝ) + p))) *
    ∫⁻ y, (eBallSet n x t).indicator (fun y => ENNReal.ofReal (|g y - g x| ^ p)) y

/-- The Jensen majorant `∫ K(x - y, t) |g y|^p dy`. -/
noncomputable def extPsi (n : ℕ) (p : ℝ) (g : Vec n → ℝ) (x : Vec n) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (dil n (extKernel n) (x - y) t) * ENNReal.ofReal (|g y| ^ p)

theorem enn_combine {p : ℝ} (hp : 1 ≤ p) {N R c a B Q : ℝ≥0∞} (hR : R ^ p ≤ B) (ha : a ^ p ≤ Q) :
    (N * R + c * a) ^ p ≤ 2 ^ (p - 1) * (N ^ p * B + c ^ p * Q) := by
  have hp0 : 0 ≤ p := by linarith
  refine (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp).trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0, ENNReal.mul_rpow_of_nonneg _ _ hp0]
  gcongr

theorem enn_consts {p : ℝ} (hp : 1 < p) (n : ℕ) {c0 Cχ : ℝ} (hCχ : 0 ≤ Cχ)
    (Φ Ψ : ℝ≥0∞) :
    Ψ + 2 ^ (p - 1) * (ENNReal.ofReal ((n : ℝ) + 1) ^ p * (ENNReal.ofReal c0 * Φ) +
        ENNReal.ofReal Cχ ^ p * Ψ) =
      ENNReal.ofReal (2 ^ (p - 1) * ((n : ℝ) + 1) ^ p * c0) * Φ +
        ENNReal.ofReal (1 + 2 ^ (p - 1) * Cχ ^ p) * Ψ := by
  have hp1 : 0 ≤ p - 1 := by linarith
  have hp0 : 0 ≤ p := by linarith
  have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have e2 : (2 : ℝ≥0∞) ^ (p - 1) = ENNReal.ofReal (2 ^ (p - 1)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) hp1]
    simp
  have h2 : (0 : ℝ) ≤ 2 ^ (p - 1) := Real.rpow_nonneg (by norm_num) _
  have h3 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ p := Real.rpow_nonneg hn _
  have h4 : (0 : ℝ) ≤ Cχ ^ p := Real.rpow_nonneg hCχ _
  have e3 : ENNReal.ofReal ((n : ℝ) + 1) ^ p = ENNReal.ofReal (((n : ℝ) + 1) ^ p) :=
    ENNReal.ofReal_rpow_of_nonneg hn hp0
  have e4 : ENNReal.ofReal Cχ ^ p = ENNReal.ofReal (Cχ ^ p) :=
    ENNReal.ofReal_rpow_of_nonneg hCχ hp0
  have hC1 : ENNReal.ofReal (2 ^ (p - 1) * ((n : ℝ) + 1) ^ p * c0) =
      ENNReal.ofReal (2 ^ (p - 1)) * ENNReal.ofReal (((n : ℝ) + 1) ^ p) * ENNReal.ofReal c0 := by
    rw [ENNReal.ofReal_mul (mul_nonneg h2 h3), ENNReal.ofReal_mul h2]
  have hC2 : ENNReal.ofReal (1 + 2 ^ (p - 1) * Cχ ^ p) =
      1 + ENNReal.ofReal (2 ^ (p - 1)) * ENNReal.ofReal (Cχ ^ p) := by
    rw [ENNReal.ofReal_add zero_le_one (mul_nonneg h2 h4), ENNReal.ofReal_one,
      ENNReal.ofReal_mul h2]
  rw [hC1, hC2, e2, e3, e4]
  ring

theorem real_sqrt_add_sq_le (a b : ℝ) (ha : 0 ≤ a) : Real.sqrt (a + b ^ 2) ≤ Real.sqrt a + |b| := by
  rw [Real.sqrt_le_iff]
  refine ⟨add_nonneg (Real.sqrt_nonneg _) (abs_nonneg _), ?_⟩
  have h1 := Real.sq_sqrt ha
  have h2 := mul_nonneg (Real.sqrt_nonneg a) (abs_nonneg b)
  have h3 := sq_abs b
  nlinarith

theorem modelGradNorm_le_sum (v : Vec n × ℝ → ℝ) (z : Vec n × ℝ) :
    modelGradNorm v z ≤ ∑ i, |tanGrad v z i| + |normDeriv v z| := by
  unfold modelGradNorm
  refine (real_sqrt_add_sq_le _ _ (vecNormSq_nonneg _)).trans ?_
  exact add_le_add_left (vecEuclideanNorm_le_sum_abs _) _

theorem tanGrad_modelExt_eq_zero {g : Vec n → ℝ} (hg : LocallyIntegrable g volume)
    {z : Vec n × ℝ} (hz : 1 < z.2) : tanGrad (modelExt n g) z = 0 := by
  funext i
  rw [tanGrad_modelExt hg (by linarith), extCutoff_eq_zero hz.le]
  simp

theorem normDeriv_modelExt_eq_zero {g : Vec n → ℝ} (hg : LocallyIntegrable g volume)
    {z : Vec n × ℝ} (hz : 1 < z.2) : normDeriv (modelExt n g) z = 0 := by
  rw [normDeriv_modelExt hg (by linarith), extCutoff_eq_zero hz.le, deriv_extCutoff_eq_zero hz]
  simp

theorem modelGradNorm_modelExt_eq_zero {g : Vec n → ℝ} (hg : LocallyIntegrable g volume)
    {z : Vec n × ℝ} (hz : 1 < z.2) : modelGradNorm (modelExt n g) z = 0 := by
  unfold modelGradNorm
  rw [tanGrad_modelExt_eq_zero hg hz, normDeriv_modelExt_eq_zero hg hz]
  simp [vecNormSq, vecDot]

theorem integral_extTan (n : ℕ) (i : Fin n) : ∫ w, extTan n i w = 0 :=
  integral_fderiv_extKernel n (basisVec i)

theorem abs_extTan_le_bound {M : ℝ} (hM : ∀ w : Vec n, ‖fderiv ℝ (extKernel n) w‖ ≤ M)
    (i : Fin n) (w : Vec n) : |extTan n i w| ≤ M :=
  (abs_extTan_le n i w).trans (hM w)

theorem modelGradNorm_nonneg (v : Vec n × ℝ → ℝ) (z : Vec n × ℝ) : 0 ≤ modelGradNorm v z :=
  Real.sqrt_nonneg _

theorem exists_pointwise_bound {p : ℝ} (hp : 1 < p) (n : ℕ) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ g : Vec n → ℝ, Measurable g →
      LocallyIntegrable g volume → ∀ (x : Vec n) (t : ℝ), 0 < t →
        ENNReal.ofReal (|modelExt n g (x, t)| ^ p) +
            ENNReal.ofReal (modelGradNorm (modelExt n g) (x, t) ^ p) ≤
          (Ioc (0 : ℝ) 1).indicator (fun t => ENNReal.ofReal C₁ * extPhi n p g x t +
            ENNReal.ofReal C₂ * extPsi n p g x t) t := by
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨M, hM0, hM⟩ := exists_extKernel_bound n
  obtain ⟨Cχ, hCχ0, hCχ⟩ := exists_deriv_extCutoff_bound
  have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) ≤ 2 ^ (p - 1) := Real.rpow_nonneg (by norm_num) _
  refine ⟨2 ^ (p - 1) * ((n : ℝ) + 1) ^ p * (M ^ p * (2 : ℝ) ^ ((n : ℝ) * (p - 1))),
    1 + 2 ^ (p - 1) * Cχ ^ p, ?_, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg h2 (Real.rpow_nonneg hn _))
      (mul_nonneg (Real.rpow_nonneg hM0 _) (Real.rpow_nonneg (by norm_num) _))
  · exact add_nonneg zero_le_one (mul_nonneg h2 (Real.rpow_nonneg hCχ0 _))
  intro g hgm hg x t ht
  by_cases ht1 : t ≤ 1
  swap
  · have ht1' : (1 : ℝ) < t := not_le.1 ht1
    rw [indicator_of_notMem (by simp [ht1])]
    rw [modelExt_eq_zero g (x, t) ht1'.le, modelGradNorm_modelExt_eq_zero hg (z := (x, t)) ht1']
    simp [Real.zero_rpow (show p ≠ 0 by linarith)]
  rw [indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht, ht1⟩)]
  -- real inequalities
  set A := dilConv n (extKernel n) g (x, t) with hA
  have hχ0 := extCutoff_nonneg t
  have hχ1 := extCutoff_le_one t
  have hE : |modelExt n g (x, t)| ≤ |A| := by
    rw [modelExt_eq_on_upperHalf g ht, abs_mul, abs_of_nonneg hχ0]
    exact mul_le_of_le_one_left (abs_nonneg _) hχ1
  have htan : ∀ i, |tanGrad (modelExt n g) (x, t) i| ≤
      |dilConv (n + 1) (extTan n i) g (x, t)| := by
    intro i
    rw [tanGrad_modelExt hg ht i, abs_mul, abs_of_nonneg hχ0]
    exact mul_le_of_le_one_left (abs_nonneg _) hχ1
  have hnd : |normDeriv (modelExt n g) (x, t)| ≤
      |dilConv (n + 1) (extRad n) g (x, t)| + Cχ * |A| := by
    rw [normDeriv_modelExt hg ht]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg hχ0]
      exact mul_le_of_le_one_left (abs_nonneg _) hχ1
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hCχ t) (abs_nonneg _)
  have hmgn : modelGradNorm (modelExt n g) (x, t) ≤
      ∑ i, |dilConv (n + 1) (extTan n i) g (x, t)| +
        (|dilConv (n + 1) (extRad n) g (x, t)| + Cχ * |A|) :=
    (modelGradNorm_le_sum _ _).trans (add_le_add (Finset.sum_le_sum fun i _ => htan i) hnd)
  -- the ball bounds
  set I := ∫⁻ y, (eBallSet n x t).indicator (fun y => ENNReal.ofReal |g y - g x|) y with hI
  set R := ENNReal.ofReal (M * (t⁻¹) ^ (n + 1)) * I with hR
  have hMt : ∀ i, ENNReal.ofReal |dilConv (n + 1) (extTan n i) g (x, t)| ≤ R := fun i =>
    ofReal_abs_dilConv_le_ball (isProfile_extTan n i) (integral_extTan n i)
      (abs_extTan_le_bound (fun w => (hM w).1) i) hg ht x
  have hMr : ENNReal.ofReal |dilConv (n + 1) (extRad n) g (x, t)| ≤ R :=
    ofReal_abs_dilConv_le_ball (isProfile_extRad n) (integral_extRad n)
      (fun w => (hM w).2.2) hg ht x
  have hS : ENNReal.ofReal (modelGradNorm (modelExt n g) (x, t)) ≤
      ENNReal.ofReal ((n : ℝ) + 1) * R + ENNReal.ofReal Cχ * ENNReal.ofReal |A| := by
    have hsum : 0 ≤ ∑ i, |dilConv (n + 1) (extTan n i) g (x, t)| :=
      Finset.sum_nonneg fun i _ => abs_nonneg _
    have hrest : 0 ≤ |dilConv (n + 1) (extRad n) g (x, t)| + Cχ * |A| :=
      add_nonneg (abs_nonneg _) (mul_nonneg hCχ0 (abs_nonneg _))
    calc ENNReal.ofReal (modelGradNorm (modelExt n g) (x, t))
        ≤ ENNReal.ofReal (∑ i, |dilConv (n + 1) (extTan n i) g (x, t)| +
            (|dilConv (n + 1) (extRad n) g (x, t)| + Cχ * |A|)) :=
          ENNReal.ofReal_le_ofReal hmgn
      _ = ∑ i, ENNReal.ofReal |dilConv (n + 1) (extTan n i) g (x, t)| +
            (ENNReal.ofReal |dilConv (n + 1) (extRad n) g (x, t)| +
              ENNReal.ofReal Cχ * ENNReal.ofReal |A|) := by
          rw [ENNReal.ofReal_add hsum hrest, ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _),
            ENNReal.ofReal_add (abs_nonneg _) (mul_nonneg hCχ0 (abs_nonneg _)),
            ENNReal.ofReal_mul hCχ0]
      _ ≤ ∑ _i : Fin n, R + (R + ENNReal.ofReal Cχ * ENNReal.ofReal |A|) := by
          gcongr with i
          exact hMt i
      _ = ENNReal.ofReal ((n : ℝ) + 1) * R + ENNReal.ofReal Cχ * ENNReal.ofReal |A| := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_add (Nat.cast_nonneg n) zero_le_one, ENNReal.ofReal_natCast,
            ENNReal.ofReal_one]
          ring
  have hA' : ENNReal.ofReal |A| ^ p ≤ extPsi n p g x t := by
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0]
    exact ofReal_abs_dilConv_rpow_le hp hgm ht x
  have hRB : R ^ p ≤ ENNReal.ofReal (M ^ p * (2 : ℝ) ^ ((n : ℝ) * (p - 1))) * extPhi n p g x t := by
    refine (rball_rpow_le hp hM0 hgm ht x).trans (le_of_eq ?_)
    unfold extPhi
    rw [ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hM0 _) (Real.rpow_nonneg (by norm_num) _)),
      mul_assoc]
  calc ENNReal.ofReal (|modelExt n g (x, t)| ^ p) +
        ENNReal.ofReal (modelGradNorm (modelExt n g) (x, t) ^ p)
      ≤ ENNReal.ofReal |A| ^ p + (ENNReal.ofReal ((n : ℝ) + 1) * R +
          ENNReal.ofReal Cχ * ENNReal.ofReal |A|) ^ p := by
        refine add_le_add ?_ ?_
        · rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0]
          exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (abs_nonneg _) hE hp0)
        · rw [← ENNReal.ofReal_rpow_of_nonneg (modelGradNorm_nonneg _ _) hp0]
          exact ENNReal.rpow_le_rpow hS hp0
    _ ≤ extPsi n p g x t + 2 ^ (p - 1) * (ENNReal.ofReal ((n : ℝ) + 1) ^ p *
          (ENNReal.ofReal (M ^ p * (2 : ℝ) ^ ((n : ℝ) * (p - 1))) * extPhi n p g x t) +
          ENNReal.ofReal Cχ ^ p * extPsi n p g x t) :=
        add_le_add hA' (enn_combine hp.le hRB hA')
    _ = _ := enn_consts hp n hCχ0 _ _

end PDE.TraceLane
