module

public import PDEFoundation.Sobolev.Trace.Extension.FlatReal
public import PDEFoundation.Sobolev.Trace.Extension.FlatKernel
public import PDEFoundation.Sobolev.Trace.Extension.FlatLp

/-!
# The pointwise bound for the flat Gagliardo integrand of the pull-back

For every pair `x', y' : Vec n`, the integrand `|w x' - w y'|^p / |x' - y'|^q` of the flat
Gagliardo seminorm of `w = flatPullback φ ζ g` is bounded by the sum of

* `flatT1`: a multiple of the surface Gagliardo integrand `|g X - g Y|^p / |X - Y|^q`, supported on
  pairs in the chart ball;
* a multiple of `(Pg x' + Pg y') · flatRadKer (|x' - y'|)`, an off-diagonal term of convolution
  type, where `Pg = flatPg` is the `p`-th power of `g` along the chart.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped ENNReal NNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

/-- The integrand of the Gagliardo seminorm, as an extended nonnegative real. -/
noncomputable def flatKerF {d : ℕ} (p q : ℝ) (g : Vec d → ℝ) (X Y : Vec d) : ℝ≥0∞ :=
  ENNReal.ofReal (|g X - g Y| ^ p / vecEuclideanNorm (X - Y) ^ q)

theorem measurable_flatKerF {d : ℕ} (p q : ℝ) {g : Vec d → ℝ} (hg : Measurable g) :
    Measurable fun z : Vec d × Vec d => flatKerF p q g z.1 z.2 :=
  ENNReal.measurable_ofReal.comp
    (((continuous_abs.measurable.comp ((hg.comp measurable_fst).sub
      (hg.comp measurable_snd))).pow_const p).div
      ((measurable_vecEuclideanNorm.comp (measurable_fst.sub measurable_snd)).pow_const q))

/-- The first term: the surface Gagliardo integrand along the chart, on pairs in the ball. -/
noncomputable def flatT1 (φ : GraphChart Ω) (E p q : ℝ) (g : Vec (n + 1) → ℝ) (x' y' : Vec n) :
    ℝ≥0∞ :=
  (euclideanBall φ.c φ.r ×ˢ euclideanBall φ.c φ.r).indicator
    (fun z : Vec n × Vec n =>
      ENNReal.ofReal E * flatKerF p q g (φ.map (z.1, 0)) (φ.map (z.2, 0))) (x', y')

theorem measurable_flatT1 (φ : GraphChart Ω) (E p q : ℝ) {g : Vec (n + 1) → ℝ}
    (hg : Measurable g) : Measurable fun z : Vec n × Vec n => flatT1 φ E p q g z.1 z.2 := by
  have hpair : Measurable fun z : Vec n × Vec n =>
      (φ.map (z.1, 0), φ.map (z.2, 0)) :=
    (φ.measurable_boundaryMap.comp measurable_fst).prodMk
      (φ.measurable_boundaryMap.comp measurable_snd)
  have hF : Measurable fun z : Vec n × Vec n =>
      ENNReal.ofReal E * flatKerF p q g (φ.map (z.1, 0)) (φ.map (z.2, 0)) :=
    Measurable.const_mul ((measurable_flatKerF p q hg).comp hpair) _
  have h : (fun z : Vec n × Vec n => flatT1 φ E p q g z.1 z.2) =
      (euclideanBall φ.c φ.r ×ˢ euclideanBall φ.c φ.r).indicator
        (fun z : Vec n × Vec n =>
          ENNReal.ofReal E * flatKerF p q g (φ.map (z.1, 0)) (φ.map (z.2, 0))) := by
    funext z
    rfl
  rw [h]
  exact hF.indicator (φ.measurableSet_ball.prod φ.measurableSet_ball)

theorem ofReal_combo {E A c P Q R : ℝ} (hE : 0 ≤ E) (hA : 0 ≤ A) (hc : 0 ≤ c) (hP : 0 ≤ P)
    (hQ : 0 ≤ Q) (hR : 0 ≤ R) :
    ENNReal.ofReal (E * A + c * ((P + Q) * R)) =
      ENNReal.ofReal E * ENNReal.ofReal A +
        ENNReal.ofReal c * (ENNReal.ofReal P * ENNReal.ofReal R +
          ENNReal.ofReal Q * ENNReal.ofReal R) := by
  rw [ENNReal.ofReal_add (mul_nonneg hE hA) (mul_nonneg hc (mul_nonneg (add_nonneg hP hQ) hR)),
    ENNReal.ofReal_mul hE, ENNReal.ofReal_mul hc, ENNReal.ofReal_mul (add_nonneg hP hQ),
    ENNReal.ofReal_add hP hQ, add_mul]

namespace GraphChart

/-- One point inside the ball and one outside. -/
theorem flat_oneSided (φ : GraphChart Ω) {ζ : Vec (n + 1) → ℝ}
    {M Lz δ p : ℝ} (hp : 1 < p) (hM0 : 0 ≤ M) (hM : ∀ X, |ζ X| ≤ M) (hLz0 : 0 ≤ Lz)
    (hδ : 0 < δ)
    (hδK : ∀ x' y' : Vec n, φ.map (x', 0) ∈ tsupport ζ → vecEuclideanNorm (x' - y') < δ →
      y' ∈ euclideanBall φ.c φ.r)
    (g : Vec (n + 1) → ℝ) {x' y' : Vec n} (hx : x' ∈ euclideanBall φ.c φ.r)
    (hy : y' ∉ euclideanBall φ.c φ.r) :
    ENNReal.ofReal (|flatPullback φ ζ g x'| ^ p / vecEuclideanNorm (x' - y') ^ ((n : ℝ) + p - 1)) ≤
      ENNReal.ofReal (2 ^ (p - 1) + M ^ p) * (flatPg φ p g x' *
        flatRadKer n p (2 * M + 1) (Lz * Real.sqrt (1 + φ.L ^ 2) + 1 / δ)
          (vecEuclideanNorm (x' - y'))) := by
  have hp0 : 0 < p := by linarith
  set q : ℝ := (n : ℝ) + p - 1 with hqdef
  have hq : 0 < q := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  set s := vecEuclideanNorm (x' - y') with hsdef
  have hs : 0 ≤ s := vecEuclideanNorm_nonneg _
  by_cases hz : ζ (φ.map (x', 0)) = 0
  · have : flatPullback φ ζ g x' = 0 := by simp [flatPullback, hz]
    rw [this]
    simp [Real.zero_rpow hp0.ne']
  · have hmem : φ.map (x', 0) ∈ tsupport ζ := subset_tsupport _ (Function.mem_support.2 hz)
    have hsδ : δ ≤ s := by
      by_contra h
      exact hy (hδK x' y' hmem (lt_of_not_ge h))
    set m := min (2 * M + 1) ((Lz * Real.sqrt (1 + φ.L ^ 2) + 1 / δ) * s) with hm
    have hm1 : 1 ≤ m := by
      refine le_min (by linarith) ?_
      have h1 : 1 ≤ 1 / δ * s := by
        rw [one_div, inv_mul_eq_div, one_le_div hδ]; exact hsδ
      have h2 : 0 ≤ Lz * Real.sqrt (1 + φ.L ^ 2) * s :=
        mul_nonneg (mul_nonneg hLz0 (Real.sqrt_nonneg _)) hs
      nlinarith
    have hsq : 0 < s ^ q := Real.rpow_pos_of_pos (hδ.trans_le hsδ) q
    have hmp : 1 ≤ m ^ p := Real.one_le_rpow hm1 hp0.le
    simp only [flatPg, indicator_of_mem hx]
    have hw : |flatPullback φ ζ g x'| ≤ M * |g (φ.map (x', 0))| := by
      rw [flatPullback, abs_mul]
      exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
    have hgp : 0 ≤ |g (φ.map (x', 0))| ^ p := Real.rpow_nonneg (abs_nonneg _) _
    have hMp : 0 ≤ M ^ p := Real.rpow_nonneg hM0 _
    have hmain : |flatPullback φ ζ g x'| ^ p / s ^ q ≤
        M ^ p * (|g (φ.map (x', 0))| ^ p * (m ^ p / s ^ q)) := by
      calc |flatPullback φ ζ g x'| ^ p / s ^ q
          ≤ (M * |g (φ.map (x', 0))|) ^ p / s ^ q :=
            div_le_div_of_nonneg_right (Real.rpow_le_rpow (abs_nonneg _) hw hp0.le) hsq.le
        _ = M ^ p * (|g (φ.map (x', 0))| ^ p * (1 / s ^ q)) := by
            rw [Real.mul_rpow hM0 (abs_nonneg _)]; ring
        _ ≤ M ^ p * (|g (φ.map (x', 0))| ^ p * (m ^ p / s ^ q)) := by
            gcongr
    calc ENNReal.ofReal (|flatPullback φ ζ g x'| ^ p / s ^ q)
        ≤ ENNReal.ofReal (M ^ p * (|g (φ.map (x', 0))| ^ p * (m ^ p / s ^ q))) :=
          ENNReal.ofReal_le_ofReal hmain
      _ = ENNReal.ofReal (M ^ p) * (ENNReal.ofReal (|g (φ.map (x', 0))| ^ p) *
            flatRadKer n p (2 * M + 1) (Lz * Real.sqrt (1 + φ.L ^ 2) + 1 / δ) s) := by
          rw [ENNReal.ofReal_mul hMp, ENNReal.ofReal_mul hgp]
          rfl
      _ ≤ _ := by
          gcongr
          exact le_add_of_nonneg_left (Real.rpow_nonneg (by norm_num) _)

/-- The pointwise bound for the flat Gagliardo integrand. -/
theorem flat_pointwise (φ : GraphChart Ω) {ζ : Vec (n + 1) → ℝ} (hζU : tsupport ζ ⊆ φ.dom)
    {M Lz δ p : ℝ} (hp : 1 < p) (hM0 : 0 ≤ M) (hM : ∀ X, |ζ X| ≤ M) (hLz0 : 0 ≤ Lz)
    (hLz : ∀ X Y, |ζ X - ζ Y| ≤ Lz * vecEuclideanNorm (X - Y)) (hδ : 0 < δ)
    (hδK : ∀ x' y' : Vec n, φ.map (x', 0) ∈ tsupport ζ → vecEuclideanNorm (x' - y') < δ →
      y' ∈ euclideanBall φ.c φ.r)
    (g : Vec (n + 1) → ℝ) (x' y' : Vec n) :
    ENNReal.ofReal (|flatPullback φ ζ g x' - flatPullback φ ζ g y'| ^ p /
        vecEuclideanNorm (x' - y') ^ ((n : ℝ) + p - 1)) ≤
      flatT1 φ (2 ^ (p - 1) * M ^ p * Real.sqrt (1 + φ.L ^ 2) ^ ((n : ℝ) + p - 1)) p
          ((n : ℝ) + p - 1) g x' y' +
        ENNReal.ofReal (2 ^ (p - 1) + M ^ p) *
          (flatPg φ p g x' * flatRadKer n p (2 * M + 1)
              (Lz * Real.sqrt (1 + φ.L ^ 2) + 1 / δ) (vecEuclideanNorm (x' - y')) +
            flatPg φ p g y' * flatRadKer n p (2 * M + 1)
              (Lz * Real.sqrt (1 + φ.L ^ 2) + 1 / δ) (vecEuclideanNorm (x' - y'))) := by
  have hp0 : 0 < p := by linarith
  by_cases hx : x' ∈ euclideanBall φ.c φ.r <;> by_cases hy : y' ∈ euclideanBall φ.c φ.r
  · have h := φ.flat_real_ineq hp hM0 hM hLz0 hLz hδ g x' y'
    have hT1 : flatT1 φ (2 ^ (p - 1) * M ^ p * Real.sqrt (1 + φ.L ^ 2) ^ ((n : ℝ) + p - 1)) p
        ((n : ℝ) + p - 1) g x' y' =
        ENNReal.ofReal (2 ^ (p - 1) * M ^ p * Real.sqrt (1 + φ.L ^ 2) ^ ((n : ℝ) + p - 1)) *
          ENNReal.ofReal (|g (φ.map (x', 0)) - g (φ.map (y', 0))| ^ p /
            vecEuclideanNorm (φ.map (x', 0) - φ.map (y', 0)) ^ ((n : ℝ) + p - 1)) := by
      simp only [flatT1, indicator_of_mem (show (x', y') ∈ euclideanBall φ.c φ.r ×ˢ euclideanBall φ.c φ.r from ⟨hx, hy⟩)]
      rfl
    rw [hT1]
    simp only [flatPg, indicator_of_mem hx, indicator_of_mem hy]
    refine (ENNReal.ofReal_le_ofReal h).trans (le_of_eq ?_)
    have h2p : 0 ≤ (2 : ℝ) ^ (p - 1) := Real.rpow_nonneg (by norm_num) _
    have hMp : 0 ≤ M ^ p := Real.rpow_nonneg hM0 _
    have hsq : 0 ≤ vecEuclideanNorm (x' - y') ^ ((n : ℝ) + p - 1) :=
      Real.rpow_nonneg (vecEuclideanNorm_nonneg _) _
    rw [ofReal_combo (mul_nonneg (mul_nonneg h2p hMp) (Real.rpow_nonneg (Real.sqrt_nonneg _) _))
      (div_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg
        (vecEuclideanNorm_nonneg _) _)) (add_nonneg h2p hMp)
      (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
      (div_nonneg (Real.rpow_nonneg (le_min (by linarith) (mul_nonneg (add_nonneg
        (mul_nonneg hLz0 (Real.sqrt_nonneg _)) (by positivity)) (vecEuclideanNorm_nonneg _))) _)
        hsq)]
    rfl
  · have hwy : flatPullback φ ζ g y' = 0 := φ.flatPullback_eq_zero_of_notMem hζU g hy
    have h := φ.flat_oneSided hp hM0 hM hLz0 hδ hδK g hx hy
    rw [hwy, sub_zero]
    refine h.trans ?_
    refine le_trans ?_ (le_add_left le_rfl)
    have : flatPg φ p g y' = 0 := by simp [flatPg, indicator_of_notMem hy]
    rw [this]
    simp
  · have hwx : flatPullback φ ζ g x' = 0 := φ.flatPullback_eq_zero_of_notMem hζU g hx
    have h := φ.flat_oneSided hp hM0 hM hLz0 hδ hδK g hy hx
    rw [hwx, zero_sub, abs_neg]
    rw [vecEuclideanNorm_sub_comm y' x'] at h
    refine h.trans ?_
    refine le_trans ?_ (le_add_left le_rfl)
    have : flatPg φ p g x' = 0 := by simp [flatPg, indicator_of_notMem hx]
    rw [this]
    simp
  · rw [φ.flatPullback_eq_zero_of_notMem hζU g hx, φ.flatPullback_eq_zero_of_notMem hζU g hy]
    simp [Real.zero_rpow hp0.ne']

end GraphChart

end PDE.TraceLane
