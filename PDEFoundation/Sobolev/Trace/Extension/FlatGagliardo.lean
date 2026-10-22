module

public import PDEFoundation.Sobolev.Trace.Extension.FlatPointwise
public import PDEFoundation.Sobolev.Trace.Model.Defs

/-!
# The flat Gagliardo bound for measurable boundary functions

For a measurable `g`, integrating the pointwise bound of `FlatPointwise` over `Vec n × Vec n`
bounds the flat Gagliardo seminorm of `flatPullback φ ζ g` by
`C (∫ |g|^p dσ + [g]^p)`, for `n ≥ 1`; for `n = 0` the flat seminorm vanishes.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped ENNReal NNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

/-- On `Vec 0` the flat Gagliardo seminorm vanishes. -/
theorem flat_flatGagliardo_zero (q : ℝ) {p : ℝ} (hp : 0 < p) (w : Vec 0 → ℝ) :
    flatGagliardo 0 q p w = 0 := by
  unfold flatGagliardo
  refine (lintegral_congr (fun x' => (lintegral_congr (fun y' => ?_)).trans
    lintegral_zero)).trans lintegral_zero
  have : x' = y' := Subsingleton.elim _ _
  subst this
  simp [Real.zero_rpow hp.ne']

theorem iterated_indicator_flatT1 (φ : GraphChart Ω) (E p q : ℝ) (g : Vec (n + 1) → ℝ)
    (x' : Vec n) :
    ∫⁻ y', flatT1 φ E p q g x' y' = (euclideanBall φ.c φ.r).indicator
      (fun x' => ∫⁻ y' in euclideanBall φ.c φ.r,
        ENNReal.ofReal E * flatKerF p q g (φ.map (x', 0)) (φ.map (y', 0))) x' := by
  by_cases hx : x' ∈ euclideanBall φ.c φ.r
  · rw [indicator_of_mem hx, ← lintegral_indicator φ.measurableSet_ball]
    refine lintegral_congr (fun y' => ?_)
    by_cases hy : y' ∈ euclideanBall φ.c φ.r <;>
      simp [flatT1, hx, hy]
  · rw [indicator_of_notMem hx]
    refine (lintegral_congr (fun y' => ?_)).trans lintegral_zero
    simp [flatT1, hx]

theorem lintegral_lintegral_flatT1_le (φ : GraphChart Ω) (E p q : ℝ) {g : Vec (n + 1) → ℝ}
    (hg : Measurable g) :
    ∫⁻ x', ∫⁻ y', flatT1 φ E p q g x' y' ≤ ENNReal.ofReal E *
      ∫⁻ x, ∫⁻ y, flatKerF p q g x y ∂boundarySurfaceMeasure Ω ∂boundarySurfaceMeasure Ω := by
  simp_rw [iterated_indicator_flatT1]
  rw [lintegral_indicator φ.measurableSet_ball]
  have h := φ.lintegral_boundaryMap_prod_le (F := fun x y => ENNReal.ofReal E * flatKerF p q g x y)
    (Measurable.const_mul (measurable_flatKerF p q hg) _)
  refine h.trans (le_of_eq ?_)
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The flat Gagliardo bound for measurable `g` and `n ≥ 1`. -/
theorem flatGagliardo_le_measurable [NeZero n] (φ : GraphChart Ω) {ζ : Vec (n + 1) → ℝ}
    (hζ : ContDiff ℝ 1 ζ) (hζK : HasCompactSupport ζ) (hζU : tsupport ζ ⊆ φ.dom) {p : ℝ}
    (hp : 1 < p) :
    ∃ C : ℝ≥0, ∀ g : Vec (n + 1) → ℝ, Measurable g →
      flatGagliardo n ((n : ℝ) + p - 1) p (flatPullback φ ζ g) ≤
        C * (∫⁻ x, ENNReal.ofReal (|g x| ^ p) ∂boundarySurfaceMeasure Ω +
          ∫⁻ x, ∫⁻ y, flatKerF p ((n : ℝ) + p - 1) g x y ∂boundarySurfaceMeasure Ω
            ∂boundarySurfaceMeasure Ω) := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_le_of_hasCompactSupport hζ.continuous hζK
  obtain ⟨Lz, hLz0, hLz⟩ := exists_lipschitz_of_contDiff hζ hζK
  obtain ⟨δ, hδ, hδK⟩ := φ.exists_delta hζK hζU
  have hp0 : 0 < p := by linarith
  set a : ℝ := 2 * M + 1 with ha
  set b : ℝ := Lz * Real.sqrt (1 + φ.L ^ 2) + 1 / δ with hb
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hb0 : 0 ≤ b := by
    have : 0 ≤ 1 / δ := by positivity
    rw [hb]; have := mul_nonneg hLz0 (Real.sqrt_nonneg (1 + φ.L ^ 2)); linarith
  set H : ℝ≥0∞ := ∫⁻ z : Vec n, flatRadKer n p a b (vecEuclideanNorm z) with hH
  have hHtop : H ≠ ⊤ := (lintegral_flatRadKer_lt_top n hp ha0 hb0).ne
  set E : ℝ := 2 ^ (p - 1) * M ^ p * Real.sqrt (1 + φ.L ^ 2) ^ ((n : ℝ) + p - 1) with hE
  set cT : ℝ := 2 ^ (p - 1) + M ^ p with hcT
  have hE0 : 0 ≤ E := by
    rw [hE]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hM0 _))
      (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  have hCtop : ENNReal.ofReal E + 2 * ENNReal.ofReal cT * H ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hHtop⟩
  refine ⟨(ENNReal.ofReal E + 2 * ENNReal.ofReal cT * H).toNNReal, fun g hg => ?_⟩
  rw [ENNReal.coe_toNNReal hCtop]
  set G : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (|g x| ^ p) ∂boundarySurfaceMeasure Ω with hG
  set S : ℝ≥0∞ := ∫⁻ x, ∫⁻ y, flatKerF p ((n : ℝ) + p - 1) g x y ∂boundarySurfaceMeasure Ω
    ∂boundarySurfaceMeasure Ω with hS
  set K : Vec n → Vec n → ℝ≥0∞ := fun x' y' => flatRadKer n p a b (vecEuclideanNorm (x' - y'))
    with hK
  have hKm : Measurable fun z : Vec n × Vec n => K z.1 z.2 := measurable_flatRadKer_sub n p a b
  have hPg := measurable_flatPg φ p hg
  have hT1m := measurable_flatT1 φ E p ((n : ℝ) + p - 1) hg
  set T2 : Vec n → Vec n → ℝ≥0∞ := fun x' y' =>
    ENNReal.ofReal cT * (flatPg φ p g x' * K x' y' + flatPg φ p g y' * K x' y') with hT2
  have hA1m : Measurable fun z : Vec n × Vec n => flatPg φ p g z.1 * K z.1 z.2 :=
    (hPg.comp measurable_fst).mul hKm
  have hA2m : Measurable fun z : Vec n × Vec n => flatPg φ p g z.2 * K z.1 z.2 :=
    (hPg.comp measurable_snd).mul hKm
  have hT2m : Measurable fun z : Vec n × Vec n => T2 z.1 z.2 :=
    Measurable.const_mul (hA1m.add hA2m) _
  -- Step A: pointwise bound.
  have hA : flatGagliardo n ((n : ℝ) + p - 1) p (flatPullback φ ζ g) ≤
      ∫⁻ x', ∫⁻ y', (flatT1 φ E p ((n : ℝ) + p - 1) g x' y' + T2 x' y') := by
    unfold flatGagliardo
    exact lintegral_mono fun x' => lintegral_mono fun y' =>
      φ.flat_pointwise hζU hp hM0 hM hLz0 hLz hδ hδK g x' y'
  refine hA.trans ?_
  -- Step B: split.
  have hT1y : ∀ x', Measurable fun y' => flatT1 φ E p ((n : ℝ) + p - 1) g x' y' := fun x' =>
    Measurable.of_uncurry_left
      (f := fun x' y' => flatT1 φ E p ((n : ℝ) + p - 1) g x' y') hT1m
  have hB1 : ∀ x', ∫⁻ y', (flatT1 φ E p ((n : ℝ) + p - 1) g x' y' + T2 x' y') =
      (∫⁻ y', flatT1 φ E p ((n : ℝ) + p - 1) g x' y') + ∫⁻ y', T2 x' y' := fun x' =>
    lintegral_add_left (μ := (volume : Measure (Vec n))) (hT1y x') (fun y' => T2 x' y')
  simp_rw [hB1]
  rw [lintegral_add_left hT1m.lintegral_prod_right']
  -- Step C and D.
  have hC := lintegral_lintegral_flatT1_le φ E p ((n : ℝ) + p - 1) hg
  have hD : ∫⁻ x', ∫⁻ y', T2 x' y' ≤ ENNReal.ofReal cT * (G * H + G * H) := by
    have hA1y : ∀ x', Measurable fun y' => flatPg φ p g x' * K x' y' := fun x' =>
      Measurable.of_uncurry_left (f := fun x' y' => flatPg φ p g x' * K x' y') hA1m
    have h1 : ∀ x', ∫⁻ y', T2 x' y' = ENNReal.ofReal cT *
        ((∫⁻ y', flatPg φ p g x' * K x' y') + ∫⁻ y', flatPg φ p g y' * K x' y') := fun x' => by
      simp only [hT2]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left (hA1y x')]
    simp_rw [h1]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_add_left hA1m.lintegral_prod_right']
    have e1 := lintegral_lintegral_mul_flatRadKer_left n p a b hPg
    have e2 := lintegral_lintegral_mul_flatRadKer_right n p a b hPg
    have f1 : ∫⁻ x', ∫⁻ y', flatPg φ p g x' * K x' y' =
        (∫⁻ x', flatPg φ p g x') * H := e1
    have f2 : ∫⁻ x', ∫⁻ y', flatPg φ p g y' * K x' y' =
        (∫⁻ x', flatPg φ p g x') * H := e2
    rw [f1, f2]
    have hPgG := lintegral_flatPg_le φ p hg.aemeasurable
    gcongr
  calc (∫⁻ x', ∫⁻ y', flatT1 φ E p ((n : ℝ) + p - 1) g x' y') + ∫⁻ x', ∫⁻ y', T2 x' y'
      ≤ ENNReal.ofReal E * S + ENNReal.ofReal cT * (G * H + G * H) := add_le_add hC hD
    _ ≤ (ENNReal.ofReal E + 2 * ENNReal.ofReal cT * H) * (G + S) := by
        have : (ENNReal.ofReal E + 2 * ENNReal.ofReal cT * H) * (G + S) =
            (ENNReal.ofReal E * S + ENNReal.ofReal cT * (G * H + G * H)) +
              (ENNReal.ofReal E * G + 2 * ENNReal.ofReal cT * H * S) := by ring
        rw [this]
        exact le_self_add

end PDE.TraceLane
