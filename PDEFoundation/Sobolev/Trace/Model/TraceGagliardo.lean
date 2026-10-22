module

public import PDEFoundation.Sobolev.Trace.Model.TraceKernel
public import PDEFoundation.Sobolev.Trace.Model.TraceVertical
public import PDEFoundation.Sobolev.Trace.Model.TracePolar

/-!
# Step 3 of the trace theorem: assembly for `n ≥ 1`

The Gagliardo seminorm of the trace on the half-space is bounded by `C(n, p)` times the `L^p`
norm of the gradient.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped ENNReal NNReal

variable {n : ℕ}

theorem measurable_traceVert (v : Vec n × ℝ → ℝ) (p : ℝ) :
    Measurable (fun r : Vec n × ℝ => traceVert v p r.1 r.2) :=
  ((measurable_vertInt v).pow_const p).mul
    (ENNReal.measurable_ofReal.comp (measurable_snd.pow_const _))

theorem measurable_traceHoriz (v : Vec n × ℝ → ℝ) (p : ℝ) :
    Measurable (fun q : Vec n × Vec n => traceHoriz v p q.1 q.2) := by
  have hnorm : Measurable (fun q : Vec n × Vec n => vecEuclideanNorm (q.2 - q.1)) :=
    measurable_vecEuclideanNorm.comp (measurable_snd.sub measurable_fst)
  have hf : Measurable (fun r : (Vec n × Vec n) × ℝ =>
      tanGradPow v p (r.1.1 + r.2 • (r.1.2 - r.1.1), vecEuclideanNorm (r.1.2 - r.1.1))) := by
    refine (measurable_tanGradPow v p).comp (Measurable.prodMk ?_ ?_)
    · exact (measurable_fst.comp measurable_fst).add (measurable_snd.smul
        ((measurable_snd.comp measurable_fst).sub (measurable_fst.comp measurable_fst)))
    · exact measurable_vecEuclideanNorm.comp
        ((measurable_snd.comp measurable_fst).sub (measurable_fst.comp measurable_fst))
  exact (ENNReal.measurable_ofReal.comp (hnorm.pow_const _)).mul
    (hf.lintegral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) 1)))

/-- Splitting a double integral of a constant times a sum of three terms. -/
theorem lintegral_lintegral_const_mul_add3 {K : ℝ≥0∞} (hK : K ≠ ⊤) (A B C : Vec n → Vec n → ℝ≥0∞)
    (hA : Measurable fun q : Vec n × Vec n => A q.1 q.2)
    (hB : Measurable fun q : Vec n × Vec n => B q.1 q.2)
    (hC : Measurable fun q : Vec n × Vec n => C q.1 q.2) :
    ∫⁻ x, ∫⁻ y, K * (A x y + B x y + C x y) =
      K * ((∫⁻ x, ∫⁻ y, A x y) + (∫⁻ x, ∫⁻ y, B x y) + (∫⁻ x, ∫⁻ y, C x y)) := by
  have hAx : ∀ x, Measurable (fun y => A x y) := fun x => hA.comp measurable_prodMk_left
  have hBx : ∀ x, Measurable (fun y => B x y) := fun x => hB.comp measurable_prodMk_left
  have hCx : ∀ x, Measurable (fun y => C x y) := fun x => hC.comp measurable_prodMk_left
  have hAi : Measurable fun x => ∫⁻ y, A x y := hA.lintegral_prod_right'
  have hBi : Measurable fun x => ∫⁻ y, B x y := hB.lintegral_prod_right'
  have hCi : Measurable fun x => ∫⁻ y, C x y := hC.lintegral_prod_right'
  have h1 : ∀ x, ∫⁻ y, K * (A x y + B x y + C x y) =
      K * ((∫⁻ y, A x y) + (∫⁻ y, B x y) + (∫⁻ y, C x y)) := by
    intro x
    rw [lintegral_const_mul' _ _ hK,
      lintegral_add_left (f := fun y => A x y + B x y) ((hAx x).add (hBx x)) (fun y => C x y),
      lintegral_add_left (f := fun y => A x y) (hAx x) (fun y => B x y)]
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ hK,
    lintegral_add_left (f := fun x => (∫⁻ y, A x y) + (∫⁻ y, B x y)) (hAi.add hBi)
      (fun x => ∫⁻ y, C x y),
    lintegral_add_left (f := fun x => ∫⁻ y, A x y) hAi (fun x => ∫⁻ y, B x y)]

/-- The first vertical term. -/
theorem vertical_term_left [NeZero n] {p : ℝ} (hp : 1 < p) (c : ℝ≥0∞) (hctop : c ≠ ⊤)
    (hc : ∀ f : ℝ → ℝ≥0∞, Measurable f → ∫⁻ k : Vec n, f (vecEuclideanNorm k) =
      c * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (n - 1)) * f r)
    (v : Vec n × ℝ → ℝ) :
    ∫⁻ x' : Vec n, ∫⁻ y' : Vec n, traceVert v p x' (vecEuclideanNorm (y' - x')) ≤
      c * ENNReal.ofReal ((p / (p - 1)) ^ p) *
        ∫⁻ z in upperHalf n, ENNReal.ofReal (|normDeriv v z| ^ p) := by
  have hmeas : Measurable (fun z : Vec n × ℝ => ENNReal.ofReal (|normDeriv v z| ^ p)) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_abs.measurable.comp (measurable_normDeriv v)).pow_const p)
  have h1 : ∀ x' : Vec n, ∫⁻ y' : Vec n, traceVert v p x' (vecEuclideanNorm (y' - x')) ≤
      c * ENNReal.ofReal ((p / (p - 1)) ^ p) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (|normDeriv v (x', t)| ^ p) := by
    intro x'
    have h := (lintegral_add_left_eq_self (μ := (volume : Measure (Vec n)))
      (fun y' => traceVert v p x' (vecEuclideanNorm (y' - x'))) x').symm
    simp only [add_sub_cancel_left] at h
    rw [h]
    exact vertical_bound hp c hc v x'
  refine (lintegral_mono h1).trans (le_of_eq ?_)
  rw [lintegral_const_mul' _ _ (by
      exact ENNReal.mul_ne_top hctop ENNReal.ofReal_ne_top),
    lintegral_upperHalf _ hmeas.aemeasurable]

/-- The second vertical term. -/
theorem vertical_term_right [NeZero n] {p : ℝ} (hp : 1 < p) (c : ℝ≥0∞) (hctop : c ≠ ⊤)
    (hc : ∀ f : ℝ → ℝ≥0∞, Measurable f → ∫⁻ k : Vec n, f (vecEuclideanNorm k) =
      c * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (n - 1)) * f r)
    (v : Vec n × ℝ → ℝ) :
    ∫⁻ x' : Vec n, ∫⁻ y' : Vec n, traceVert v p y' (vecEuclideanNorm (y' - x')) ≤
      c * ENNReal.ofReal ((p / (p - 1)) ^ p) *
        ∫⁻ z in upperHalf n, ENNReal.ofReal (|normDeriv v z| ^ p) := by
  have hmeas : Measurable (fun z : Vec n × ℝ => ENNReal.ofReal (|normDeriv v z| ^ p)) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_abs.measurable.comp (measurable_normDeriv v)).pow_const p)
  have hF : Measurable (fun q : Vec n × Vec n =>
      traceVert v p q.2 (vecEuclideanNorm (q.2 - q.1))) :=
    (measurable_traceVert v p).comp (measurable_snd.prodMk
      (measurable_vecEuclideanNorm.comp (measurable_snd.sub measurable_fst)))
  rw [lintegral_lintegral_swap (f := fun x' y' => traceVert v p y' (vecEuclideanNorm (y' - x')))
    hF.aemeasurable]
  have h1 : ∀ y' : Vec n, ∫⁻ x' : Vec n, traceVert v p y' (vecEuclideanNorm (y' - x')) ≤
      c * ENNReal.ofReal ((p / (p - 1)) ^ p) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (|normDeriv v (y', t)| ^ p) := by
    intro y'
    have h := (lintegral_add_left_eq_self (μ := (volume : Measure (Vec n)))
      (fun x' => traceVert v p y' (vecEuclideanNorm (y' - x'))) y').symm
    simp only [sub_add_cancel_left, vecEuclideanNorm_neg] at h
    rw [h]
    exact vertical_bound hp c hc v y'
  refine (lintegral_mono h1).trans (le_of_eq ?_)
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top hctop ENNReal.ofReal_ne_top),
    lintegral_upperHalf _ hmeas.aemeasurable]

/-- The horizontal term. -/
theorem horizontal_term [NeZero n] (p : ℝ) (c : ℝ≥0∞)
    (hc : ∀ f : ℝ → ℝ≥0∞, Measurable f → ∫⁻ k : Vec n, f (vecEuclideanNorm k) =
      c * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (n - 1)) * f r)
    (v : Vec n × ℝ → ℝ) :
    ∫⁻ x' : Vec n, ∫⁻ y' : Vec n, traceHoriz v p x' y' =
      c * ∫⁻ z in upperHalf n, tanGradPow v p z := by
  rw [← horizontal_eq p c hc v]
  refine lintegral_congr (fun x' => ?_)
  have h := (lintegral_add_left_eq_self (μ := (volume : Measure (Vec n)))
    (fun y' => traceHoriz v p x' y') x').symm
  rw [h]
  simp only [traceHoriz, add_sub_cancel_left]

theorem trace_abs_normDeriv_le_modelGradNorm (v : Vec n × ℝ → ℝ) (z : Vec n × ℝ) :
    |normDeriv v z| ≤ modelGradNorm v z :=
  Real.abs_le_sqrt (by nlinarith [vecNormSq_nonneg (tanGrad v z)])

theorem tanGradNorm_le_modelGradNorm (v : Vec n × ℝ → ℝ) (z : Vec n × ℝ) :
    tanGradNorm v z ≤ modelGradNorm v z :=
  Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (normDeriv v z)])

/-- **Step 3 for `n ≥ 1`.** -/
theorem model_trace_gagliardo_pos (n : ℕ) [NeZero n] {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ≥0, ∀ v : Vec n × ℝ → ℝ, ContDiffOn ℝ 1 v (closedUpperHalf n) →
      flatGagliardo n (n + p - 1) p (fun x' => v (x', 0)) ≤
        (C : ℝ≥0∞) * ∫⁻ z in upperHalf n, ENNReal.ofReal (modelGradNorm v z ^ p) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨c, hctop, hc⟩ := exists_lintegral_comp_vecEuclideanNorm n
  set K : ℝ≥0∞ := 2 ^ (p - 1) * 2 ^ (p - 1) with hKdef
  have hKtop : K ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp))
    (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp))
  set CV : ℝ≥0∞ := c * ENNReal.ofReal ((p / (p - 1)) ^ p) with hCV
  set M : ℝ≥0∞ := K * (CV + c + CV) with hM
  have hMtop : M ≠ ⊤ := ENNReal.mul_ne_top hKtop
    (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hctop ENNReal.ofReal_ne_top,
      hctop⟩, ENNReal.mul_ne_top hctop ENNReal.ofReal_ne_top⟩)
  refine ⟨M.toNNReal, fun v hv => ?_⟩
  rw [ENNReal.coe_toNNReal hMtop]
  set J : ℝ≥0∞ := ∫⁻ z in upperHalf n, ENNReal.ofReal (modelGradNorm v z ^ p) with hJ
  have hJ1 : ∫⁻ z in upperHalf n, ENNReal.ofReal (|normDeriv v z| ^ p) ≤ J :=
    lintegral_mono (fun z => ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow (abs_nonneg _) (trace_abs_normDeriv_le_modelGradNorm v z) hp0.le))
  have hJ2 : ∫⁻ z in upperHalf n, tanGradPow v p z ≤ J :=
    lintegral_mono (fun z => ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow (vecEuclideanNorm_nonneg _) (tanGradNorm_le_modelGradNorm v z) hp0.le))
  have hV :
      Measurable (fun q : Vec n × Vec n => traceVert v p q.1 (vecEuclideanNorm (q.2 - q.1))) :=
    (measurable_traceVert v p).comp (measurable_fst.prodMk
      (measurable_vecEuclideanNorm.comp (measurable_snd.sub measurable_fst)))
  have hV' : Measurable (fun q : Vec n × Vec n =>
      traceVert v p q.2 (vecEuclideanNorm (q.2 - q.1))) :=
    (measurable_traceVert v p).comp (measurable_snd.prodMk
      (measurable_vecEuclideanNorm.comp (measurable_snd.sub measurable_fst)))
  have hbound : flatGagliardo n ((n : ℝ) + p - 1) p (fun x' => v (x', 0)) ≤
      ∫⁻ x' : Vec n, ∫⁻ y' : Vec n, K * (traceVert v p x' (vecEuclideanNorm (y' - x')) +
        traceHoriz v p x' y' + traceVert v p y' (vecEuclideanNorm (y' - x'))) :=
    lintegral_mono (fun x' => lintegral_mono (fun y' => integrand_le hp hv x' y'))
  refine hbound.trans ?_
  rw [lintegral_lintegral_const_mul_add3 hKtop
    (fun x' y' => traceVert v p x' (vecEuclideanNorm (y' - x')))
    (fun x' y' => traceHoriz v p x' y')
    (fun x' y' => traceVert v p y' (vecEuclideanNorm (y' - x'))) hV (measurable_traceHoriz v p) hV',
    horizontal_term p c hc v]
  have h1 := vertical_term_left hp c hctop hc v
  have h3 := vertical_term_right hp c hctop hc v
  calc K * (((∫⁻ x' : Vec n, ∫⁻ y' : Vec n, traceVert v p x' (vecEuclideanNorm (y' - x'))) +
        c * (∫⁻ z in upperHalf n, tanGradPow v p z)) +
        (∫⁻ x' : Vec n, ∫⁻ y' : Vec n, traceVert v p y' (vecEuclideanNorm (y' - x'))))
      ≤ K * (CV * J + c * J + CV * J) := by
        gcongr
        · exact h1.trans (by gcongr)
        · exact h3.trans (by gcongr)
    _ = M * J := by rw [hM]; ring

end PDE.TraceLane
