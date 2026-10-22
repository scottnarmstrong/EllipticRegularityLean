module

public import EllipticRegularity.Ch4.Meyers.AxisRemoval

/-!
# The classical gradient off a codimension-two set is the weak gradient
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE.Ch4Meyers

open MeasureTheory Set Filter

variable {d : ℕ} {w : Fin d → ℝ}

/-- Multiply a test function by the cutoff vanishing near the singular set; the result is a test
function on the domain with the singular set removed. -/
noncomputable def axisPunct {U : Set (Vec d)} (φ : WeakTestFunction U) {ε : ℝ} (hε : 0 < ε) :
    WeakTestFunction (U \ {x : Vec d | axisSq w x = 0}) where
  toFun := fun x => φ x * axisCutoff w ε x
  contDiff := φ.contDiff.mul (axisCutoff_smooth w ε)
  hasCompactSupport := φ.hasCompactSupport.mul_right
  tsupport_subset := by
    intro x hx
    refine ⟨φ.tsupport_subset (tsupport_mul_subset_left hx), ?_⟩
    intro hx0
    have hx0' : axisSq w x = 0 := hx0
    have hopen : IsOpen {y : Vec d | axisSq w y < ε ^ 2} :=
      isOpen_lt (contDiff_axisSq w).continuous continuous_const
    have hev : (fun y : Vec d => φ y * axisCutoff w ε y) =ᶠ[𝓝 x] (0 : Vec d → ℝ) := by
      filter_upwards [hopen.mem_nhds (show axisSq w x < ε ^ 2 by rw [hx0']; positivity)] with y hy
      rw [axisCutoff_eq_zero hε hy.le]; simp
    exact (notMem_tsupport_iff_eventuallyEq.mpr hev) hx

theorem axisPunct_partialDeriv {U : Set (Vec d)} (φ : WeakTestFunction U) {ε : ℝ} (hε : 0 < ε)
    (i : Fin d) (x : Vec d) :
    (axisPunct (w := w) φ hε).partialDeriv i x =
      φ.partialDeriv i x * axisCutoff w ε x +
        φ x * fderiv ℝ (axisCutoff w ε) x (basisVec i) := by
  have hφ : DifferentiableAt ℝ φ.toFun x := φ.contDiff.differentiable (by simp) x
  have hη : DifferentiableAt ℝ (axisCutoff w ε) x :=
    (axisCutoff_smooth w ε).differentiable (by simp) x
  unfold WeakTestFunction.partialDeriv
  change fderiv ℝ (φ.toFun * axisCutoff w ε) x (basisVec i) = _
  rw [fderiv_mul hφ hη]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- **Axis removal.**  A specified `L²` gradient agreeing with the classical gradient off the
codimension-two set `{s = 0}` is the weak gradient on the whole domain. -/
theorem hasWeakGradientOn_of_axis (hw : ∀ i, w i = 0 ∨ w i = 1) {i0 i1 : Fin d}
    (hi : i0 ≠ i1) (h0 : w i0 = 1) (h1 : w i1 = 1) {U : Set (Vec d)} (hU : IsOpen U)
    {f : Vec d → ℝ} {G : Vec d → Vec d}
    (hf : MemLp f 2 (volume.restrict U))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict U))
    (hSmooth : ContDiffOn ℝ 1 f (U \ {x : Vec d | axisSq w x = 0}))
    (hGrad : ∀ x ∈ U \ {x : Vec d | axisSq w x = 0}, classicalGradient f x = G x) :
    HasWeakGradientOn U f G := by
  have hZ := volume_axisSq_eq_zero hw h0
  have hZclosed : IsClosed {x : Vec d | axisSq w x = 0} :=
    isClosed_eq (contDiff_axisSq w).continuous continuous_const
  have hOpen : IsOpen (U \ {x : Vec d | axisSq w x = 0}) := hU.sdiff hZclosed
  have hClassical := HasWeakGradientOn.of_contDiffOn hOpen hSmooth
  let ε : ℕ → ℝ := fun n => 1 / (n + 1)
  have hε : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hμ : volume.restrict (U \ {x : Vec d | axisSq w x = 0}) = volume.restrict U :=
    Measure.restrict_congr_set (sdiff_null_ae_eq_self hZ)
  intro i
  rw [hasWeakPartialDerivOn_iff_forall_testFunction]
  intro φ
  have hφ2 := φ.memLp_toFun 2
  have hdφ2 := φ.memLp_partialDeriv i 2
  have hfdφ : Integrable (fun x => f x * φ.partialDeriv i x) (volume.restrict U) :=
    hf.integrable_mul hdφ2
  have hGφ : Integrable (fun x => G x i * φ x) (volume.restrict U) :=
    (hG i).integrable_mul hφ2
  have hA := tendsto_integral_mul_axisCutoff hw h0 hfdφ ε hε hε0
  have hB := tendsto_integral_mul_axisCutoff hw h0 hGφ ε hε hε0
  have hE := tendsto_integral_axis_error hw hi h0 h1 hf φ i ε hε hε0
  have hid (n : ℕ) :
      (∫ x in U, (f x * φ.partialDeriv i x) * axisCutoff w (ε n) x) +
        (∫ x in U, f x * φ x * fderiv ℝ (axisCutoff w (ε n)) x (basisVec i)) =
      -(∫ x in U, (G x i * φ x) * axisCutoff w (ε n) x) := by
    have hp := (hasWeakPartialDerivOn_iff_forall_testFunction.mp (hClassical i))
      (axisPunct (w := w) φ (hε n))
    have hEq : (∫ x in U \ {x : Vec d | axisSq w x = 0},
        classicalGradient f x i * (axisPunct (w := w) φ (hε n)) x) =
        ∫ x in U \ {x : Vec d | axisSq w x = 0},
          G x i * (axisPunct (w := w) φ (hε n)) x := by
      apply setIntegral_congr_fun hOpen.measurableSet
      intro x hx
      dsimp only
      rw [hGrad x hx]
    have hp' : (∫ x, f x * (axisPunct (w := w) φ (hε n)).partialDeriv i x
        ∂(volume.restrict (U \ {x : Vec d | axisSq w x = 0}))) =
      -∫ x, G x i * (axisPunct (w := w) φ (hε n)) x
        ∂(volume.restrict (U \ {x : Vec d | axisSq w x = 0})) := by
      rw [hp]
      congr 1
    rw [hμ] at hp'
    simp only [axisPunct_partialDeriv] at hp'
    have hfirst : Integrable (fun x => (f x * φ.partialDeriv i x) * axisCutoff w (ε n) x)
        (volume.restrict U) :=
      hfdφ.mul_bdd (axisCutoff_smooth w (ε n)).continuous.aestronglyMeasurable
        (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (axisCutoff_nonneg w _ x)]
          exact axisCutoff_le_one w _ x)
    have herr : Integrable (fun x => f x * φ x *
        fderiv ℝ (axisCutoff w (ε n)) x (basisVec i)) (volume.restrict U) := by
      refine (hf.integrable_mul hφ2).mul_bdd (c := 11 / ε n)
        (((axisCutoff_smooth w (ε n)).continuous_fderiv (by simp)).clm_apply
          continuous_const).aestronglyMeasurable
        (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs]
      refine (abs_partial_axisCutoff_le hw (hε n) x i).trans ?_
      have := hε n
      split_ifs
      · simp
      · simp; positivity
    have hsplit : (∫ x in U, f x * (φ.partialDeriv i x * axisCutoff w (ε n) x +
        φ x * fderiv ℝ (axisCutoff w (ε n)) x (basisVec i))) =
        (∫ x in U, (f x * φ.partialDeriv i x) * axisCutoff w (ε n) x) +
          (∫ x in U, f x * φ x * fderiv ℝ (axisCutoff w (ε n)) x (basisVec i)) := by
      rw [← integral_add hfirst herr]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only []
      ring
    have hrhs : (∫ x in U, G x i * (axisPunct (w := w) φ (hε n)) x) =
        ∫ x in U, (G x i * φ x) * axisCutoff w (ε n) x := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      show G x i * (φ.toFun x * axisCutoff w (ε n) x) =
        G x i * φ.toFun x * axisCutoff w (ε n) x
      ring
    rw [hsplit, hrhs] at hp'
    exact hp'
  have hleft := hA.add hE
  have hright := hB.neg
  rw [add_zero] at hleft
  exact tendsto_nhds_unique hleft
    (hright.congr' (Filter.Eventually.of_forall fun n => (hid n).symm))

end PDE.Ch4Meyers
