module

public import EllipticRegularity.Ch4.GreenDecay.Source
public import PDEFoundation.Sobolev.Inequalities.ConvexPoincareL2

/-!
# Step 1 of Lemma 4.35: the energy estimate `‖∇v‖_{L²(B_R)} ≤ C₁ r ‖g‖`

The Poincaré inequality with mean on the ball `B_r` (constant `2^d · 2r`) and the mean-zero source `g`
supported in `B_r` give the `r`-dependent energy bound.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4GreenDecay

open MeasureTheory PDE

noncomputable section

variable {d : ℕ}

/-- Poincaré inequality with mean on a round ball (4.137), constant `2^d · 2s`. -/
theorem ball_mean_poincare {s : ℝ} (hs : 0 < s) (w : H1Function (euclideanBall (0 : Vec d) s)) :
    (∫ x in euclideanBall (0 : Vec d) s,
        (w.toFun x - integralAverage (euclideanBall (0 : Vec d) s) w.toFun) ^ 2) ≤
      ((2 : ℝ) ^ d * (2 * s)) ^ 2 * ∫ x in euclideanBall (0 : Vec d) s, vecNormSq (w.grad x) :=
  centeredPoincare_sq_on_boundedConvexDomain (isOpenBoundedConvexDomain_euclideanBall 0 hs)
    (hasEuclideanDiameterLE_euclideanBall 0 hs) (by positivity)
    ⟨0, center_mem_euclideanBall 0 hs⟩ w

/-- The Poincaré inequality with mean for the restriction to a smaller ball. -/
theorem ball_mean_poincare_restrict {R s : ℝ} (hs : 0 < s) (hsR : s ≤ R)
    (v : H1Function (euclideanBall (0 : Vec d) R)) :
    (∫ x in euclideanBall (0 : Vec d) s,
        (v.toFun x - integralAverage (euclideanBall (0 : Vec d) s) v.toFun) ^ 2) ≤
      ((2 : ℝ) ^ d * (2 * s)) ^ 2 * ∫ x in euclideanBall (0 : Vec d) s, vecNormSq (v.grad x) :=
  ball_mean_poincare hs (v.restrict (isOpen_euclideanBall 0 s) (euclideanBall_mono hs.le hsR))

/-- **Energy estimate** (Step 1 of Lemma 4.35). -/
theorem dirichlet_energy_local {Λ R r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    {b : CoeffField d}
    (hbm : ∀ i j : Fin d,
      AEMeasurable (fun x => b x i j) (volumeOn (euclideanBall (0 : Vec d) R)))
    (hbell : ∀ x ∈ euclideanBall (0 : Vec d) R, IsEllipticMatrix 1 Λ (b x))
    {g : Vec d → ℝ} (hg : MemL2On (euclideanBall (0 : Vec d) R) g)
    (hgmean : (∫ x in euclideanBall (0 : Vec d) R, g x) = 0)
    (hgsupp : ∀ x, x ∉ euclideanBall (0 : Vec d) r → g x = 0)
    {v : H10Function (euclideanBall (0 : Vec d) R)}
    (hv : IsWeakDivergenceFormH10SolutionOn b (euclideanBall (0 : Vec d) R) v.toH1Function g
      (0 : Vec d → Vec d)) :
    Real.sqrt (∫ x in euclideanBall (0 : Vec d) R, vecNormSq (v.toH1Function.grad x)) ≤
      (2 ^ d * (2 * r)) *
        Real.sqrt (∫ x in euclideanBall (0 : Vec d) R, g x ^ 2) := by
  have hR : 0 < R := lt_of_lt_of_le hr hrR
  have hUm : MeasurableSet (euclideanBall (0 : Vec d) R) := measurableSet_euclideanBall _ _
  have hBr : euclideanBall (0 : Vec d) r ⊆ (euclideanBall (0 : Vec d) R) := euclideanBall_mono hr.le hrR
  have hfinU : IsFiniteMeasure (volumeOn (euclideanBall (0 : Vec d) R)) := isFiniteMeasure_volumeOn_euclideanBall 0 hR.le
  set c := integralAverage (euclideanBall (0 : Vec d) r) v.toH1Function.toFun with hc
  set h : Vec d → ℝ := (euclideanBall (0 : Vec d) r).indicator
    (fun x => v.toH1Function.toFun x - c) with hh
  have hvL2 : MemL2On (euclideanBall (0 : Vec d) R) v.toH1Function.toFun := v.toH1Function.memL2
  have hh2 : MemL2On (euclideanBall (0 : Vec d) R) h :=
    MemLp.indicator (measurableSet_euclideanBall _ _) (hvL2.sub (memLp_const c))
  have hgint : IntegrableOn g (euclideanBall (0 : Vec d) R) := hg.integrable (by norm_num)
  -- the energy identity and coercivity
  have hself := (hv v).2
  simp only [Pi.zero_apply, vecDot_zero_left', integral_zero, sub_zero] at hself
  have hcoerc := integral_vecNormSq_le_flux hUm hbm hbell v.toH1Function
  set A := ∫ x in (euclideanBall (0 : Vec d) R), vecNormSq (v.toH1Function.grad x) with hA
  set N := Real.sqrt (∫ x in (euclideanBall (0 : Vec d) R), g x ^ 2) with hN
  have hA0 : 0 ≤ A := integral_nonneg fun x => vecNormSq_nonneg _
  -- `∫ g v = ∫ g h`
  have hgv : (∫ x in (euclideanBall (0 : Vec d) R), g x * v.toH1Function.toFun x) = ∫ x in (euclideanBall (0 : Vec d) R), g x * h x := by
    have e1 : (∫ x in (euclideanBall (0 : Vec d) R), g x * v.toH1Function.toFun x) =
        ∫ x in (euclideanBall (0 : Vec d) R), g x * (v.toH1Function.toFun x - c) := by
      have : ∀ x, g x * (v.toH1Function.toFun x - c) =
          g x * v.toH1Function.toFun x - c * g x := fun x => by ring
      simp_rw [this]
      rw [integral_sub ((integrableOn_mul_of_memL2On hg hvL2)) (hgint.const_mul c),
        integral_const_mul, hgmean, mul_zero, sub_zero]
    rw [e1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ euclideanBall (0 : Vec d) r
    · simp only [hh, Set.indicator_of_mem hx]
    · simp only [hh, Set.indicator_of_notMem hx, hgsupp x hx, zero_mul]
  have hcs := integral_mul_le_sqrt hg hh2
  have hh2int : (∫ x in (euclideanBall (0 : Vec d) R), h x ^ 2) =
      ∫ x in euclideanBall (0 : Vec d) r,
        (v.toH1Function.toFun x - c) ^ 2 := by
    have : ∀ x, h x ^ 2 = (euclideanBall (0 : Vec d) r).indicator
        (fun x => (v.toH1Function.toFun x - c) ^ 2) x := fun x => by
      by_cases hx : x ∈ euclideanBall (0 : Vec d) r
      · simp only [hh, Set.indicator_of_mem hx]
      · simp only [hh, Set.indicator_of_notMem hx]; ring
    simp_rw [this]
    exact setIntegral_indicator_eq (measurableSet_euclideanBall _ _) hBr _
  have hpoinc := ball_mean_poincare_restrict hr hrR v.toH1Function
  have hmono : (∫ x in euclideanBall (0 : Vec d) r, vecNormSq (v.toH1Function.grad x)) ≤ A :=
    setIntegral_mono_set (integrableOn_vecNormSq_of_memVectorL2On v.toH1Function.gradMemL2)
      (Filter.Eventually.of_forall fun x => vecNormSq_nonneg _)
      (Filter.Eventually.of_forall hBr)
  have hI : (∫ x in euclideanBall (0 : Vec d) r, (v.toH1Function.toFun x - c) ^ 2) ≤
      ((2 : ℝ) ^ d * (2 * r)) ^ 2 * A :=
    hpoinc.trans (mul_le_mul_of_nonneg_left hmono (sq_nonneg _))
  have hsqrtI : Real.sqrt (∫ x in (euclideanBall (0 : Vec d) R), h x ^ 2) ≤ (2 ^ d * (2 * r)) * Real.sqrt A := by
    rw [hh2int]
    calc Real.sqrt _ ≤ Real.sqrt (((2 : ℝ) ^ d * (2 * r)) ^ 2 * A) := Real.sqrt_le_sqrt hI
      _ = (2 ^ d * (2 * r)) * Real.sqrt A := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  -- combine
  have hAle : A ≤ N * ((2 ^ d * (2 * r)) * Real.sqrt A) := by
    calc A ≤ ∫ x in (euclideanBall (0 : Vec d) R), vecDot (matVecMul (b x) (v.toH1Function.grad x)) (v.toH1Function.grad x) :=
          hcoerc
      _ = ∫ x in (euclideanBall (0 : Vec d) R), g x * v.toH1Function.toFun x := hself
      _ = ∫ x in (euclideanBall (0 : Vec d) R), g x * h x := hgv
      _ ≤ N * Real.sqrt (∫ x in (euclideanBall (0 : Vec d) R), h x ^ 2) := hcs
      _ ≤ N * ((2 ^ d * (2 * r)) * Real.sqrt A) :=
          mul_le_mul_of_nonneg_left hsqrtI (Real.sqrt_nonneg _)
  have hsA : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA0
  rcases eq_or_lt_of_le (Real.sqrt_nonneg A) with h0 | hpos
  · rw [← h0]; positivity
  · have : Real.sqrt A ^ 2 ≤ Real.sqrt A * (N * (2 ^ d * (2 * r))) := by
      nlinarith
    exact le_of_mul_le_mul_left (by nlinarith) hpos

end

end PDE.Ch4GreenDecay
