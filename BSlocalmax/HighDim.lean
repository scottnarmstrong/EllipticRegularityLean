module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import BSlocalmax.FaceInequalities
public import BSlocalmax.ShellSmoothing
public import PDEFoundation.PDE.Ch4.CaccioppoliEnergy

/-!
# The case d ≥ 4: Steps 1-3 and the iteration

This file collects the following pieces, in dependency order: Step1, Step2L2, Step2Alg, Step2, Iteration, Step3Alg, Step3, Step3Init, Main.
-/

-- ==== from Step1.lean ====
-- Step 1 (inequality (20)): gradient estimate for (u-k)₊ on the inner cube.


@[expose] public section

open MeasureTheory Set Filter PDE PDE.Ch4Infra

namespace PDE.BSlocalmax

variable {n : ℕ}

set_option maxHeartbeats 1600000 in
/-- **Step 1**: `∫_{Q_ρ} |∇(u-h-c)₊|² ≤ 10 Λ · shellBound(…, 4 ∫_shell ((u-h)₊² + |∇(u-h)₊|²))`. -/
theorem step1_gradient_bound (hn : 3 ≤ n) :
    ∃ Cb : ℝ, 0 < Cb ∧ ∀ {Λ ρ σ c h : ℝ} {a : CoeffField (n + 1)}, 1 / 2 ≤ ρ → ρ < σ → σ ≤ 1 →
      0 < c →
      (∀ i j, AEMeasurable (fun x => a x i j) (volumeOn (Metric.ball (0 : Vec (n + 1)) 1))) →
      (∀ x ∈ Metric.ball (0 : Vec (n + 1)) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ {u : H1Function (Metric.ball (0 : Vec (n + 1)) 1)},
        IsWeakDivergenceFormSubharmonicOn a (Metric.ball (0 : Vec (n + 1)) 1) u →
        ∫ x in Metric.ball (0 : Vec (n + 1)) ρ,
            vecNormSq ({y | h + c < u.toFun y}.indicator u.grad x) ≤
          10 * Λ * shellBound n Cb ρ ((ρ + σ) / 2) c 0
            (4 * ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < (ρ + σ) / 2},
              ((max (u.toFun x - h) 0) ^ 2 +
                vecNormSq ({y | h < u.toFun y}.indicator u.grad x))) := by
  obtain ⟨Cb, hCb, hcut⟩ := cutoff_H1 hn
  refine ⟨Cb, hCb, ?_⟩
  intro Λ ρ σ c h a hρ hρσ hσ hc ha hEll u hsub
  have hU : IsOpen (Metric.ball (0 : Vec (n + 1)) 1) := Metric.isOpen_ball
  have hfin : volume (Metric.ball (0 : Vec (n + 1)) 1) ≠ ⊤ :=
    Metric.isBounded_ball.measure_lt_top.ne
  have hΛ : 1 ≤ Λ := (hEll 0 (Metric.mem_ball_self one_pos)).lam_le_Lam
  have hρσ' : ρ < (ρ + σ) / 2 := by linarith
  have hσ' : (ρ + σ) / 2 < 1 := by linarith
  have hρ1 : ρ ≤ 1 := by linarith
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hθ : 0 < ε / (10 * Λ) := by positivity
  obtain ⟨K, η, hK0, hη, hη01, hη1, hη0, hint⟩ := hcut hρ hρσ hσ hc u _ hθ
  have hM : ∀ x, |η x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (hη01 x).1]; exact (hη01 x).2
  have hηsub : Function.support η ⊆ Metric.closedBall (0 : Vec (n + 1)) ((ρ + σ) / 2) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hc'
    exact hx (hη0 x (le_of_lt (not_le.1 hc')))
  have hηc : HasCompactSupport η :=
    HasCompactSupport.intro (isCompact_closedBall _ _) (fun x hx => by
      by_contra hx0
      exact hx (hηsub hx0))
  have hηU : tsupport η ⊆ Metric.ball (0 : Vec (n + 1)) 1 := by
    refine (closure_minimal hηsub Metric.isClosed_closedBall).trans ?_
    exact Metric.closedBall_subset_ball hσ'
  set k : ℝ := h + c with hk
  have hcacc := caccioppoli_energy_positivePart_ten_open hU hfin ha hEll hsub k hη hK0 hM hηc hηU
  -- Integrability of the energy density
  have hηcont : Continuous η := hη.continuous hK0
  have hwL2 : MemL2On (Metric.ball (0 : Vec (n + 1)) 1) (fun x => max (u.toFun x - k) 0) :=
    memL2On_positivePart_of_finite u hfin k
  have hξL2 : MemVectorL2On (Metric.ball (0 : Vec (n + 1)) 1)
      (fun x => {y | k < u.toFun y}.indicator u.grad x) := posPartGrad_gradMemL2 u k
  have hA : MemVectorL2On (Metric.ball (0 : Vec (n + 1)) 1)
      (fun x => η x • {y | k < u.toFun y}.indicator u.grad x) := fun i => by
    simpa only [Pi.smul_apply, smul_eq_mul] using memL2On_mul_bounded (hξL2 i) hηcont hM
  have hB : MemVectorL2On (Metric.ball (0 : Vec (n + 1)) 1)
      (fun x => max (u.toFun x - k) 0 • classicalGradient η x) := fun i => by
    simpa only [Pi.smul_apply, smul_eq_mul, classicalGradient] using
      memL2On_mul_partialDeriv hη hK0 hwL2 i
  have hABsq := integrableOn_vecNormSq_of_memVectorL2On (fun i => (hA i).add (hB i))
  -- inner cube
  have hin : ∫ x in Metric.ball (0 : Vec (n + 1)) ρ,
        vecNormSq ({y | k < u.toFun y}.indicator u.grad x) =
      ∫ x in Metric.ball (0 : Vec (n + 1)) ρ,
        vecNormSq (η x • {y | k < u.toFun y}.indicator u.grad x +
          max (u.toFun x - k) 0 • classicalGradient η x) := by
    refine setIntegral_congr_fun Metric.isOpen_ball.measurableSet (fun x hx => ?_)
    have hxn : ‖x‖ < ρ := by simpa using hx
    have hev : ∀ᶠ y in nhds x, η y = 1 :=
      Filter.mem_of_superset ((isOpen_lt continuous_norm continuous_const).mem_nhds hxn)
        (fun y hy => hη1 y (le_of_lt hy))
    have h0 := classicalGradient_eq_zero_of_eventually hev
    simp only [hη1 x hxn.le, h0, one_smul, smul_zero, add_zero]
  have hmono : ∫ x in Metric.ball (0 : Vec (n + 1)) ρ,
        vecNormSq (η x • {y | k < u.toFun y}.indicator u.grad x +
          max (u.toFun x - k) 0 • classicalGradient η x) ≤
      ∫ x in Metric.ball (0 : Vec (n + 1)) 1,
        vecNormSq (η x • {y | k < u.toFun y}.indicator u.grad x +
          max (u.toFun x - k) 0 • classicalGradient η x) :=
    setIntegral_mono_set hABsq (Filter.Eventually.of_forall (fun x => vecNormSq_nonneg' _))
      (HasSubset.Subset.eventuallyLE (Metric.ball_subset_ball hρ1))
  have hint' : ∫ x in Metric.ball (0 : Vec (n + 1)) 1,
      (max (u.toFun x - k) 0) ^ 2 * vecNormSq (classicalGradient η x) ≤
        shellBound n Cb ρ ((ρ + σ) / 2) c 0
          (4 * ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < (ρ + σ) / 2},
            ((max (u.toFun x - h) 0) ^ 2 +
              vecNormSq ({y | h < u.toFun y}.indicator u.grad x))) + ε / (10 * Λ) := by
    simpa only [hk, sub_sub] using hint
  calc ∫ x in Metric.ball (0 : Vec (n + 1)) ρ,
        vecNormSq ({y | h + c < u.toFun y}.indicator u.grad x)
      ≤ 10 * Λ * ∫ x in Metric.ball (0 : Vec (n + 1)) 1,
          (max (u.toFun x - k) 0) ^ 2 * vecNormSq (classicalGradient η x) :=
        hin.le.trans (hmono.trans hcacc)
    _ ≤ 10 * Λ * (shellBound n Cb ρ ((ρ + σ) / 2) c 0
          (4 * ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < (ρ + σ) / 2},
            ((max (u.toFun x - h) 0) ^ 2 +
              vecNormSq ({y | h < u.toFun y}.indicator u.grad x))) + ε / (10 * Λ)) :=
        mul_le_mul_of_nonneg_left hint' (by positivity)
    _ = _ := by
        field_simp

end PDE.BSlocalmax
end

-- ==== from Step2L2.lean ====
-- Step 2, L² part: Hölder + Sobolev on the cube + Chebyshev (as a weight).


@[expose] public section

open MeasureTheory Set PDE PDE.Ch4Infra
open scoped ENNReal

namespace PDE.BSlocalmax

set_option maxHeartbeats 1600000 in
theorem l2_control {d : ℕ} (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r h k : ℝ}, 1 / 2 ≤ r → r ≤ 1 → h < k →
      ∀ u : H1Function (Metric.ball (0 : Vec d) 1),
      (∫ x in Metric.ball (0 : Vec d) r, (max (u.toFun x - k) 0) ^ 2) ^ (1 / 2 : ℝ) ≤
        (C * (∫ x in Metric.ball (0 : Vec d) r,
            vecNormSq ({y | k < u.toFun y}.indicator u.grad x)) ^ (1 / 2 : ℝ) +
          (∫ x in Metric.ball (0 : Vec d) r, (max (u.toFun x - k) 0) ^ 2) ^ (1 / 2 : ℝ)) *
        ((∫ x in Metric.ball (0 : Vec d) r, (max (u.toFun x - h) 0) ^ 2) / (k - h) ^ 2) ^
          (1 / (d : ℝ)) := by
  obtain ⟨C, hC, hS⟩ := sobolev_cube_h1 hd
  refine ⟨C, hC, ?_⟩
  intro r h k hr hr1 hhk u
  have hr0 : 0 < r := by linarith
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2 : (0 : ℝ) < (d : ℝ) - 2 := by linarith
  have hc : 0 < k - h := sub_pos.2 hhk
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = sobolevConjugate d 2 := ⟨_, rfl⟩
  have hqe : q = 2 * d / ((d : ℝ) - 2) := by rw [hq]; unfold sobolevConjugate; ring
  have hq0 : 0 < q := by rw [hqe]; positivity
  have hUc := isOpenBoundedConvexDomain_cube d
  have hfin : volume (Metric.ball (0 : Vec d) 1) ≠ ⊤ := Metric.isBounded_ball.measure_lt_top.ne
  have hVU : Metric.ball (0 : Vec d) r ⊆ Metric.ball (0 : Vec d) 1 := Metric.ball_subset_ball hr1
  let w : H1Function (Metric.ball (0 : Vec d) r) :=
    (u.positivePartSubConst hUc k).restrict Metric.isOpen_ball hVU
  have hwv : ∀ x, w.toFun x = max (u.toFun x - k) 0 := fun x => rfl
  have hwg : ∀ x, w.grad x = {y | k < u.toFun y}.indicator u.grad x := fun x => rfl
  obtain ⟨hint, hSq⟩ := hS r hr0 _ rfl w
  rw [← hq] at hint hSq
  simp only [hwv, hwg] at hint hSq
  -- Abbreviations
  set V := Metric.ball (0 : Vec d) r with hV
  set c := k - h with hcdef
  -- Measurability / integrability
  have hmeasV : ∀ s : ℝ, AEStronglyMeasurable (fun x => max (u.toFun x - s) 0) (volume.restrict V) :=
    fun s => (memL2On_positivePart_of_finite u hfin s).aestronglyMeasurable.mono_measure
      (Measure.restrict_mono hVU le_rfl)
  have hsqV : ∀ s : ℝ, IntegrableOn (fun x => (max (u.toFun x - s) 0) ^ 2) V := fun s => by
    have hL2 := memL2On_positivePart_of_finite u hfin s
    have : IntegrableOn (fun x => (max (u.toFun x - s) 0) ^ 2) (Metric.ball (0 : Vec d) 1) := by
      simpa only [pow_two] using integrableOn_mul_of_memL2On hL2 hL2
    exact this.mono_set hVU
  -- Functions
  set f : Vec d → ℝ := fun x => (max (u.toFun x - k) 0) ^ 2 with hf
  set g : Vec d → ℝ := fun x => (max (u.toFun x - h) 0 / c) ^ (4 / (d : ℝ)) with hg
  have hf0 : ∀ x, 0 ≤ f x := fun x => sq_nonneg _
  have hg0 : ∀ x, 0 ≤ g x := fun x => Real.rpow_nonneg (div_nonneg (le_max_right _ _) hc.le) _
  have hfm : AEStronglyMeasurable f (volume.restrict V) :=
    (continuous_pow 2).comp_aestronglyMeasurable (hmeasV k)
  have hgm : AEStronglyMeasurable g (volume.restrict V) :=
    ((continuous_id.div_const c).rpow_const (fun _ => Or.inr (by positivity))).comp_aestronglyMeasurable
      (hmeasV h)
  -- Exponents
  have hpq : Real.HolderConjugate (q / 2) ((d : ℝ) / 2) := by
    refine ⟨?_, by positivity, by positivity⟩
    rw [hqe, inv_one]
    field_simp
    ring
  have hfp : ∀ x, f x ^ (q / 2) = |max (u.toFun x - k) 0| ^ q := fun x => by
    simp only [hf]
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    push_cast
    ring
  have hgp : ∀ x, g x ^ ((d : ℝ) / 2) = (max (u.toFun x - h) 0) ^ 2 / c ^ 2 := fun x => by
    simp only [hg]
    rw [← Real.rpow_mul (div_nonneg (le_max_right _ _) hc.le)]
    have : 4 / (d : ℝ) * (d / 2) = 2 := by field_simp; norm_num
    rw [this, Real.rpow_two, div_pow]
  -- MemLp
  have hfmem : MemLp f (ENNReal.ofReal (q / 2)) (volume.restrict V) := by
    refine (integrable_norm_rpow_iff hfm (ENNReal.ofReal_pos.2 (by positivity)).ne'
      ENNReal.ofReal_ne_top).1 ?_
    rw [ENNReal.toReal_ofReal (by positivity)]
    refine hint.congr (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [Real.norm_of_nonneg (hf0 x), hfp]
  have hgmem : MemLp g (ENNReal.ofReal ((d : ℝ) / 2)) (volume.restrict V) := by
    refine (integrable_norm_rpow_iff hgm (ENNReal.ofReal_pos.2 (by positivity)).ne'
      ENNReal.ofReal_ne_top).1 ?_
    rw [ENNReal.toReal_ofReal (by positivity)]
    refine ((hsqV h).div_const (c ^ 2)).congr (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [Real.norm_of_nonneg (hg0 x), hgp]
  -- Hölder
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0) hfmem hgmem
  -- Integrability of f * g (Young)
  have hfgint : IntegrableOn (fun x => f x * g x) V := by
    have hY : ∀ x, f x * g x ≤ f x ^ (q / 2) / (q / 2) + g x ^ ((d : ℝ) / 2) / ((d : ℝ) / 2) :=
      fun x => Real.young_inequality_of_nonneg (hf0 x) (hg0 x) hpq
    have hmaj : IntegrableOn (fun x => f x ^ (q / 2) / (q / 2) +
        g x ^ ((d : ℝ) / 2) / ((d : ℝ) / 2)) V := by
      refine (Integrable.div_const ?_ _).add (Integrable.div_const ?_ _)
      · exact hint.congr (Filter.Eventually.of_forall fun x => (hfp x).symm)
      · exact ((hsqV h).div_const (c ^ 2)).congr
          (Filter.Eventually.of_forall fun x => (hgp x).symm)
    refine Integrable.mono' hmaj (hfm.mul hgm) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hf0 x) (hg0 x))]
    exact hY x
  -- f ≤ f * g
  have hfg : ∀ x, f x ≤ f x * g x := fun x => by
    by_cases hx : u.toFun x ≤ k
    · have : f x = 0 := by
        simp only [hf]
        rw [max_eq_right (by linarith)]
        norm_num
      rw [this]; simp
    · push_neg at hx
      have hz : c ≤ max (u.toFun x - h) 0 := by
        refine le_trans ?_ (le_max_left _ _)
        simp only [hcdef]; linarith
      have h1 : 1 ≤ max (u.toFun x - h) 0 / c := by rw [le_div_iff₀ hc]; linarith
      have h2 : 1 ≤ g x := Real.one_le_rpow h1 (by positivity)
      nlinarith [hf0 x]
  have hI1 : ∫ x in V, f x ≤ ∫ x in V, f x * g x :=
    integral_mono (hsqV k) hfgint hfg
  -- Values of the Hölder factors
  have hF : ∫ x in V, f x ^ (q / 2) = ∫ x in V, |max (u.toFun x - k) 0| ^ q :=
    integral_congr_ae (Filter.Eventually.of_forall hfp)
  have hGg : ∫ x in V, g x ^ ((d : ℝ) / 2) =
      (∫ x in V, (max (u.toFun x - h) 0) ^ 2) / c ^ 2 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hgp), integral_div]
  rw [hF, hGg] at hH
  -- Norm estimate
  set Sq : ℝ := (∫ x in V, |max (u.toFun x - k) 0| ^ q) ^ (1 / q) with hSqdef
  set R : ℝ := (∫ x in V, (max (u.toFun x - h) 0) ^ 2) / c ^ 2 with hR
  set Vs : ℝ := ∫ x in V, (max (u.toFun x - k) 0) ^ 2 with hVs
  set Gs : ℝ := ∫ x in V, vecNormSq ({y | k < u.toFun y}.indicator u.grad x) with hGs
  have hS0 : 0 ≤ Sq := Real.rpow_nonneg (integral_nonneg fun x => by positivity) _
  have hR0 : 0 ≤ R := div_nonneg (integral_nonneg fun x => sq_nonneg _) (by positivity)
  have hVs0 : 0 ≤ Vs := integral_nonneg fun x => sq_nonneg _
  have hf_eq : ∫ x in V, f x = Vs := rfl
  -- (∫ |w|^q)^(1/(q/2)) = Sq^2
  have hSq2 : (∫ x in V, |max (u.toFun x - k) 0| ^ q) ^ (1 / (q / 2)) = Sq ^ 2 := by
    rw [hSqdef, ← Real.rpow_natCast, ← Real.rpow_mul
      (integral_nonneg fun x => by positivity)]
    congr 1
    push_cast
    field_simp
  have hRd : R ^ (1 / ((d : ℝ) / 2)) = (R ^ (1 / (d : ℝ))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR0]
    congr 1
    push_cast
    field_simp
  rw [hSq2, hRd] at hH
  have hVsle : Vs ≤ (Sq * R ^ (1 / (d : ℝ))) ^ 2 := by
    calc Vs = ∫ x in V, f x := rfl
      _ ≤ _ := hI1
      _ ≤ _ := hH
      _ = _ := by ring
  have hVsq : Vs ^ (1 / 2 : ℝ) ≤ Sq * R ^ (1 / (d : ℝ)) := by
    calc Vs ^ (1 / 2 : ℝ) ≤ ((Sq * R ^ (1 / (d : ℝ))) ^ 2) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hVs0 hVsle (by norm_num)
      _ = Sq * R ^ (1 / (d : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (mul_nonneg hS0 (Real.rpow_nonneg hR0 _))]
          norm_num
  -- Sobolev
  have hSb : Sq ≤ C * Gs ^ (1 / 2 : ℝ) + Vs ^ (1 / 2 : ℝ) := by
    refine hSq.trans ?_
    have h2r : (2 * r)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have hVn : 0 ≤ Vs ^ (1 / 2 : ℝ) := Real.rpow_nonneg hVs0 _
    nlinarith
  calc Vs ^ (1 / 2 : ℝ) ≤ Sq * R ^ (1 / (d : ℝ)) := hVsq
    _ ≤ (C * Gs ^ (1 / 2 : ℝ) + Vs ^ (1 / 2 : ℝ)) * R ^ (1 / (d : ℝ)) :=
        mul_le_mul_of_nonneg_right hSb (Real.rpow_nonneg hR0 _)

end PDE.BSlocalmax
end

-- ==== from Step2Alg.lean ====
-- Step 2, algebraic part: case distinction and `shellBound` at ε = 0.


@[expose] public section

namespace PDE.BSlocalmax

variable {n : ℕ}

/-- Case distinction: `s ≤ (C t + s) ε` and `s² ≤ M` imply `s² ≤ C² t² + 4 ε² M`. -/
theorem alg_split {s t M ε C : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hsM : s ^ 2 ≤ M) (h : s ≤ (C * t + s) * ε) :
    s ^ 2 ≤ C ^ 2 * t ^ 2 + 4 * ε ^ 2 * M := by
  have hM : 0 ≤ M := le_trans (sq_nonneg s) hsM
  by_cases hε2 : ε ≤ 1 / 2
  · have h1 : s ≤ 2 * (C * t * ε) := by nlinarith [mul_nonneg hC ht, mul_nonneg (mul_nonneg hC ht) hε]
    have h2 : s ^ 2 ≤ (2 * (C * t * ε)) ^ 2 := pow_le_pow_left₀ hs h1 2
    have h3 : (C * t * ε) ^ 2 ≤ (C * t) ^ 2 * (1 / 4) := by
      have : ε ^ 2 ≤ 1 / 4 := by nlinarith
      calc (C * t * ε) ^ 2 = (C * t) ^ 2 * ε ^ 2 := by ring
        _ ≤ (C * t) ^ 2 * (1 / 4) := mul_le_mul_of_nonneg_left this (sq_nonneg _)
    nlinarith [mul_nonneg (sq_nonneg ε) hM]
  · push_neg at hε2
    have : 1 ≤ 4 * ε ^ 2 := by nlinarith
    nlinarith [sq_nonneg (C * t), mul_le_mul_of_nonneg_right this hM]

lemma qexp_eq_two_mul_inv_dexp (hn : 3 ≤ n) : qexp n / 2 = 1 / dexp n := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have : (n : ℝ) - 2 ≠ 0 := by linarith
  unfold qexp dexp
  field_simp

/-- `shellBound` at `ε = 0`. -/
theorem shellBound_zero (hn : 3 ≤ n) {Cb ρ σ c P : ℝ} (hρσ : ρ < σ) (hc : 0 < c)
    (hCb : 0 ≤ Cb) (hP : 0 ≤ P) :
    shellBound n Cb ρ σ c 0 P =
      (σ - ρ) ^ (-(1 + qexp n / 2)) * (c ^ (-(qexp n - 2)) * (Cb * P) ^ (qexp n / 2)) := by
  have hδ := dexp_pos hn
  have hq := qexp_eq_two_mul_inv_dexp hn
  have hσρ : 0 < σ - ρ := sub_pos.2 hρσ
  unfold shellBound
  rw [zero_mul, Real.zero_rpow hδ.ne', mul_zero, add_zero, hq,
    Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hc.le]
  have e1 : -((qexp n - 2) * dexp n) * (1 / dexp n) = -(qexp n - 2) := by
    field_simp
  rw [e1, ← hq]

end PDE.BSlocalmax
end

-- ==== from Step2.lean ====
-- Step 2: improvement inequality (26) for the energy
-- `Eng u s r = ∫_{Q_r} ((u-s)₊² + |∇(u-s)₊|²)`.


@[expose] public section

open MeasureTheory Set PDE PDE.Ch4Infra

namespace PDE.BSlocalmax

variable {n : ℕ}

/-- Energy of `(u-s)₊` on the cube `Q_r`. -/
noncomputable def Eng {d : ℕ} (u : H1Function (Metric.ball (0 : Vec d) 1)) (s r : ℝ) : ℝ :=
  ∫ x in Metric.ball (0 : Vec d) r,
    ((max (u.toFun x - s) 0) ^ 2 + vecNormSq ({y | s < u.toFun y}.indicator u.grad x))

lemma eng_integrand_integrable {d : ℕ} (u : H1Function (Metric.ball (0 : Vec d) 1)) (s : ℝ)
    {r : ℝ} (hr : r ≤ 1) :
    IntegrableOn (fun x => (max (u.toFun x - s) 0) ^ 2 +
      vecNormSq ({y | s < u.toFun y}.indicator u.grad x)) (Metric.ball (0 : Vec d) r) := by
  have hfin : volume (Metric.ball (0 : Vec d) 1) ≠ ⊤ := Metric.isBounded_ball.measure_lt_top.ne
  have hL2 := memL2On_positivePart_of_finite u hfin s
  have h1 : IntegrableOn (fun x => (max (u.toFun x - s) 0) ^ 2) (Metric.ball (0 : Vec d) 1) := by
    simpa only [pow_two] using integrableOn_mul_of_memL2On hL2 hL2
  have hξ : MemVectorL2On (Metric.ball (0 : Vec d) 1)
      (fun x => {y | s < u.toFun y}.indicator u.grad x) := posPartGrad_gradMemL2 u s
  have h2 := integrableOn_vecNormSq_of_memVectorL2On hξ
  exact (h1.add h2).mono_set (Metric.ball_subset_ball hr)

lemma eng_integrand_nonneg {d : ℕ} (u : H1Function (Metric.ball (0 : Vec d) 1)) (s : ℝ) (x : Vec d) :
    0 ≤ (max (u.toFun x - s) 0) ^ 2 + vecNormSq ({y | s < u.toFun y}.indicator u.grad x) :=
  add_nonneg (sq_nonneg _) (vecNormSq_nonneg' _)

/-- Pure algebra of the constants. -/
lemma G_const_alg (hn : 3 ≤ n) {Λ Cb ρ σ c E : ℝ} (hρσ : ρ < σ) (hCb : 0 ≤ Cb) (hE : 0 ≤ E) :
    10 * Λ * (((ρ + σ) / 2 - ρ) ^ (-(1 + qexp n / 2)) *
      (c ^ (-(qexp n - 2)) * (Cb * (4 * E)) ^ (qexp n / 2))) =
    Λ * (10 * 2 ^ (1 + qexp n / 2) * (4 * Cb) ^ (qexp n / 2)) * (σ - ρ) ^ (-(1 + qexp n / 2)) *
      c ^ (-(qexp n - 2)) * E ^ (qexp n / 2) := by
  have hσρ : 0 < σ - ρ := sub_pos.2 hρσ
  have e1 : (ρ + σ) / 2 - ρ = (σ - ρ) / 2 := by ring
  have e2 : Cb * (4 * E) = (4 * Cb) * E := by ring
  have e3 : ((σ - ρ) / 2) ^ (-(1 + qexp n / 2)) =
      2 ^ (1 + qexp n / 2) * (σ - ρ) ^ (-(1 + qexp n / 2)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_neg hσρ.le, Real.div_rpow hσρ.le (by norm_num)]
    field_simp
  rw [e1, e2, e3, Real.mul_rpow (by positivity) hE]
  ring

set_option maxHeartbeats 1600000 in
/-- **Step 2**: improvement (26) in energy form. -/
theorem step2_E (hn : 3 ≤ n) :
    ∃ A : ℝ, 0 < A ∧ ∀ {Λ ρ σ h k : ℝ} {a : CoeffField (n + 1)}, 1 / 2 ≤ ρ → ρ < σ → σ ≤ 1 →
      h < k →
      (∀ i j, AEMeasurable (fun x => a x i j) (volumeOn (Metric.ball (0 : Vec (n + 1)) 1))) →
      (∀ x ∈ Metric.ball (0 : Vec (n + 1)) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ {u : H1Function (Metric.ball (0 : Vec (n + 1)) 1)},
        IsWeakDivergenceFormSubharmonicOn a (Metric.ball (0 : Vec (n + 1)) 1) u →
        Eng u k ρ ≤
          A * Λ * (σ - ρ) ^ (-(1 + qexp n / 2)) * (k - h) ^ (-(qexp n - 2)) *
              Eng u h σ ^ (qexp n / 2) +
            4 * Eng u h σ ^ (1 + 2 / ((n : ℝ) + 1)) * (k - h) ^ (-(4 / ((n : ℝ) + 1))) := by
  obtain ⟨Cb, hCb, hS1⟩ := step1_gradient_bound hn
  obtain ⟨C2, hC2, hL⟩ := l2_control (d := n + 1) (by omega)
  refine ⟨(1 + C2 ^ 2) * (10 * 2 ^ (1 + qexp n / 2) * (4 * Cb) ^ (qexp n / 2)), by positivity, ?_⟩
  intro Λ ρ σ h k a hρ hρσ hσ hhk ha hEll u hsub
  have hΛ : 1 ≤ Λ := (hEll 0 (Metric.mem_ball_self one_pos)).lam_le_Lam
  have hc : 0 < k - h := sub_pos.2 hhk
  have hρ1 : ρ ≤ 1 := by linarith
  have hρσ' : (ρ + σ) / 2 ≤ σ := by linarith
  have hd : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  -- Abbreviations
  set Eh : ℝ := Eng u h σ with hEh
  set V : ℝ := ∫ x in Metric.ball (0 : Vec (n + 1)) ρ, (max (u.toFun x - k) 0) ^ 2 with hV
  set G : ℝ := ∫ x in Metric.ball (0 : Vec (n + 1)) ρ,
    vecNormSq ({y | k < u.toFun y}.indicator u.grad x) with hG
  set M : ℝ := ∫ x in Metric.ball (0 : Vec (n + 1)) ρ, (max (u.toFun x - h) 0) ^ 2 with hM
  have hfin : volume (Metric.ball (0 : Vec (n + 1)) 1) ≠ ⊤ := Metric.isBounded_ball.measure_lt_top.ne
  have hsqI : ∀ s : ℝ, IntegrableOn (fun x => (max (u.toFun x - s) 0) ^ 2)
      (Metric.ball (0 : Vec (n + 1)) ρ) := fun s => by
    have hL2 := memL2On_positivePart_of_finite u hfin s
    have : IntegrableOn (fun x => (max (u.toFun x - s) 0) ^ 2) (Metric.ball (0 : Vec (n + 1)) 1) := by
      simpa only [pow_two] using integrableOn_mul_of_memL2On hL2 hL2
    exact this.mono_set (Metric.ball_subset_ball hρ1)
  have hξI : ∀ s : ℝ, IntegrableOn (fun x => vecNormSq ({y | s < u.toFun y}.indicator u.grad x))
      (Metric.ball (0 : Vec (n + 1)) ρ) := fun s => by
    have hξ : MemVectorL2On (Metric.ball (0 : Vec (n + 1)) 1)
        (fun x => {y | s < u.toFun y}.indicator u.grad x) := posPartGrad_gradMemL2 u s
    exact (integrableOn_vecNormSq_of_memVectorL2On hξ).mono_set (Metric.ball_subset_ball hρ1)
  have hV0 : 0 ≤ V := integral_nonneg fun x => sq_nonneg _
  have hG0 : 0 ≤ G := integral_nonneg fun x => vecNormSq_nonneg' _
  have hM0 : 0 ≤ M := integral_nonneg fun x => sq_nonneg _
  have hEk : Eng u k ρ = V + G := integral_add (hsqI k) (hξI k)
  -- V ≤ M
  have hVM : V ≤ M := integral_mono (hsqI k) (hsqI h) (fun x => by
    have h1 : max (u.toFun x - k) 0 ≤ max (u.toFun x - h) 0 :=
      max_le_max (by linarith) le_rfl
    exact pow_le_pow_left₀ (le_max_right _ _) h1 2)
  -- M ≤ Eh
  have hEh0 : 0 ≤ Eh := integral_nonneg fun x => eng_integrand_nonneg u h x
  have hMEh : M ≤ Eh := by
    have h1 : M ≤ ∫ x in Metric.ball (0 : Vec (n + 1)) ρ, ((max (u.toFun x - h) 0) ^ 2 +
        vecNormSq ({y | h < u.toFun y}.indicator u.grad x)) :=
      integral_mono (hsqI h) (eng_integrand_integrable u h hρ1)
        (fun x => le_add_of_nonneg_right (vecNormSq_nonneg' _))
    refine h1.trans ?_
    exact setIntegral_mono_set (eng_integrand_integrable u h hσ)
      (Filter.Eventually.of_forall (eng_integrand_nonneg u h))
      (HasSubset.Subset.eventuallyLE (Metric.ball_subset_ball hρσ.le))
  -- shell integral ≤ Eh
  have hI : ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < (ρ + σ) / 2},
      ((max (u.toFun x - h) 0) ^ 2 + vecNormSq ({y | h < u.toFun y}.indicator u.grad x)) ≤ Eh := by
    refine setIntegral_mono_set (eng_integrand_integrable u h hσ)
      (Filter.Eventually.of_forall (eng_integrand_nonneg u h))
      (HasSubset.Subset.eventuallyLE ?_)
    intro x hx
    rw [Metric.mem_ball, dist_zero_right]
    linarith [hx.2]
  have hI0 : 0 ≤ ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < (ρ + σ) / 2},
      ((max (u.toFun x - h) 0) ^ 2 + vecNormSq ({y | h < u.toFun y}.indicator u.grad x)) :=
    integral_nonneg fun x => eng_integrand_nonneg u h x
  -- Step 1
  have h1 := hS1 (Λ := Λ) (ρ := ρ) (σ := σ) (c := k - h) (h := h) hρ hρσ hσ hc ha hEll hsub
  rw [add_sub_cancel] at h1
  have hGle : G ≤ 10 * Λ * shellBound n Cb ρ ((ρ + σ) / 2) (k - h) 0 (4 * Eh) := by
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    exact shellBound_mono hn hCb.le (by linarith) hc le_rfl (by positivity) (by linarith)
  rw [shellBound_zero hn (by linarith) hc hCb.le (by positivity), G_const_alg hn hρσ hCb.le hEh0] at hGle
  -- L² control
  have hl := hL (r := ρ) (h := h) (k := k) hρ hρ1 hhk u
  -- alg_split
  have hsqrt : ∀ x : ℝ, 0 ≤ x → (x ^ (1 / 2 : ℝ)) ^ 2 = x := fun x hx => by
    rw [← Real.sqrt_eq_rpow]; exact Real.sq_sqrt hx
  have hε0 : 0 ≤ (M / (k - h) ^ 2) ^ (1 / ((n + 1 : ℕ) : ℝ)) :=
    Real.rpow_nonneg (div_nonneg hM0 (by positivity)) _
  have hal := alg_split (s := V ^ (1 / 2 : ℝ)) (t := G ^ (1 / 2 : ℝ))
    (M := M) (ε := (M / (k - h) ^ 2) ^ (1 / ((n + 1 : ℕ) : ℝ))) (C := C2)
    (Real.rpow_nonneg hV0 _) (Real.rpow_nonneg hG0 _) hε0 hC2.le
    (by rw [hsqrt V hV0]; exact hVM) hl
  rw [hsqrt V hV0, hsqrt G hG0] at hal
  -- ε²·M ≤ Eh^(1+2/d) c^(-4/d)
  have hε2M : 4 * ((M / (k - h) ^ 2) ^ (1 / ((n + 1 : ℕ) : ℝ))) ^ 2 * M ≤
      4 * Eh ^ (1 + 2 / ((n : ℝ) + 1)) * (k - h) ^ (-(4 / ((n : ℝ) + 1))) := by
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hc2 : 0 < (k - h) ^ 2 := by positivity
    have e1 : ((M / (k - h) ^ 2) ^ (1 / ((n : ℝ) + 1))) ^ 2 = (M / (k - h) ^ 2) ^ (2 / ((n : ℝ) + 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hM0 hc2.le)]
      congr 1; push_cast; ring
    have e2 : (M / (k - h) ^ 2) ^ (2 / ((n : ℝ) + 1)) ≤ (Eh / (k - h) ^ 2) ^ (2 / ((n : ℝ) + 1)) :=
      Real.rpow_le_rpow (div_nonneg hM0 hc2.le) (div_le_div_of_nonneg_right hMEh hc2.le) (by positivity)
    have e3 : (Eh / (k - h) ^ 2) ^ (2 / ((n : ℝ) + 1)) * Eh =
        Eh ^ (1 + 2 / ((n : ℝ) + 1)) * (k - h) ^ (-(4 / ((n : ℝ) + 1))) := by
      rw [Real.div_rpow hEh0 hc2.le, ← Real.rpow_natCast (k - h) 2, ← Real.rpow_mul hc.le,
        Real.rpow_neg hc.le, Real.rpow_add' hEh0 (by positivity), Real.rpow_one]
      have : ((2 : ℕ) : ℝ) * (2 / ((n : ℝ) + 1)) = 4 / ((n : ℝ) + 1) := by push_cast; ring
      rw [this]
      field_simp
    rw [e1]
    calc 4 * (M / (k - h) ^ 2) ^ (2 / ((n : ℝ) + 1)) * M
        ≤ 4 * (Eh / (k - h) ^ 2) ^ (2 / ((n : ℝ) + 1)) * Eh := by
          have := mul_le_mul e2 hMEh hM0 (Real.rpow_nonneg (div_nonneg hEh0 hc2.le) _)
          linarith
      _ = _ := by rw [mul_assoc, e3]; ring
  -- Assembly
  have hGnn : 0 ≤ G := hG0
  calc Eng u k ρ = V + G := hEk
    _ ≤ (1 + C2 ^ 2) * G + 4 * ((M / (k - h) ^ 2) ^ (1 / ((n + 1 : ℕ) : ℝ))) ^ 2 * M := by
        nlinarith [sq_nonneg C2]
    _ ≤ (1 + C2 ^ 2) * (Λ * (10 * 2 ^ (1 + qexp n / 2) * (4 * Cb) ^ (qexp n / 2)) *
          (σ - ρ) ^ (-(1 + qexp n / 2)) * (k - h) ^ (-(qexp n - 2)) * Eh ^ (qexp n / 2)) +
        4 * Eh ^ (1 + 2 / ((n : ℝ) + 1)) * (k - h) ^ (-(4 / ((n : ℝ) + 1))) := by
        have := mul_le_mul_of_nonneg_left hGle (by positivity : (0 : ℝ) ≤ 1 + C2 ^ 2)
        linarith
    _ = _ := by ring

end PDE.BSlocalmax
end

-- ==== from Iteration.lean ====
/-!
# The nonlinear iteration (Step 3 of Lemma 3, Bella–Schäffner), case `f = 0`

Abstract setting.  `F k r` plays the role of `J(k, r) = ‖(v - k)₊‖_{W^{1,2}(Q_r)}`.
Hypotheses (`IterHyp`):
* `F ≥ 0`, antitone in `k`, monotone in `r`;
* the one-step improvement (26) with `f = 0`: for `h < k` and `1/2 ≤ ρ < σ ≤ 1`
  `F k ρ ≤ a (σ-ρ)^{-α} F h σ ^ γ (k-h)^{-(γ-1)} + b F h σ ^ (1+θ) (k-h)^{-θ}`,
  where `γ = 2*/2 = (d-1)/(d-3)`, `α = 1/2 + 2/2*`, `θ = 2/(d-2)`, `a ~ c₁ c_m M₁`, `b = c₂`.

Conclusion: `F (k₀ + c (1 + a^{1/(γ-1)}) F k₀ 1) (1/2) = 0`, with `c = c(γ, θ, b)`.

Proof.  `ρ = 2^{α/(γ-1)}`, `τ = 1/(2ρ)` (so `τ ρ = 1/2`), `J₀ = F k₀ 1`,
`σ_i = 1/2 + 2^{-i-1}`, `k_i = k₀ + ∑_{j<i} D_j`, `D_j = P 2^{-j} + Q τ^j`,
`P = (2a/τ)^{1/(γ-1)} ρ² J₀`, `Q = (2b/τ)^{1/θ} J₀`.  Claim `F k_i σ_i ≤ τ^i J₀`:
the two terms of the step inequality are each `≤ τ^{i+1} J₀ / 2` by `rpow_term_le`.
Summation with `∑ 2^{-j} ≤ 2`, `τ ≤ 1/2`, then `τ^i → 0`.
-/

@[expose] public section

namespace PDE.BSlocalmax

/-- Hypotheses of the iteration, packaged. -/
structure IterHyp (γ θ α a b : ℝ) (F : ℝ → ℝ → ℝ) : Prop where
  nonneg : ∀ k r, 0 ≤ F k r
  anti : ∀ k k' r r', k ≤ k' → r' ≤ r → F k' r' ≤ F k r
  step : ∀ h k ρ σ, h < k → 1 / 2 ≤ ρ → ρ < σ → σ ≤ 1 →
    F k ρ ≤ a * (σ - ρ) ^ (-α) * F h σ ^ γ * (k - h) ^ (-(γ - 1)) +
      b * F h σ ^ (1 + θ) * (k - h) ^ (-θ)

/-- Exponent algebra: `A x^γ Δ^{-(γ-1)} ≤ t` as soon as `Δ ≥ x (A x / t)^{1/(γ-1)}`. -/
theorem rpow_term_le {γ A x Δ t : ℝ} (hγ : 1 < γ) (hA : 0 < A) (hx : 0 < x) (hΔ : 0 < Δ)
    (ht : 0 < t) (h : x * (A * x / t) ^ (1 / (γ - 1)) ≤ Δ) :
    A * x ^ γ * Δ ^ (-(γ - 1)) ≤ t := by
  have hr : 0 < γ - 1 := sub_pos.mpr hγ
  have hxr : 0 < x ^ (γ - 1) := Real.rpow_pos_of_pos hx _
  have hΔr : 0 < Δ ^ (γ - 1) := Real.rpow_pos_of_pos hΔ _
  have h1 : (A * x / t) ^ (1 / (γ - 1)) ≤ Δ / x := by
    rw [le_div_iff₀ hx, mul_comm]
    exact h
  have h2 : A * x / t ≤ (Δ / x) ^ (γ - 1) := by
    have h3 := Real.rpow_le_rpow (by positivity) h1 hr.le
    rwa [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hr.ne',
      Real.rpow_one] at h3
  rw [Real.div_rpow hΔ.le hx.le] at h2
  have h3 : A * x * x ^ (γ - 1) ≤ t * Δ ^ (γ - 1) := by
    have h4 := (div_le_div_iff₀ ht hxr).mp h2
    rw [mul_comm t]
    exact h4
  have hxγ : x ^ γ = x * x ^ (γ - 1) := by
    conv_lhs => rw [show γ = 1 + (γ - 1) by ring]
    rw [Real.rpow_add hx, Real.rpow_one]
  rw [hxγ, Real.rpow_neg hΔ.le, ← div_eq_mul_inv, div_le_iff₀ hΔr]
  have e : A * (x * x ^ (γ - 1)) = A * x * x ^ (γ - 1) := by ring
  rw [e]
  exact h3

theorem one_le_rho {γ α : ℝ} (hγ : 1 < γ) (hα : 0 ≤ α) : 1 ≤ (2 : ℝ) ^ (α / (γ - 1)) :=
  Real.one_le_rpow (by norm_num) (div_nonneg hα (sub_nonneg.2 hγ.le))

/-- `((2^{-(i+2)})^{-α})^{1/(γ-1)} = (2^{α/(γ-1)})^{i+2}`. -/
theorem weight_pow {γ α : ℝ} (i : ℕ) :
    (((1 / 2 : ℝ) ^ (i + 2)) ^ (-α)) ^ (1 / (γ - 1)) = ((2 : ℝ) ^ (α / (γ - 1))) ^ (i + 2) := by
  have h0 : (0 : ℝ) ≤ (1 / 2) ^ (i + 2) := by positivity
  rw [← Real.rpow_mul h0, ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  have e : (1 / 2 : ℝ) = 2⁻¹ := by norm_num
  rw [e, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  push_cast
  ring

/-- **Iteration lemma** (Step 3, `f = 0`). -/
theorem iteration_limit {γ θ α b : ℝ} (hγ : 1 < γ) (hθ : 0 < θ) (hα : 0 ≤ α) (hb : 0 < b) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : ℝ, 0 < a → ∀ F : ℝ → ℝ → ℝ, IterHyp γ θ α a b F →
      ∀ k₀ : ℝ, F (k₀ + c * (1 + a ^ (1 / (γ - 1))) * F k₀ 1) (1 / 2) = 0 := by
  have hr : 0 < γ - 1 := sub_pos.mpr hγ
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (2 : ℝ) ^ (α / (γ - 1)) := ⟨_, rfl⟩
  have hρ1 : 1 ≤ ρ := by rw [hρ]; exact one_le_rho hγ hα
  have hρ0 : 0 < ρ := by linarith
  have hρne : ρ ≠ 0 := hρ0.ne'
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = 1 / (2 * ρ) := ⟨_, rfl⟩
  have hτ0 : 0 < τ := by rw [hτ]; positivity
  have hτne : τ ≠ 0 := hτ0.ne'
  have hτ1 : τ ≤ 1 / 2 := by
    rw [hτ, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hτρ : τ * ρ = 1 / 2 := by rw [hτ]; field_simp
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ, K1 = (2 / τ) ^ (1 / (γ - 1)) * ρ ^ 2 := ⟨_, rfl⟩
  obtain ⟨K3, hK3⟩ : ∃ K3 : ℝ, K3 = (2 * b / τ) ^ (1 / θ) := ⟨_, rfl⟩
  have hK1pos : 0 < K1 := by rw [hK1]; positivity
  have hK3pos : 0 < K3 := by rw [hK3]; positivity
  have hm : 0 ≤ max K1 K3 := le_max_of_le_left hK1pos.le
  refine ⟨2 * max K1 K3 + 1, by linarith, ?_⟩
  intro a ha F hF k₀
  obtain ⟨J0, hJ0⟩ : ∃ J0 : ℝ, J0 = F k₀ 1 := ⟨_, rfl⟩
  rw [← hJ0]
  have hJ0nn : 0 ≤ J0 := by rw [hJ0]; exact hF.nonneg _ _
  rcases hJ0nn.eq_or_lt with h0 | hpos
  · -- trivial case `J0 = 0`
    rw [← h0, mul_zero, add_zero]
    have h1 := hF.anti k₀ k₀ 1 (1 / 2) le_rfl (by norm_num)
    have h2 := hF.nonneg k₀ (1 / 2)
    rw [← hJ0, ← h0] at h1
    linarith
  · have hJne : J0 ≠ 0 := hpos.ne'
    obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (2 * a / τ) ^ (1 / (γ - 1)) * ρ ^ 2 * J0 := ⟨_, rfl⟩
    obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = K3 * J0 := ⟨_, rfl⟩
    have hP0 : 0 < P := by rw [hP]; positivity
    have hQ0 : 0 < Q := by rw [hQ]; positivity
    obtain ⟨S, hS⟩ : ∃ S : ℕ → ℝ, ∀ i, S i =
        ∑ j ∈ Finset.range i, (P * (1 / 2 : ℝ) ^ j + Q * τ ^ j) := ⟨fun i => _, fun i => rfl⟩
    have hS0 : S 0 = 0 := by rw [hS, Finset.sum_range_zero]
    have hSsucc : ∀ i, S (i + 1) = S i + (P * (1 / 2 : ℝ) ^ i + Q * τ ^ i) := by
      intro i; rw [hS, hS, Finset.sum_range_succ]
    have hSle : ∀ i, S i ≤ 2 * P + 2 * Q := by
      intro i
      have hs1 := sum_geometric_two_le i
      have hs3 : ∑ j ∈ Finset.range i, τ ^ j ≤ 2 :=
        le_trans (Finset.sum_le_sum fun j _ => pow_le_pow_left₀ hτ0.le hτ1 j) hs1
      rw [hS, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      linarith [mul_le_mul_of_nonneg_left hs1 hP0.le, mul_le_mul_of_nonneg_left hs3 hQ0.le]
    -- the main induction
    have claim : ∀ i : ℕ, F (k₀ + S i) (1 / 2 + (1 / 2 : ℝ) ^ (i + 1)) ≤ τ ^ i * J0 := by
      intro i
      induction i with
      | zero =>
        have e : (1 / 2 : ℝ) + (1 / 2) ^ (0 + 1) = 1 := by norm_num
        rw [hS0, add_zero, pow_zero, one_mul, e]
        exact hJ0.symm.le
      | succ i ih =>
        have hx : 0 < τ ^ i * J0 := by positivity
        obtain ⟨D, hD⟩ : ∃ D : ℝ, D = P * (1 / 2 : ℝ) ^ i + Q * τ ^ i := ⟨_, rfl⟩
        have hDpos : 0 < D := by rw [hD]; positivity
        have hFi0 := hF.nonneg (k₀ + S i) (1 / 2 + (1 / 2 : ℝ) ^ (i + 1))
        have hkh : k₀ + S (i + 1) - (k₀ + S i) = D := by rw [hSsucc, hD]; ring
        have hgap : (1 / 2 + (1 / 2 : ℝ) ^ (i + 1)) - (1 / 2 + (1 / 2 : ℝ) ^ (i + 1 + 1))
            = (1 / 2 : ℝ) ^ (i + 2) := by ring
        have hpos1 : (0 : ℝ) < (1 / 2) ^ (i + 1) := by positivity
        have hstep := hF.step (k₀ + S i) (k₀ + S (i + 1)) (1 / 2 + (1 / 2 : ℝ) ^ (i + 1 + 1))
          (1 / 2 + (1 / 2 : ℝ) ^ (i + 1))
          (by rw [hSsucc]; have : 0 < P * (1 / 2 : ℝ) ^ i + Q * τ ^ i := by positivity
              linarith)
          (by have : (0 : ℝ) ≤ (1 / 2) ^ (i + 1 + 1) := by positivity
              linarith)
          (by rw [pow_succ (1 / 2 : ℝ) (i + 1)]; linarith)
          (by rw [pow_succ (1 / 2 : ℝ) i]
              have := pow_le_one₀ (n := i) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
              linarith)
        rw [hkh, hgap] at hstep
        obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ((1 / 2 : ℝ) ^ (i + 2)) ^ (-α) := ⟨_, rfl⟩
        rw [← hW] at hstep
        have hW0 : 0 < W := by rw [hW]; positivity
        have hWp : W ^ (1 / (γ - 1)) = ρ ^ (i + 2) := by rw [hW, weight_pow, hρ]
        have htpos : 0 < τ ^ (i + 1) * J0 / 2 := by positivity
        have hτi : τ ^ i * ρ ^ (i + 2) = ρ ^ 2 * (1 / 2 : ℝ) ^ i := by
          rw [← hτρ, mul_pow]; ring
        -- first term
        have hcond1 : (τ ^ i * J0) *
            ((a * W) * (τ ^ i * J0) / (τ ^ (i + 1) * J0 / 2)) ^ (1 / (γ - 1)) ≤ D := by
          have e1 : (a * W) * (τ ^ i * J0) / (τ ^ (i + 1) * J0 / 2) = (2 * a / τ) * W := by
            field_simp; ring
          rw [e1, Real.mul_rpow (by positivity) hW0.le, hWp]
          have e2 : (τ ^ i * J0) * ((2 * a / τ) ^ (1 / (γ - 1)) * ρ ^ (i + 2))
              = P * (1 / 2 : ℝ) ^ i := by
            rw [hP]
            linear_combination ((2 * a / τ) ^ (1 / (γ - 1)) * J0) * hτi
          rw [e2, hD]
          have : 0 ≤ Q * τ ^ i := by positivity
          linarith
        have T1 := rpow_term_le hγ (mul_pos ha hW0) hx hDpos htpos hcond1
        -- second term
        have hq : (1 + θ) - 1 = θ := by ring
        have hcond2 : (τ ^ i * J0) *
            (b * (τ ^ i * J0) / (τ ^ (i + 1) * J0 / 2)) ^ (1 / ((1 + θ) - 1)) ≤ D := by
          have e3 : b * (τ ^ i * J0) / (τ ^ (i + 1) * J0 / 2) = 2 * b / τ := by
            field_simp; ring
          rw [e3, hq, ← hK3]
          have e4 : (τ ^ i * J0) * K3 = Q * τ ^ i := by rw [hQ]; ring
          rw [e4, hD]
          have : 0 ≤ P * (1 / 2 : ℝ) ^ i := by positivity
          linarith
        have T2 := rpow_term_le (γ := 1 + θ) (by linarith) hb hx hDpos htpos hcond2
        rw [hq] at T2
        have M1 : a * W * F (k₀ + S i) (1 / 2 + (1 / 2 : ℝ) ^ (i + 1)) ^ γ * D ^ (-(γ - 1))
            ≤ a * W * (τ ^ i * J0) ^ γ * D ^ (-(γ - 1)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hFi0 ih (by linarith))
              (mul_pos ha hW0).le)
            (Real.rpow_nonneg hDpos.le _)
        have M2 : b * F (k₀ + S i) (1 / 2 + (1 / 2 : ℝ) ^ (i + 1)) ^ (1 + θ) * D ^ (-θ)
            ≤ b * (τ ^ i * J0) ^ (1 + θ) * D ^ (-θ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hFi0 ih (by linarith)) hb.le)
            (Real.rpow_nonneg hDpos.le _)
        calc F (k₀ + S (i + 1)) (1 / 2 + (1 / 2 : ℝ) ^ (i + 1 + 1))
            ≤ _ := hstep
          _ ≤ a * W * (τ ^ i * J0) ^ γ * D ^ (-(γ - 1)) +
              b * (τ ^ i * J0) ^ (1 + θ) * D ^ (-θ) := add_le_add M1 M2
          _ ≤ τ ^ (i + 1) * J0 / 2 + τ ^ (i + 1) * J0 / 2 := add_le_add T1 T2
          _ = τ ^ (i + 1) * J0 := by ring
    -- conclusion
    have hap : 0 ≤ a ^ (1 / (γ - 1)) := Real.rpow_nonneg ha.le _
    have hP' : P = K1 * a ^ (1 / (γ - 1)) * J0 := by
      rw [hP, hK1, show 2 * a / τ = 2 / τ * a by ring,
        Real.mul_rpow (by positivity) ha.le]
      ring
    have hQ' : Q = K3 * J0 := hQ
    have h1 : K1 * a ^ (1 / (γ - 1)) * J0 ≤ max K1 K3 * a ^ (1 / (γ - 1)) * J0 := by
      gcongr
      exact le_max_left _ _
    have h2 : K3 * J0 ≤ max K1 K3 * J0 := by
      gcongr
      exact le_max_right _ _
    have hKb : ∀ i, k₀ + S i ≤
        k₀ + (2 * max K1 K3 + 1) * (1 + a ^ (1 / (γ - 1))) * J0 := by
      intro i
      have := hSle i
      rw [hP', hQ'] at this
      nlinarith [mul_nonneg hap hJ0nn, hJ0nn]
    have hle : ∀ i : ℕ, F (k₀ + (2 * max K1 K3 + 1) * (1 + a ^ (1 / (γ - 1))) * J0) (1 / 2)
        ≤ τ ^ i * J0 := by
      intro i
      refine le_trans (hF.anti (k₀ + S i) _ (1 / 2 + (1 / 2 : ℝ) ^ (i + 1)) (1 / 2)
        (hKb i) ?_) (claim i)
      have : (0 : ℝ) ≤ (1 / 2) ^ (i + 1) := by positivity
      linarith
    have hlim : Filter.Tendsto (fun i : ℕ => τ ^ i * J0) Filter.atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hτ0.le (by linarith)).mul_const J0
    exact le_antisymm (ge_of_tendsto' hlim hle) (hF.nonneg _ _)

end PDE.BSlocalmax
end

-- ==== from Step3Alg.lean ====
-- Square-root version of (26): pure computation with powers.


@[expose] public section

namespace PDE.BSlocalmax

lemma sqrt_rpow' {z : ℝ} (hz : 0 ≤ z) (p : ℝ) : Real.sqrt (z ^ p) = z ^ (p / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hz]; congr 1; ring

lemma rpow_sqrt' {z : ℝ} (hz : 0 ≤ z) (p : ℝ) : (Real.sqrt z) ^ p = z ^ (p / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hz]; congr 1; ring

lemma sqrt_add_le' {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    Real.sqrt (P + Q) ≤ Real.sqrt P + Real.sqrt Q := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt hP, Real.sq_sqrt hQ, mul_nonneg (Real.sqrt_nonneg P) (Real.sqrt_nonneg Q)]

/-- Square root of the improvement inequality. -/
theorem sqrt_step {B s c X Y g θ : ℝ} (hB : 0 ≤ B) (hs : 0 < s) (hc : 0 < c) (hY : 0 ≤ Y)
    (hX : 0 ≤ X)
    (h : X ≤ B * (s / 2) ^ (-(1 + g)) * c ^ (-(2 * g - 2)) * Y ^ g +
      4 * Y ^ (1 + θ) * c ^ (-(2 * θ))) :
    Real.sqrt X ≤ (Real.sqrt B * 2 ^ ((1 + g) / 2)) * s ^ (-((1 + g) / 2)) *
        (Real.sqrt Y) ^ g * c ^ (-(g - 1)) +
      2 * (Real.sqrt Y) ^ (1 + θ) * c ^ (-θ) := by
  have hP : 0 ≤ B * (s / 2) ^ (-(1 + g)) * c ^ (-(2 * g - 2)) * Y ^ g := by positivity
  have hQ : 0 ≤ 4 * Y ^ (1 + θ) * c ^ (-(2 * θ)) := by positivity
  refine (Real.sqrt_le_sqrt h).trans ((sqrt_add_le' hP hQ).trans ?_)
  have e4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have e1 : Real.sqrt (B * (s / 2) ^ (-(1 + g)) * c ^ (-(2 * g - 2)) * Y ^ g) =
      (Real.sqrt B * 2 ^ ((1 + g) / 2)) * s ^ (-((1 + g) / 2)) *
        (Real.sqrt Y) ^ g * c ^ (-(g - 1)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity), sqrt_rpow' (by positivity), sqrt_rpow' hc.le,
      sqrt_rpow' hY, rpow_sqrt' hY]
    have e5 : (s / 2) ^ (-(1 + g) / 2) = 2 ^ ((1 + g) / 2) * s ^ (-((1 + g) / 2)) := by
      rw [show -(1 + g) / 2 = -((1 + g) / 2) by ring, Real.rpow_neg (by positivity),
        Real.rpow_neg hs.le, Real.div_rpow hs.le (by norm_num)]
      field_simp
    have e6 : -(2 * g - 2) / 2 = -(g - 1) := by ring
    rw [e5, e6]
    ring
  have e2 : Real.sqrt (4 * Y ^ (1 + θ) * c ^ (-(2 * θ))) =
      2 * (Real.sqrt Y) ^ (1 + θ) * c ^ (-θ) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), e4,
      sqrt_rpow' hY, sqrt_rpow' hc.le, rpow_sqrt' hY]
    have : -(2 * θ) / 2 = -θ := by ring
    rw [this]
  rw [e1, e2]

end PDE.BSlocalmax
end

-- ==== from Step3.lean ====
-- Verification of `IterHyp` for the (rescaled) energy.


@[expose] public section

open MeasureTheory Set PDE PDE.Ch4Infra

namespace PDE.BSlocalmax

variable {n : ℕ}

lemma eng_nonneg {d : ℕ} (u : H1Function (Metric.ball (0 : Vec d) 1)) (s r : ℝ) :
    0 ≤ Eng u s r :=
  integral_nonneg fun x => eng_integrand_nonneg u s x

lemma vecNormSq_indicator_mono {d : ℕ} {S T : Set (Vec d)} (hST : S ⊆ T) (g : Vec d → Vec d)
    (x : Vec d) :
    vecNormSq (S.indicator g x) ≤ vecNormSq (T.indicator g x) := by
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hST hx)]
  · rw [Set.indicator_of_notMem hx]
    have h0 : vecNormSq (0 : Vec d) = 0 := by
      have := vecNormSq_smul (0 : ℝ) (0 : Vec d)
      simpa using this
    rw [h0]
    exact vecNormSq_nonneg' _

lemma eng_anti_k {d : ℕ} (u : H1Function (Metric.ball (0 : Vec d) 1)) {k k' : ℝ} (hk : k ≤ k')
    {r : ℝ} (hr : r ≤ 1) : Eng u k' r ≤ Eng u k r := by
  refine integral_mono (eng_integrand_integrable u k' hr) (eng_integrand_integrable u k hr)
    (fun x => ?_)
  have h1 : max (u.toFun x - k') 0 ≤ max (u.toFun x - k) 0 := max_le_max (by linarith) le_rfl
  have h2 := vecNormSq_indicator_mono (S := {y | k' < u.toFun y}) (T := {y | k < u.toFun y})
    (fun y hy => lt_of_le_of_lt hk hy) u.grad x
  have h3 := pow_le_pow_left₀ (le_max_right _ _) h1 2
  exact add_le_add h3 h2

lemma eng_mono_r {d : ℕ} (u : H1Function (Metric.ball (0 : Vec d) 1)) (s : ℝ) {r r' : ℝ}
    (hr : r ≤ r') (hr' : r' ≤ 1) : Eng u s r ≤ Eng u s r' :=
  setIntegral_mono_set (eng_integrand_integrable u s hr')
    (Filter.Eventually.of_forall (eng_integrand_nonneg u s))
    (HasSubset.Subset.eventuallyLE (Metric.ball_subset_ball hr))

/-- Rescaled square-root energy `F(k, r) = ‖(u-k)₊‖_{W^{1,2}(Q_{1/4 + r/2})}`. -/
noncomputable def Fn {d : ℕ} (u : H1Function (Metric.ball (0 : Vec d) 1)) (k r : ℝ) : ℝ :=
  Real.sqrt (Eng u k (1 / 4 + max 0 (min r 1) / 2))

lemma clamp_le (r : ℝ) : 1 / 4 + max 0 (min r 1) / 2 ≤ 3 / 4 := by
  have : max 0 (min r 1) ≤ 1 := max_le (by norm_num) (min_le_right _ _)
  linarith

lemma clamp_ge (r : ℝ) : 0 ≤ 1 / 4 + max 0 (min r 1) / 2 := by
  have : 0 ≤ max 0 (min r 1) := le_max_left _ _
  linarith

set_option maxHeartbeats 1600000 in
theorem iterHyp_Fn (hn : 3 ≤ n) :
    ∃ A : ℝ, 0 < A ∧ ∀ {Λ : ℝ} {a : CoeffField (n + 1)},
      (∀ i j, AEMeasurable (fun x => a x i j) (volumeOn (Metric.ball (0 : Vec (n + 1)) 1))) →
      (∀ x ∈ Metric.ball (0 : Vec (n + 1)) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ {u : H1Function (Metric.ball (0 : Vec (n + 1)) 1)},
        IsWeakDivergenceFormSubharmonicOn a (Metric.ball (0 : Vec (n + 1)) 1) u →
        IterHyp (qexp n / 2) (2 / ((n : ℝ) + 1)) ((1 + qexp n / 2) / 2)
          (Real.sqrt (A * Λ) * 2 ^ ((1 + qexp n / 2) / 2)) 2 (Fn u) := by
  obtain ⟨A, hA, hS⟩ := step2_E hn
  refine ⟨A, hA, ?_⟩
  intro Λ a ha hEll u hsub
  refine ⟨fun k r => Real.sqrt_nonneg _, ?_, ?_⟩
  · intro k k' r r' hk hr
    unfold Fn
    have hs' := clamp_le r'
    have hs := clamp_le r
    have hle : max 0 (min r' 1) ≤ max 0 (min r 1) := max_le_max le_rfl (min_le_min hr le_rfl)
    refine Real.sqrt_le_sqrt ((eng_anti_k u hk (by linarith)).trans
      (eng_mono_r u k (by linarith) (by linarith)))
  · intro h k ρ σ hhk hρ hρσ hσ
    have hΛ : 1 ≤ Λ := (hEll 0 (Metric.mem_ball_self one_pos)).lam_le_Lam
    have hcl : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → max 0 (min r 1) = r := fun r h0 h1 => by
      rw [min_eq_left h1, max_eq_right h0]
    have hρ' : max 0 (min ρ 1) = ρ := hcl ρ (by linarith) (by linarith)
    have hσ' : max 0 (min σ 1) = σ := hcl σ (by linarith) (by linarith)
    unfold Fn
    rw [hρ', hσ']
    have h2 := hS (Λ := Λ) (ρ := 1 / 4 + ρ / 2) (σ := 1 / 4 + σ / 2) (h := h) (k := k)
      (by linarith) (by linarith) (by linarith) hhk ha hEll hsub
    have eσ : (1 / 4 + σ / 2) - (1 / 4 + ρ / 2) = (σ - ρ) / 2 := by ring
    have eg : -(2 * (qexp n / 2) - 2) = -(qexp n - 2) := by ring
    have eθ : -(2 * (2 / ((n : ℝ) + 1))) = -(4 / ((n : ℝ) + 1)) := by ring
    rw [eσ] at h2
    have hAΛ : 0 ≤ A * Λ := by positivity
    have := sqrt_step (B := A * Λ) (s := σ - ρ) (c := k - h) (X := Eng u k (1 / 4 + ρ / 2))
      (Y := Eng u h (1 / 4 + σ / 2)) (g := qexp n / 2) (θ := 2 / ((n : ℝ) + 1)) hAΛ
      (by linarith) (sub_pos.2 hhk) (eng_nonneg u _ _) (eng_nonneg u _ _)
      (by rw [eg, eθ]; exact h2)
    have e1 : qexp n / 2 - 1 = (qexp n / 2) - 1 := rfl
    convert this using 3

end PDE.BSlocalmax
end

-- ==== from Step3Init.lean ====
-- Initial estimate: energy of `u₊` on `Q_{3/4}` bounded by `Λ ‖u‖²_{L²(Q_1)}`.


@[expose] public section

open MeasureTheory Set Filter PDE PDE.Ch4Infra

namespace PDE.BSlocalmax

variable {n : ℕ}

set_option maxHeartbeats 1600000 in
theorem initial_energy_gen :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ {Λ : ℝ} {a : CoeffField (n + 1)},
      (∀ i j, AEMeasurable (fun x => a x i j) (volumeOn (Metric.ball (0 : Vec (n + 1)) 1))) →
      (∀ x ∈ Metric.ball (0 : Vec (n + 1)) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ {u : H1Function (Metric.ball (0 : Vec (n + 1)) 1)},
        IsWeakDivergenceFormSubharmonicOn a (Metric.ball (0 : Vec (n + 1)) 1) u →
        Eng u 0 (3 / 4) ≤ C0 * Λ * ∫ x in Metric.ball (0 : Vec (n + 1)) 1, (u.toFun x) ^ 2 := by
  refine ⟨641, by norm_num, ?_⟩
  intro Λ a ha hEll u hsub
  have hΛ : 1 ≤ Λ := (hEll 0 (Metric.mem_ball_self one_pos)).lam_le_Lam
  have hU : IsOpen (Metric.ball (0 : Vec (n + 1)) 1) := Metric.isOpen_ball
  have hfin : volume (Metric.ball (0 : Vec (n + 1)) 1) ≠ ⊤ :=
    Metric.isBounded_ball.measure_lt_top.ne
  have h34 : (3 / 4 : ℝ) < 7 / 8 := by norm_num
  set η : Vec (n + 1) → ℝ := cubeCutoff (0 : Vec (n + 1)) (3 / 4) (7 / 8) with hηdef
  have hη : EucLip 8 η := by
    have := cubeCutoff_eucLip (0 : Vec (n + 1)) h34
    convert this using 1; norm_num
  have hK0 : (0 : ℝ) ≤ 8 := by norm_num
  have hM : ∀ x, |η x| ≤ 1 := fun x => abs_cubeCutoff_le_one _ _ _ x
  have hηc : HasCompactSupport η := hasCompactSupport_cubeCutoff 0 h34
  have hηU : tsupport η ⊆ Metric.ball (0 : Vec (n + 1)) 1 :=
    (tsupport_cubeCutoff_subset 0 h34).trans (Metric.closedBall_subset_ball (by norm_num))
  have hη1 : ∀ x : Vec (n + 1), ‖x‖ ≤ 3 / 4 → η x = 1 := fun x hx =>
    cubeCutoff_eq_one h34 (by simpa using hx)
  have hcacc := caccioppoli_energy_positivePart_ten_open hU hfin ha hEll hsub 0 hη hK0 hM hηc hηU
  have hηcont : Continuous η := hη.continuous hK0
  have hwL2 : MemL2On (Metric.ball (0 : Vec (n + 1)) 1) (fun x => max (u.toFun x - 0) 0) := by
    simpa only [sub_zero] using memL2On_positivePart_of_finite u hfin 0
  have hξL2 : MemVectorL2On (Metric.ball (0 : Vec (n + 1)) 1)
      (fun x => {y | 0 < u.toFun y}.indicator u.grad x) := posPartGrad_gradMemL2 u 0
  have hA : MemVectorL2On (Metric.ball (0 : Vec (n + 1)) 1)
      (fun x => η x • {y | 0 < u.toFun y}.indicator u.grad x) := fun i => by
    simpa only [Pi.smul_apply, smul_eq_mul] using memL2On_mul_bounded (hξL2 i) hηcont hM
  have hB : MemVectorL2On (Metric.ball (0 : Vec (n + 1)) 1)
      (fun x => max (u.toFun x - 0) 0 • classicalGradient η x) := fun i => by
    simpa only [Pi.smul_apply, smul_eq_mul, classicalGradient] using
      memL2On_mul_partialDeriv hη hK0 hwL2 i
  have hABsq := integrableOn_vecNormSq_of_memVectorL2On (fun i => (hA i).add (hB i))
  have hin : ∫ x in Metric.ball (0 : Vec (n + 1)) (3 / 4),
        vecNormSq ({y | 0 < u.toFun y}.indicator u.grad x) =
      ∫ x in Metric.ball (0 : Vec (n + 1)) (3 / 4),
        vecNormSq (η x • {y | 0 < u.toFun y}.indicator u.grad x +
          max (u.toFun x - 0) 0 • classicalGradient η x) := by
    refine setIntegral_congr_fun Metric.isOpen_ball.measurableSet (fun x hx => ?_)
    have hxn : ‖x‖ < 3 / 4 := by simpa using hx
    have hev : ∀ᶠ y in nhds x, η y = 1 :=
      Filter.mem_of_superset ((isOpen_lt continuous_norm continuous_const).mem_nhds hxn)
        (fun y hy => hη1 y (le_of_lt hy))
    have h0 := classicalGradient_eq_zero_of_eventually hev
    simp only [hη1 x hxn.le, h0, one_smul, smul_zero, add_zero]
  have hmono : ∫ x in Metric.ball (0 : Vec (n + 1)) (3 / 4),
        vecNormSq (η x • {y | 0 < u.toFun y}.indicator u.grad x +
          max (u.toFun x - 0) 0 • classicalGradient η x) ≤
      ∫ x in Metric.ball (0 : Vec (n + 1)) 1,
        vecNormSq (η x • {y | 0 < u.toFun y}.indicator u.grad x +
          max (u.toFun x - 0) 0 • classicalGradient η x) :=
    setIntegral_mono_set hABsq (Filter.Eventually.of_forall (fun x => vecNormSq_nonneg' _))
      (HasSubset.Subset.eventuallyLE (Metric.ball_subset_ball (by norm_num)))
  -- Right-hand side
  have hu2 : IntegrableOn (fun x => (u.toFun x) ^ 2) (Metric.ball (0 : Vec (n + 1)) 1) := by
    simpa only [pow_two] using integrableOn_mul_of_memL2On u.memL2 u.memL2
  have hgrad : ∀ x, vecNormSq (classicalGradient η x) ≤ 64 := fun x => by
    have h1 := EucLip.vecEuclideanNorm_classicalGradient_le' hη hK0 x
    have h3 := pow_le_pow_left₀ (vecEuclideanNorm_nonneg _) h1 2
    rw [vecEuclideanNorm_sq] at h3
    linarith
  have hR : ∫ x in Metric.ball (0 : Vec (n + 1)) 1,
      (max (u.toFun x - 0) 0) ^ 2 * vecNormSq (classicalGradient η x) ≤
      64 * ∫ x in Metric.ball (0 : Vec (n + 1)) 1, (u.toFun x) ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x =>
      mul_nonneg (sq_nonneg _) (vecNormSq_nonneg' _)) (hu2.const_mul 64)
      (Filter.Eventually.of_forall fun x => ?_)
    have h1 : (max (u.toFun x - 0) 0) ^ 2 ≤ (u.toFun x) ^ 2 := by
      rw [sub_zero]
      rcases le_total (u.toFun x) 0 with h | h
      · rw [max_eq_right h]; nlinarith [sq_nonneg (u.toFun x)]
      · rw [max_eq_left h]
    calc (max (u.toFun x - 0) 0) ^ 2 * vecNormSq (classicalGradient η x)
        ≤ (u.toFun x) ^ 2 * 64 :=
          mul_le_mul h1 (hgrad x) (vecNormSq_nonneg' _) (sq_nonneg _)
      _ = 64 * (u.toFun x) ^ 2 := by ring
  have hGle : ∫ x in Metric.ball (0 : Vec (n + 1)) (3 / 4),
      vecNormSq ({y | 0 < u.toFun y}.indicator u.grad x) ≤
      640 * Λ * ∫ x in Metric.ball (0 : Vec (n + 1)) 1, (u.toFun x) ^ 2 := by
    calc _ ≤ 10 * Λ * ∫ x in Metric.ball (0 : Vec (n + 1)) 1,
          (max (u.toFun x - 0) 0) ^ 2 * vecNormSq (classicalGradient η x) :=
          hin.le.trans (hmono.trans hcacc)
      _ ≤ 10 * Λ * (64 * ∫ x in Metric.ball (0 : Vec (n + 1)) 1, (u.toFun x) ^ 2) :=
          mul_le_mul_of_nonneg_left hR (by linarith)
      _ = _ := by ring
  -- Positive part
  have hsqI : IntegrableOn (fun x => (max (u.toFun x - 0) 0) ^ 2)
      (Metric.ball (0 : Vec (n + 1)) (3 / 4)) := by
    have hL2 := memL2On_positivePart_of_finite u hfin 0
    have : IntegrableOn (fun x => (max (u.toFun x - 0) 0) ^ 2) (Metric.ball (0 : Vec (n + 1)) 1) := by
      simpa only [pow_two] using integrableOn_mul_of_memL2On hL2 hL2
    exact this.mono_set (Metric.ball_subset_ball (by norm_num))
  have hξI : IntegrableOn (fun x => vecNormSq ({y | 0 < u.toFun y}.indicator u.grad x))
      (Metric.ball (0 : Vec (n + 1)) (3 / 4)) :=
    (integrableOn_vecNormSq_of_memVectorL2On hξL2).mono_set (Metric.ball_subset_ball (by norm_num))
  have hVle : ∫ x in Metric.ball (0 : Vec (n + 1)) (3 / 4), (max (u.toFun x - 0) 0) ^ 2 ≤
      ∫ x in Metric.ball (0 : Vec (n + 1)) 1, (u.toFun x) ^ 2 := by
    calc _ ≤ ∫ x in Metric.ball (0 : Vec (n + 1)) 1, (max (u.toFun x - 0) 0) ^ 2 :=
          setIntegral_mono_set (by
            have hL2 := memL2On_positivePart_of_finite u hfin 0
            simpa only [pow_two] using integrableOn_mul_of_memL2On hL2 hL2)
            (Filter.Eventually.of_forall fun x => sq_nonneg _)
            (HasSubset.Subset.eventuallyLE (Metric.ball_subset_ball (by norm_num)))
      _ ≤ _ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _) hu2
            (Filter.Eventually.of_forall fun x => ?_)
          beta_reduce
          rw [sub_zero]
          rcases le_total (u.toFun x) 0 with h | h
          · rw [max_eq_right h]; nlinarith [sq_nonneg (u.toFun x)]
          · rw [max_eq_left h]
  have hI0 : 0 ≤ ∫ x in Metric.ball (0 : Vec (n + 1)) 1, (u.toFun x) ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have hEng : Eng u 0 (3 / 4) = (∫ x in Metric.ball (0 : Vec (n + 1)) (3 / 4),
      (max (u.toFun x - 0) 0) ^ 2) + ∫ x in Metric.ball (0 : Vec (n + 1)) (3 / 4),
      vecNormSq ({y | 0 < u.toFun y}.indicator u.grad x) := integral_add hsqI hξI
  rw [hEng]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Λ - 1) hI0]

end PDE.BSlocalmax
end

-- ==== from Main.lean ====
/-!
# Sharp local maximum principle on cubes (`d ≥ 4`)

The sharp `L^∞`–`L²` estimate with exponent `(d-1)/4` of the ellipticity contrast,
sup over the cube `Q_{1/2}` in terms of the `L²` norm on `Q_1` (`Q_r = Metric.ball 0 r`,
sup norm).  Compare `PDE.exists_localMaxPrinciple_constant` (exponent `d/4`, balls).

Chain: cube cutoff → shell lemma (smooth version of (25)) → Step 1 (inequality (20)) →
Step 2 (inequality (26)) → Step 3 (iteration) → initial Caccioppoli → this statement.
-/

@[expose] public section

namespace PDE.BSlocalmax

open MeasureTheory PDE PDE.Ch4Infra

set_option maxHeartbeats 1600000 in
theorem exists_sharpLocalMax_constant_cube (d : ℕ) (hd : 4 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (Metric.ball (0 : Vec d) 1))) →
      (∀ x ∈ Metric.ball (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (Metric.ball (0 : Vec d) 1),
      IsWeakDivergenceFormSubharmonicOn a (Metric.ball (0 : Vec d) 1) u →
        essSup (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (Metric.ball (0 : Vec d) (1 / 2))) ≤
          ENNReal.ofReal (C * Λ ^ (((d : ℝ) - 1) / 4)) *
            eLpNorm u.toFun 2 (volumeOn (Metric.ball (0 : Vec d) 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hn : 3 ≤ n := by omega
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hq := qexp_gt hn
  obtain ⟨A, hA, hH⟩ := iterHyp_Fn hn
  obtain ⟨C0, hC0, hI⟩ := initial_energy_gen (n := n)
  obtain ⟨c, hc, hIt⟩ := iteration_limit (γ := qexp n / 2) (θ := 2 / ((n : ℝ) + 1))
    (α := (1 + qexp n / 2) / 2) (b := 2) (by linarith) (by positivity) (by positivity)
    (by norm_num)
  have hpv : 1 / (qexp n / 2 - 1) = ((n : ℝ) - 2) / 2 := by
    have : qexp n / 2 - 1 = 2 / ((n : ℝ) - 2) := by
      have : (n : ℝ) - 2 ≠ 0 := by linarith
      unfold qexp; field_simp; ring
    rw [this, one_div_div]
  set p : ℝ := 1 / (qexp n / 2 - 1) with hp
  have hp0 : 0 ≤ p := by rw [hpv]; linarith
  set C1 : ℝ := 1 + A ^ (p / 2) * (2 ^ ((1 + qexp n / 2) / 2)) ^ p with hC1
  have hC1pos : 0 < C1 := by positivity
  refine ⟨c * C1 * Real.sqrt C0, by positivity, ?_⟩
  intro Λ a ha hEll u hsub
  have hΛ : 1 ≤ Λ := (hEll 0 (Metric.mem_ball_self one_pos)).lam_le_Lam
  have hΛ0 : 0 < Λ := by linarith
  have hHyp := hH ha hEll hsub
  have haC : 0 < Real.sqrt (A * Λ) * 2 ^ ((1 + qexp n / 2) / 2) := by positivity
  have hres := hIt _ haC (Fn u) hHyp 0
  set K : ℝ := 0 + c * (1 + (Real.sqrt (A * Λ) * 2 ^ ((1 + qexp n / 2) / 2)) ^ p) * Fn u 0 1
    with hK
  have e12 : max 0 (min (1 / 2 : ℝ) 1) = 1 / 2 := by
    rw [min_eq_left (by norm_num), max_eq_right (by norm_num)]
  have e1 : max 0 (min (1 : ℝ) 1) = 1 := by simp
  -- Eng = 0
  have hEng0 : Eng u K (1 / 2) = 0 := by
    unfold Fn at hres
    rw [e12] at hres
    have := (Real.sqrt_eq_zero (eng_nonneg u _ _)).1 hres
    convert this using 2; norm_num
  -- almost everywhere u ≤ K
  have hint : IntegrableOn (fun x => (max (u.toFun x - K) 0) ^ 2 +
      vecNormSq ({y | K < u.toFun y}.indicator u.grad x)) (Metric.ball (0 : Vec (n + 1)) (1 / 2)) :=
    eng_integrand_integrable u K (by norm_num)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => eng_integrand_nonneg u K x) hint).1 hEng0
  have hess : essSup (fun x => ENNReal.ofReal (u.toFun x))
      (volumeOn (Metric.ball (0 : Vec (n + 1)) (1 / 2))) ≤ ENNReal.ofReal K := by
    refine essSup_le_of_ae_le _ ?_
    filter_upwards [hae] with x hx
    have hx' : (max (u.toFun x - K) 0) ^ 2 + vecNormSq ({y | K < u.toFun y}.indicator u.grad x) = 0 :=
      hx
    have h1 : (max (u.toFun x - K) 0) ^ 2 = 0 := by
      nlinarith [sq_nonneg (max (u.toFun x - K) 0), vecNormSq_nonneg' ({y | K < u.toFun y}.indicator u.grad x)]
    have h2 : max (u.toFun x - K) 0 = 0 := pow_eq_zero_iff (by norm_num) |>.1 h1
    have h3 : u.toFun x - K ≤ 0 := h2 ▸ le_max_left _ _
    exact ENNReal.ofReal_le_ofReal (by linarith)
  -- Estimate of K
  have hmem : MemLp u.toFun 2 (volumeOn (Metric.ball (0 : Vec (n + 1)) 1)) := u.memL2
  set E0 : ℝ := (eLpNorm u.toFun 2 (volumeOn (Metric.ball (0 : Vec (n + 1)) 1))).toReal with hE0
  have hE0n : 0 ≤ E0 := ENNReal.toReal_nonneg
  have hE0sq : E0 ^ 2 = ∫ x in Metric.ball (0 : Vec (n + 1)) 1, (u.toFun x) ^ 2 :=
    toReal_eLpNorm_two_sq_eq_integral_sq hmem
  have hF0 : Fn u 0 1 ≤ Real.sqrt C0 * Λ ^ (1 / 2 : ℝ) * E0 := by
    unfold Fn
    rw [e1, show ((1 : ℝ) / 4 + 1 / 2) = 3 / 4 by norm_num]
    have hI' := hI ha hEll hsub
    rw [← hE0sq] at hI'
    calc Real.sqrt (Eng u 0 (3 / 4))
        ≤ Real.sqrt (C0 * Λ * E0 ^ 2) := Real.sqrt_le_sqrt hI'
      _ = Real.sqrt C0 * Λ ^ (1 / 2 : ℝ) * E0 := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hC0.le, Real.sqrt_sq hE0n,
            Real.sqrt_eq_rpow Λ]
  have hpΛ : 1 ≤ Λ ^ (p / 2) := Real.one_le_rpow hΛ (by positivity)
  have h1a : 1 + (Real.sqrt (A * Λ) * 2 ^ ((1 + qexp n / 2) / 2)) ^ p ≤ C1 * Λ ^ (p / 2) := by
    rw [Real.mul_rpow (Real.sqrt_nonneg _) (by positivity), rpow_sqrt' (by positivity),
      Real.mul_rpow hA.le hΛ0.le]
    rw [hC1]
    have hX : 0 ≤ A ^ (p / 2) * (2 ^ ((1 + qexp n / 2) / 2)) ^ p := by positivity
    nlinarith [mul_nonneg hX (sub_nonneg.2 hpΛ)]
  have hpow : Λ ^ (p / 2) * Λ ^ (1 / 2 : ℝ) = Λ ^ ((((n + 1 : ℕ) : ℝ) - 1) / 4) := by
    rw [← Real.rpow_add hΛ0]
    congr 1
    rw [hpv]; push_cast; ring
  have hKle : K ≤ (c * C1 * Real.sqrt C0) * Λ ^ ((((n + 1 : ℕ) : ℝ) - 1) / 4) * E0 := by
    have hFn0 : 0 ≤ Fn u 0 1 := Real.sqrt_nonneg _
    calc K = c * (1 + (Real.sqrt (A * Λ) * 2 ^ ((1 + qexp n / 2) / 2)) ^ p) * Fn u 0 1 := by
          rw [hK]; ring
      _ ≤ c * (C1 * Λ ^ (p / 2)) * (Real.sqrt C0 * Λ ^ (1 / 2 : ℝ) * E0) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1a hc.le) hF0 hFn0 (by positivity)
      _ = (c * C1 * Real.sqrt C0) * (Λ ^ (p / 2) * Λ ^ (1 / 2 : ℝ)) * E0 := by ring
      _ = _ := by rw [hpow]
  -- Conclusion
  refine hess.trans ?_
  have hfin : eLpNorm u.toFun 2 (volumeOn (Metric.ball (0 : Vec (n + 1)) 1)) ≠ ⊤ :=
    hmem.eLpNorm_ne_top
  calc ENNReal.ofReal K
      ≤ ENNReal.ofReal ((c * C1 * Real.sqrt C0) * Λ ^ ((((n + 1 : ℕ) : ℝ) - 1) / 4) * E0) :=
        ENNReal.ofReal_le_ofReal hKle
    _ = ENNReal.ofReal ((c * C1 * Real.sqrt C0) * Λ ^ ((((n + 1 : ℕ) : ℝ) - 1) / 4)) *
          eLpNorm u.toFun 2 (volumeOn (Metric.ball (0 : Vec (n + 1)) 1)) := by
        rw [ENNReal.ofReal_mul (by positivity), hE0, ENNReal.ofReal_toReal hfin]

end PDE.BSlocalmax
end
