module

public import EllipticRegularity.Ch4.Examples.LocalmaxExample
public import EllipticRegularity.Ch4.Examples.LocalmaxL2

/-!
# Lower bound `Λ^{(d-1)/4}` in the local maximum principle (Proposition 4.12)
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE.Ch4Examples

open MeasureTheory Filter

/-- `Λ^{(d-1)/4} = √((√Λ)^{d-1})`. -/
theorem sqrt_sqrt_pow (Λ : ℝ) (hΛ : 0 ≤ Λ) (n : ℕ) :
    Real.sqrt ((Real.sqrt Λ) ^ n) = Λ ^ ((n : ℝ) / 4) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hΛ,
    ← Real.rpow_mul hΛ]
  congr 1
  ring

theorem zero_mem_half_ball (d : ℕ) : (0 : Vec d) ∈ euclideanBall (0 : Vec d) (1 / 2) := by
  rw [mem_euclideanBall_zero_iff]
  simp [vecNormSq_eq_sum_sq]

/-- The constant of the example. -/
noncomputable def cLM (d : ℕ) : ℝ :=
  Real.exp (-(1 / ((d : ℝ) - 1))) /
    Real.sqrt (2 * Real.exp 1 * (((d : ℝ) - 1) ^ 2) ^ (d - 1))

theorem cLM_pos (d : ℕ) (hd : 2 ≤ d) : 0 < cLM d := by
  have hm1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  unfold cLM
  have : 0 < 2 * Real.exp 1 * (((d : ℝ) - 1) ^ 2) ^ (d - 1) := by positivity
  positivity

/-- Strong form of the `localmax` example. -/
theorem localmax_example_strong (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ A : Mat d,
      (∀ i j : Fin d, A i j = if i = j then (if i.val + 1 = d then Λ else 1) else 0) ∧
      IsEllipticMatrix 1 Λ A ∧
      ∃ u : H1Function (euclideanBall (0 : Vec d) 1),
        (∀ x : Vec d, u.toFun x = Real.exp (x ⟨d - 1, by omega⟩ ^ 2 / 2 -
            Real.sqrt (1 + Λ * ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val + 1 < d),
              x i ^ 2) / ((d : ℝ) - 1))) ∧
        u.grad = classicalGradient u.toFun ∧
        ContDiff ℝ (⊤ : ℕ∞) u.toFun ∧
        (∀ x, 0 < u.toFun x) ∧
        (∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) →
          ∫ x, vecDot (matVecMul A (fun i => fderiv ℝ u.toFun x (basisVec i)))
            (fun i => fderiv ℝ φ x (basisVec i)) ≤ 0) ∧
        essSup (fun x => ENNReal.ofReal (u.toFun x))
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≥
          ENNReal.ofReal (u.toFun 0) ∧
        ENNReal.ofReal (u.toFun 0) ≥
          ENNReal.ofReal (cLM d * Λ ^ (((d : ℝ) - 1) / 4)) *
            eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1)) := by
  have hm1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  obtain ⟨A, hA, hell, u, hu, hgrad, hsm, hpos, hsub⟩ := localmax_subsolution d hd Λ hΛ
  refine ⟨A, hA, hell, u, hu, hgrad, hsm, hpos, hsub, ?_, ?_⟩
  · exact le_essSup_of_continuous (isOpen_euclideanBall (0 : Vec d) (1 / 2)) hsm.continuous
      (zero_mem_half_ball d)
  · have hu0 : u.toFun 0 = Real.exp (-(1 / ((d : ℝ) - 1))) := by
      rw [hu]
      simp
    have hL2 := localmax_eLpNorm_bound d hd Λ hΛ u.toFun hsm.continuous hu
    set W : ℝ := (Real.sqrt Λ) ^ (d - 1) with hW
    have hsq : 1 ≤ Real.sqrt Λ := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hΛ
    have hWpos : 0 < W := by rw [hW]; positivity
    set N : ℝ := 2 * Real.exp 1 * (((d : ℝ) - 1) ^ 2) ^ (d - 1) with hN
    have hNpos : 0 < N := by rw [hN]; positivity
    have hK : Real.exp 1 * (2 * (2 / (2 * Real.sqrt Λ / ((d : ℝ) - 1) ^ 2)) ^ (d - 1)) = N / W := by
      rw [hN, hW]
      have h1 : 2 / (2 * Real.sqrt Λ / ((d : ℝ) - 1) ^ 2) = ((d : ℝ) - 1) ^ 2 / Real.sqrt Λ := by
        field_simp
      rw [h1, div_pow]
      field_simp
    rw [hK] at hL2
    have hcast : ((d : ℝ) - 1) = ((d - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; simp
    have hpow : Λ ^ (((d : ℝ) - 1) / 4) = Real.sqrt W := by
      rw [hcast, hW, sqrt_sqrt_pow Λ hΛ0]
    rw [hu0, hpow]
    refine (mul_le_mul' le_rfl hL2).trans ?_
    rw [← ENNReal.ofReal_mul (by unfold cLM; positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [Real.sqrt_div hNpos.le]
    unfold cLM
    have hsW : 0 < Real.sqrt W := Real.sqrt_pos.2 hWpos
    field_simp
    rw [hN]

/-- **Lower bound `Λ^{(d-1)/4}` in the local maximum principle** (Proposition 4.12, first part). -/
theorem localmax_lower_example_full (d : ℕ) (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ Λ : ℝ, 1 ≤ Λ →
      ∃ A : Mat d,
        (∀ i j : Fin d, A i j = if i = j then (if i.val + 1 = d then Λ else 1) else 0) ∧
        IsEllipticMatrix 1 Λ A ∧
        ∃ u : H1Function (euclideanBall (0 : Vec d) 1),
          (∀ x : Vec d, u.toFun x = Real.exp (x ⟨d - 1, by omega⟩ ^ 2 / 2 -
            Real.sqrt (1 + Λ * ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val + 1 < d),
              x i ^ 2) / ((d : ℝ) - 1))) ∧
          ContDiff ℝ (⊤ : ℕ∞) u.toFun ∧
          (∀ x, 0 < u.toFun x) ∧
          (∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) →
            ∫ x, vecDot (matVecMul A (fun i => fderiv ℝ u.toFun x (basisVec i)))
              (fun i => fderiv ℝ φ x (basisVec i)) ≤ 0) ∧
          essSup (fun x => ENNReal.ofReal (u.toFun x))
              (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≥
            ENNReal.ofReal (u.toFun 0) ∧
          ENNReal.ofReal (u.toFun 0) ≥
            ENNReal.ofReal (c * Λ ^ (((d : ℝ) - 1) / 4)) *
              eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1)) := by
  refine ⟨cLM d, cLM_pos d hd, fun Λ hΛ => ?_⟩
  obtain ⟨A, hA, hell, u, hu, -, hsm, hpos, hsub, hess, hL2⟩ := localmax_example_strong d hd Λ hΛ
  exact ⟨A, hA, hell, u, hu, hsm, hpos, hsub, hess, hL2⟩

/-- **Exponent consequence of Proposition 4.12**. -/
theorem localmax_exponent_lower_bound_full (d : ℕ) (hd : 3 ≤ d) (γ C : ℝ)
    (h : ∀ (Λ : ℝ), 1 ≤ Λ → ∀ (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j)
        (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSubharmonicOn a (euclideanBall (0 : Vec d) 1) u →
        essSup (fun x => ENNReal.ofReal (u.toFun x))
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
          ENNReal.ofReal (C * Λ ^ γ) *
            eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1))) :
    ((d : ℝ) - 1) / 4 ≤ γ := by
  have hd2 : 2 ≤ d := by omega
  set c := cLM d with hc
  have hcpos : 0 < c := cLM_pos d hd2
  by_contra hγ
  push Not at hγ
  have hy : 0 < ((d : ℝ) - 1) / 4 - γ := by linarith
  have hev : ∀ᶠ Λ : ℝ in atTop, 1 ≤ Λ ∧ C / c < Λ ^ (((d : ℝ) - 1) / 4 - γ) :=
    (eventually_ge_atTop 1).and ((tendsto_rpow_atTop hy).eventually_gt_atTop (C / c))
  obtain ⟨Λ, hΛ1, hΛC⟩ := hev.exists
  have hΛpos : 0 < Λ := by linarith
  have hU : MeasurableSet (euclideanBall (0 : Vec d) 1) := (isOpen_euclideanBall _ _).measurableSet
  obtain ⟨A, hA, hell, u, hu, hgrad, hsm, hpos, hsub, hess, hL2⟩ :=
    localmax_example_strong d hd2 Λ hΛ1
  have H := h Λ hΛ1 (fun _ => A) (fun i j => aemeasurable_const) (fun x _ => hell) u
    (isWeakSubharmonic_of_smooth hU A u hgrad hsm hsub)
  -- the `L²` norm is finite and nonzero
  have hfin : eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (localmax_eLpNorm_bound d hd2 Λ hΛ1 u.toFun hsm.continuous hu)
  have hne : eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1)) ≠ 0 := by
    intro h0
    rw [eLpNorm_eq_zero_iff (by norm_num)] at h0
    rw [volumeOn, EventuallyEq, ae_restrict_iff' hU] at h0
    have hnull : volume (euclideanBall (0 : Vec d) 1) = 0 := by
      have : euclideanBall (0 : Vec d) 1 ⊆ {x | ¬ (x ∈ euclideanBall (0 : Vec d) 1 → u.toFun x = 0)} := by
        intro x hx hx'
        exact (hpos x).ne' (by simpa using hx' hx)
      exact measure_mono_null this (ae_iff.1 h0)
    exact (volume_euclideanBall_pos (0 : Vec d) one_pos).ne' hnull
  have h2 := hL2.trans (hess.trans H)
  have h3 := (ENNReal.mul_le_mul_iff_left hne hfin).1 h2
  have hCγ : 0 ≤ C * Λ ^ γ := by
    by_contra hneg
    push Not at hneg
    rw [ENNReal.ofReal_of_nonpos hneg.le] at h3
    have : 0 < ENNReal.ofReal (c * Λ ^ (((d : ℝ) - 1) / 4)) :=
      ENNReal.ofReal_pos.2 (by positivity)
    exact absurd h3 (not_le.2 this)
  rw [ENNReal.ofReal_le_ofReal_iff hCγ] at h3
  have hpγ : 0 < Λ ^ γ := Real.rpow_pos_of_pos hΛpos _
  have hsplit : Λ ^ (((d : ℝ) - 1) / 4 - γ) * Λ ^ γ = Λ ^ (((d : ℝ) - 1) / 4) := by
    rw [← Real.rpow_add hΛpos, sub_add_cancel]
  have h4 : C / c * Λ ^ γ < Λ ^ (((d : ℝ) - 1) / 4 - γ) * Λ ^ γ :=
    mul_lt_mul_of_pos_right hΛC hpγ
  rw [hsplit] at h4
  have h5 : C * Λ ^ γ < c * Λ ^ (((d : ℝ) - 1) / 4) := by
    have : C * Λ ^ γ = c * (C / c * Λ ^ γ) := by field_simp
    rw [this]
    exact mul_lt_mul_of_pos_left h4 hcpos
  linarith

end PDE.Ch4Examples
