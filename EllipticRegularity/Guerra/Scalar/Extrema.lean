module

public import EllipticRegularity.Guerra.Scalar.Holder
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Guerra sharpness: non-Hölder property, exact extrema, Harnack ratio arithmetic
-/

@[expose] public section

namespace PDE.Guerra

open Real PDE MeasureTheory Filter Topology

variable {d : ℕ}

theorem single_smul_mem_euclideanBall (i : Fin d) {s R : ℝ} (hs : 0 < s) (hsR : s < R) :
    (s • (Pi.single i (1 : ℝ) : Vec d)) ∈ euclideanBall (0 : Vec d) R := by
  have hR : 0 < R := hs.trans hsR
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR, sub_zero, vecEuclideanNorm_smul_single i hs]
  exact hsR

theorem neg_single_smul_mem_euclideanBall (i : Fin d) {s R : ℝ} (hs : 0 < s) (hsR : s < R) :
    (-(s • (Pi.single i (1 : ℝ) : Vec d))) ∈ euclideanBall (0 : Vec d) R := by
  have hR : 0 < R := hs.trans hsR
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR, sub_zero, vecEuclideanNorm_neg,
    vecEuclideanNorm_smul_single i hs]
  exact hsR

/-- A function with a finite `α'`-Hölder seminorm (`α' > 0`) on a set is continuous on it. -/
theorem continuousOn_of_holder {U : Set (Vec d)} {v : Vec d → ℝ} {α' M : ℝ} (hα' : 0 < α')
    (hH : EuclideanHolderSeminormLE U v α' M) : ContinuousOn v U := by
  intro x hx
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  have hc : Continuous fun y : Vec d => M * vecEuclideanNorm (y - x) ^ α' :=
    (Continuous.rpow_const (continuous_vecEuclideanNorm.comp (continuous_id.sub continuous_const))
      (fun _ => Or.inr hα'.le)).const_mul M
  have hlim : Tendsto (fun y : Vec d => M * vecEuclideanNorm (y - x) ^ α') (𝓝[U] x) (𝓝 0) := by
    have := (hc.tendsto x).mono_left (nhdsWithin_le_nhds (s := U))
    have h0 : vecEuclideanNorm (0 : Vec d) = 0 := by
      simp [vecEuclideanNorm, vecNormSq, vecDot]
    simpa [h0, Real.zero_rpow hα'.ne'] using this
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [Real.dist_eq]
  exact hH y hy x hx

/-- No a.e.-representative of `u` on `B_ρ` is `α'`-Hölder for `α' > α`. -/
theorem uProf_not_holder (i : Fin d) {γ α : ℝ} (hγ : 1 ≤ γ) (hα : 0 < α) {ρ : ℝ} (hρ : 0 < ρ)
    {α' : ℝ} (hα' : α < α') :
    ¬ ∃ (v : Vec d → ℝ) (M : ℝ), v =ᵐ[volumeOn (euclideanBall (0 : Vec d) ρ)] uProf i γ α ∧
      EuclideanHolderSeminormLE (euclideanBall (0 : Vec d) ρ) v α' M := by
  rintro ⟨v, M, hae, hH⟩
  have hcont := continuousOn_of_holder (by linarith) hH
  have heq : Set.EqOn v (uProf i γ α) (euclideanBall (0 : Vec d) ρ) :=
    Measure.eqOn_open_of_ae_eq hae (isOpen_euclideanBall _ _) hcont
      (continuous_uProf i hγ hα).continuousOn
  set e := α' - α with he_def
  have he : 0 < e := by linarith
  have ht : Tendsto (fun s : ℝ => s ^ e) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 e (Or.inr he.le)).tendsto
    simpa [Real.zero_rpow he.ne'] using this.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ^ e < 1 / (|M| + 1) :=
    ht.eventually (gt_mem_nhds (by positivity))
  obtain ⟨s, hs1, hs2⟩ := (hev.and (Ioo_mem_nhdsGT hρ)).exists
  have hs0 : 0 < s := hs2.1
  have hmem := single_smul_mem_euclideanBall i hs0 hs2.2
  have h0mem : (0 : Vec d) ∈ euclideanBall (0 : Vec d) ρ := by
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hρ, sub_zero]
    simpa [vecEuclideanNorm, vecNormSq, vecDot] using hρ
  have hb := hH _ hmem 0 h0mem
  rw [heq hmem, heq h0mem, uProf_ray i hγ α hs0, uProf_zero, sub_zero, sub_zero,
    vecEuclideanNorm_smul_single i hs0, abs_of_pos (Real.rpow_pos_of_pos hs0 α)] at hb
  have hsplit : s ^ α' = s ^ α * s ^ e := by
    rw [← Real.rpow_add hs0]; congr 1; rw [he_def]; ring
  rw [hsplit] at hb
  have hpos : 0 < s ^ α := Real.rpow_pos_of_pos hs0 α
  have h1 : 1 ≤ M * s ^ e := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have h2 : |M| * s ^ e ≤ |M| * (1 / (|M| + 1)) :=
    mul_le_mul_of_nonneg_left hs1.le (abs_nonneg M)
  have h3 : |M| * (1 / (|M| + 1)) < 1 := by
    rw [mul_one_div, div_lt_one (by positivity)]; linarith
  have h4 : M * s ^ e ≤ |M| * s ^ e :=
    mul_le_mul_of_nonneg_right (le_abs_self M) (Real.rpow_nonneg hs0.le e)
  linarith

/-- Exact supremum of `1 + u` over `B_{1/2}`. -/
theorem uProf_isLUB (i : Fin d) {γ α : ℝ} (hγ : 1 ≤ γ) (hα : 0 < α) :
    IsLUB ((fun x => 1 + uProf i γ α x) '' euclideanBall (0 : Vec d) (1 / 2))
      (1 + (1 / 2 : ℝ) ^ α) := by
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num), sub_zero] at hx
    have h1 := (le_abs_self _).trans (abs_uProf_le i hγ hα x)
    have h2 : vecEuclideanNorm x ^ α ≤ (1 / 2 : ℝ) ^ α :=
      Real.rpow_le_rpow (vecEuclideanNorm_nonneg x) hx.le hα.le
    linarith
  · intro c hc
    have hlim : Tendsto (fun s : ℝ => 1 + s ^ α) (𝓝[<] (1 / 2 : ℝ)) (𝓝 (1 + (1 / 2 : ℝ) ^ α)) := by
      have : ContinuousAt (fun s : ℝ => 1 + s ^ α) (1 / 2 : ℝ) :=
        continuousAt_const.add (Real.continuousAt_rpow_const _ _ (Or.inl (by norm_num)))
      exact this.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 / 2 by norm_num)] with s hs
    have := hc ⟨_, single_smul_mem_euclideanBall i hs.1 hs.2, rfl⟩
    simpa [uProf_ray i hγ α hs.1] using this

/-- Exact infimum of `1 + u` over `B_{1/2}`. -/
theorem uProf_isGLB (i : Fin d) {γ α : ℝ} (hγ : 1 ≤ γ) (hα : 0 < α) :
    IsGLB ((fun x => 1 + uProf i γ α x) '' euclideanBall (0 : Vec d) (1 / 2))
      (1 - (1 / 2 : ℝ) ^ α) := by
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num), sub_zero] at hx
    have h1 := neg_le_of_abs_le (abs_uProf_le i hγ hα x)
    have h2 : vecEuclideanNorm x ^ α ≤ (1 / 2 : ℝ) ^ α :=
      Real.rpow_le_rpow (vecEuclideanNorm_nonneg x) hx.le hα.le
    linarith
  · intro c hc
    have hlim : Tendsto (fun s : ℝ => 1 - s ^ α) (𝓝[<] (1 / 2 : ℝ)) (𝓝 (1 - (1 / 2 : ℝ) ^ α)) := by
      have : ContinuousAt (fun s : ℝ => 1 - s ^ α) (1 / 2 : ℝ) :=
        continuousAt_const.sub (Real.continuousAt_rpow_const _ _ (Or.inl (by norm_num)))
      exact this.tendsto.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 / 2 by norm_num)] with s hs
    have := hc ⟨_, neg_single_smul_mem_euclideanBall i hs.1 hs.2, rfl⟩
    simp only [uProf_neg_ray i hγ α hs.1] at this
    linarith

/-- `1 + u > 0` on `B_1` (indeed on `|x| < 1`). -/
theorem one_add_uProf_pos (i : Fin d) {γ α : ℝ} (hγ : 1 ≤ γ) (hα : 0 < α) {x : Vec d}
    (hx : x ∈ euclideanBall (0 : Vec d) 1) : 0 < 1 + uProf i γ α x := by
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt one_pos, sub_zero] at hx
  have h1 := neg_le_of_abs_le (abs_uProf_le i hγ hα x)
  have h2 : vecEuclideanNorm x ^ α < 1 := Real.rpow_lt_one (vecEuclideanNorm_nonneg x) hx hα
  linarith

/-- Arithmetic of the Harnack ratio: if `0 < α ≤ exp(-x)` then
`exp(x)(1 - 2^{-α}) ≤ 1 + 2^{-α}`. -/
theorem harnack_ratio_arith {α x : ℝ} (hα : 0 < α) (hαx : α ≤ Real.exp (-x)) :
    Real.exp x * (1 - (1 / 2 : ℝ) ^ α) ≤ 1 + (1 / 2 : ℝ) ^ α := by
  set q : ℝ := (1 / 2 : ℝ) ^ α with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) α
  have hq1 : q ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) hα.le
  have hq_eq : q = Real.exp (-(α * Real.log 2)) := by
    rw [hq, Real.rpow_def_of_pos (by norm_num), one_div, Real.log_inv]; congr 1; ring
  have hlog : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have h1 : 1 - q ≤ α := by
    have := Real.add_one_le_exp (-(α * Real.log 2))
    rw [← hq_eq] at this
    nlinarith
  have hex : Real.exp x * α ≤ 1 := by
    have : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos x]
  have hex0 := Real.exp_pos x
  have : Real.exp x * (1 - q) ≤ 1 := by
    calc Real.exp x * (1 - q) ≤ Real.exp x * α := mul_le_mul_of_nonneg_left h1 hex0.le
      _ ≤ 1 := hex
  linarith

/-- With `Λ = (80γ)²`, `α ≤ exp(-√Λ/40)` gives the ratio bound. -/
theorem harnack_ratio_arith_sqrt {α Λ : ℝ} (hα : 0 < α) (hαΛ : α ≤ Real.exp (-(Real.sqrt Λ / 40))) :
    Real.exp (Real.sqrt Λ / 40) * (1 - (1 / 2 : ℝ) ^ α) ≤ 1 + (1 / 2 : ℝ) ^ α :=
  harnack_ratio_arith hα hαΛ

end PDE.Guerra
