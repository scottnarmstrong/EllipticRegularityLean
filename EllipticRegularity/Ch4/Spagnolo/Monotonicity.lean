module

public import EllipticRegularity.Ch4.Spagnolo.DifferentialInequality
public import EllipticRegularity.Ch4.Spagnolo.Profiles

/-!
# The Piccinini--Spagnolo monotonicity formula (Theorem 4.24)

For `d = 2`, a measurable symmetric coefficient field with (4.1) and a
weak solution `u ∈ H¹(B₁)` of `-∇·a∇u = 0`, the function
`r ↦ r^{-2/√Λ} ∫_{B_r} ∇u·a∇u` is nondecreasing on `(0, 1)`.

The integrated differential inequality of `DifferentialInequality.lean` is
applied to the smooth profiles `H_n` of `Profiles.lean`; dominated convergence
passes to the kink profile, and an elementary pointwise comparison gives
`ρ₁^{-β} φ(ρ₁) ≤ ρ₂^{-β} φ(ρ₂)` for `0 < ρ₁ < ρ₂ < 1` (manuscript Step 4).

The Wirtinger inequality (Lemma 4.23) enters as the
explicit hypothesis `hWirtinger`, stated verbatim as the conclusion of the
statement `PDE.wirtinger_inequality`.
-/

@[expose] public section

namespace PDE.Ch4Spagnolo

open MeasureTheory Set Filter
open scoped Topology

section Solution

variable {Λ : ℝ} {a : CoeffField 2}

local notation "𝔹" => euclideanBall (0 : Vec 2) 1

theorem measurable_profileLim (r A0 B0 : ℝ) : Measurable (profileLim r A0 B0) := by
  unfold profileLim
  refine Measurable.ite measurableSet_Iic ?_ measurable_const
  fun_prop

theorem measurable_weightLim (r A0 B0 : ℝ) : Measurable (weightLim r A0 B0) := by
  unfold weightLim
  refine Measurable.ite measurableSet_Ioo ?_ measurable_const
  fun_prop

/-- The integrated differential inequality for the kink profile, obtained from
the smooth profiles by dominated convergence. -/
theorem integral_profileLim_le (hW : WirtingerStatement)
    (hmeas : ∀ i j : Fin 2, AEMeasurable (fun x => a x i j) (volumeOn 𝔹))
    (hsymm : ∀ x ∈ 𝔹, ∀ i j : Fin 2, a x i j = a x j i)
    (hell : ∀ x ∈ 𝔹, IsEllipticMatrix 1 Λ (a x))
    (u : H1Function 𝔹)
    (hsol : IsWeakDivergenceFormSolutionOn a 𝔹 u (0 : Vec 2 → ℝ) 0)
    {r A0 B0 : ℝ} (hr : 0 < r) (hA0 : 0 < A0) (hAB : A0 ≤ B0) (hB1 : B0 < 1) :
    ∫ x in 𝔹, profileLim r A0 B0 (vecNormSq x) *
        vecDot (u.grad x) (matVecMul (a x) (u.grad x)) ≤
      Real.sqrt Λ * ∫ x in 𝔹, weightLim r A0 B0 (vecNormSq x) *
        (vecNormSq x * vecDot (u.grad x) (matVecMul (a x) (u.grad x))) := by
  set e : Vec 2 → ℝ := fun x => vecDot (u.grad x) (matVecMul (a x) (u.grad x)) with he
  have he_int : IntegrableOn e 𝔹 := integrableOn_energy hmeas hell u
  have hNe_int : IntegrableOn (fun x => vecNormSq x * e x) 𝔹 :=
    integrableOn_continuous_mul continuous_vecNormSq he_int
  have hB0 : 0 < B0 := lt_of_lt_of_le hA0 hAB
  set K : ℝ := 1 / 2 * A0 ^ (-r - 1) with hK
  have hK0 : 0 ≤ K := mul_nonneg (by norm_num) (Real.rpow_nonneg hA0.le _)
  -- the differential inequality for each smooth profile
  have hDI : ∀ n : ℕ, ∫ x in 𝔹, profileSeq r A0 B0 n (vecNormSq x) * e x ≤
      Real.sqrt Λ * ∫ x in 𝔹, weightSeq r A0 B0 n (vecNormSq x) * (vecNormSq x * e x) := by
    intro n
    have hH' : ∀ t, deriv (profileSeq r A0 B0 n) t ≤ 0 := by
      intro t
      rw [deriv_profileSeq hA0 n t]
      have := weightSeq_nonneg (r := r) (A0 := A0) (B0 := B0) hA0 n t
      linarith
    have h := integral_radial_energy_le hW hmeas hsymm hell u hsol (contDiff_profileSeq hA0 n)
      hH' hB1 (fun t ht => profileSeq_eq_zero_of_ge n ht)
    simpa only [deriv_profileSeq hA0 n, neg_neg] using h
  -- dominated convergence on both sides
  have hL : Tendsto (fun n => ∫ x in 𝔹, profileSeq r A0 B0 n (vecNormSq x) * e x) atTop
      (𝓝 (∫ x in 𝔹, profileLim r A0 B0 (vecNormSq x) * e x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => K * B0 * ‖e x‖) (fun n => ?_)
      (he_int.norm.const_mul _) (fun n => ?_) (Eventually.of_forall fun x => ?_)
    · exact (integrableOn_continuous_mul
        ((contDiff_profileSeq hA0 n).continuous.comp continuous_vecNormSq)
        he_int).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (abs_profileSeq_le hr hA0 hB0 n (vecNormSq_nonneg x)) (norm_nonneg _)
    · exact (tendsto_profileSeq hr hA0 hAB _).mul_const _
  have hR : Tendsto (fun n => ∫ x in 𝔹, weightSeq r A0 B0 n (vecNormSq x) *
      (vecNormSq x * e x)) atTop
      (𝓝 (∫ x in 𝔹, weightLim r A0 B0 (vecNormSq x) * (vecNormSq x * e x))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => K * ‖vecNormSq x * e x‖)
      (fun n => ?_) (hNe_int.norm.const_mul _) (fun n => ?_)
      (Eventually.of_forall fun x => ?_)
    · exact (integrableOn_continuous_mul
        ((contDiff_weightSeq hA0 n).continuous.comp continuous_vecNormSq)
        hNe_int).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (weightSeq_nonneg hA0 n _)]
      exact mul_le_mul_of_nonneg_right (weightSeq_le hr hA0 n _) (norm_nonneg _)
    · exact (tendsto_weightSeq _).mul_const _
  exact le_of_tendsto_of_tendsto' hL (hR.const_mul _) hDI

/-- The comparison `ρ₁^{-β} φ(ρ₁) ≤ ρ₂^{-β} φ(ρ₂)` for `0 < ρ₁ < ρ₂ < 1`. -/
theorem rpow_mul_energy_le (hW : WirtingerStatement)
    (hmeas : ∀ i j : Fin 2, AEMeasurable (fun x => a x i j) (volumeOn 𝔹))
    (hsymm : ∀ x ∈ 𝔹, ∀ i j : Fin 2, a x i j = a x j i)
    (hell : ∀ x ∈ 𝔹, IsEllipticMatrix 1 Λ (a x))
    (u : H1Function 𝔹)
    (hsol : IsWeakDivergenceFormSolutionOn a 𝔹 u (0 : Vec 2 → ℝ) 0)
    {ρ1 ρ2 : ℝ} (hρ1 : 0 < ρ1) (hρ12 : ρ1 < ρ2) (hρ2 : ρ2 < 1) :
    ρ1 ^ (-(2 / Real.sqrt Λ)) *
        ∫ x in euclideanBall (0 : Vec 2) ρ1, vecDot (u.grad x) (matVecMul (a x) (u.grad x)) ≤
      ρ2 ^ (-(2 / Real.sqrt Λ)) *
        ∫ x in euclideanBall (0 : Vec 2) ρ2, vecDot (u.grad x) (matVecMul (a x) (u.grad x)) := by
  set e : Vec 2 → ℝ := fun x => vecDot (u.grad x) (matVecMul (a x) (u.grad x)) with he
  have he_int : IntegrableOn e 𝔹 := integrableOn_energy hmeas hell u
  have hΛ1 : 1 ≤ Λ := (hell 0 (center_mem_euclideanBall (0 : Vec 2) one_pos)).lam_le_Lam
  set L : ℝ := Real.sqrt Λ with hL
  have hLpos : 0 < L := Real.sqrt_pos.2 (by linarith)
  set r : ℝ := 1 / L with hr
  have hrpos : 0 < r := by positivity
  set A0 : ℝ := ρ1 ^ 2 with hA0
  set B0 : ℝ := ρ2 ^ 2 with hB0
  have hA0pos : 0 < A0 := by positivity
  have hAB : A0 < B0 := by nlinarith
  have hB1 : B0 < 1 := by nlinarith
  have hpow : ∀ ρ : ℝ, 0 < ρ → (ρ ^ 2) ^ (-r) = ρ ^ (-(2 / L)) := by
    intro ρ hρ
    rw [← Real.rpow_two, ← Real.rpow_mul hρ.le]
    congr 1
    simp only [hr]; ring
  have hmain := integral_profileLim_le hW hmeas hsymm hell u hsol hrpos hA0pos hAB.le hB1
  -- integrability of the limit profiles
  have hPLb : ∀ t, 0 ≤ t → |profileLim r A0 B0 t| ≤ 1 / 2 * A0 ^ (-r - 1) * B0 := by
    intro t ht
    exact le_of_tendsto' ((tendsto_profileSeq hrpos hA0pos hAB.le t).abs)
      fun n => abs_profileSeq_le hrpos hA0pos (by linarith) n ht
  have hWLb : ∀ t, |weightLim r A0 B0 t| ≤ 1 / 2 * A0 ^ (-r - 1) := by
    intro t
    exact le_of_tendsto' ((tendsto_weightSeq t).abs) fun n => by
      rw [abs_of_nonneg (weightSeq_nonneg hA0pos n t)]
      exact weightSeq_le hrpos hA0pos n t
  have hI1 : IntegrableOn (fun x => profileLim r A0 B0 (vecNormSq x) * e x) 𝔹 :=
    Integrable.bdd_mul he_int
      ((measurable_profileLim r A0 B0).comp_aemeasurable
        continuous_vecNormSq.aemeasurable).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hPLb _ (vecNormSq_nonneg x))
  have hI2 : IntegrableOn (fun x => weightLim r A0 B0 (vecNormSq x) *
      (vecNormSq x * e x)) 𝔹 :=
    Integrable.bdd_mul (integrableOn_continuous_mul continuous_vecNormSq he_int)
      ((measurable_weightLim r A0 B0).comp_aemeasurable
        continuous_vecNormSq.aemeasurable).aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hWLb _)
  -- the balls as indicator sets
  have hmemball : ∀ {ρ : ℝ} (x : Vec 2), x ∈ euclideanBall (0 : Vec 2) ρ ↔
      vecNormSq x < ρ ^ 2 := by
    intro ρ x
    change vecNormSq (x - 0) < ρ ^ 2 ↔ _
    rw [sub_zero]
  have hball_sub : ∀ {ρ : ℝ}, 0 < ρ → ρ < 1 → euclideanBall (0 : Vec 2) ρ ⊆ 𝔹 :=
    fun hρ hρ1 => euclideanBall_mono hρ.le hρ1.le
  have hφ : ∀ {ρ : ℝ}, 0 < ρ → ρ < 1 →
      ∫ x in 𝔹, (euclideanBall (0 : Vec 2) ρ).indicator e x =
        ∫ x in euclideanBall (0 : Vec 2) ρ, e x := by
    intro ρ hρ hρ1
    rw [setIntegral_indicator (measurableSet_euclideanBall _ _),
      inter_eq_right.2 (hball_sub hρ hρ1)]
  have hIind : ∀ ρ : ℝ, IntegrableOn ((euclideanBall (0 : Vec 2) ρ).indicator e) 𝔹 :=
    fun ρ => he_int.indicator (measurableSet_euclideanBall _ _)
  -- the pointwise comparison
  have hpt : ∀ x ∈ 𝔹,
      ρ1 ^ (-(2 / L)) * (euclideanBall (0 : Vec 2) ρ1).indicator e x -
          ρ2 ^ (-(2 / L)) * (euclideanBall (0 : Vec 2) ρ2).indicator e x ≤
        2 / L * (profileLim r A0 B0 (vecNormSq x) * e x) -
          2 * (weightLim r A0 B0 (vecNormSq x) * (vecNormSq x * e x)) := by
    intro x hx
    have he0 : 0 ≤ e x := energy_nonneg hell u hx
    have hN0 : 0 ≤ vecNormSq x := vecNormSq_nonneg x
    have h2L : 2 / L / (2 * r) = 1 := by simp only [hr]; field_simp
    rw [← hpow ρ1 hρ1, ← hpow ρ2 (hρ1.trans hρ12)]
    have hA0r : 0 ≤ A0 ^ (-r) := Real.rpow_nonneg hA0pos.le _
    have hB0r : 0 ≤ B0 ^ (-r) := Real.rpow_nonneg (by linarith) _
    by_cases h1 : vecNormSq x < A0
    · -- inside the smaller ball
      have hin1 : x ∈ euclideanBall (0 : Vec 2) ρ1 := (hmemball x).2 h1
      have hin2 : x ∈ euclideanBall (0 : Vec 2) ρ2 := (hmemball x).2 (by linarith)
      have hPL : profileLim r A0 B0 (vecNormSq x) = (A0 ^ (-r) - B0 ^ (-r)) / (2 * r) := by
        have hNB : vecNormSq x ≤ B0 := by linarith
        simp only [profileLim, hNB, ↓reduceIte, max_eq_right h1.le]
      have hWL : weightLim r A0 B0 (vecNormSq x) = 0 := by
        simp only [weightLim, mem_Ioo, not_lt.2 h1.le, false_and, ↓reduceIte]
      rw [indicator_of_mem hin1, indicator_of_mem hin2, hPL, hWL]
      have : 2 / L * ((A0 ^ (-r) - B0 ^ (-r)) / (2 * r) * e x) =
          (A0 ^ (-r) - B0 ^ (-r)) * e x := by
        rw [show 2 / L * ((A0 ^ (-r) - B0 ^ (-r)) / (2 * r) * e x) =
          2 / L / (2 * r) * ((A0 ^ (-r) - B0 ^ (-r)) * e x) by ring, h2L, one_mul]
      rw [this]
      nlinarith
    · have hout1 : x ∉ euclideanBall (0 : Vec 2) ρ1 := fun h => h1 ((hmemball x).1 h)
      rw [indicator_of_notMem hout1, mul_zero, zero_sub]
      by_cases h2 : vecNormSq x < B0
      · have hin2 : x ∈ euclideanBall (0 : Vec 2) ρ2 := (hmemball x).2 h2
        rw [indicator_of_mem hin2]
        have hNA : A0 ≤ vecNormSq x := not_lt.1 h1
        have hPL : profileLim r A0 B0 (vecNormSq x) =
            (vecNormSq x ^ (-r) - B0 ^ (-r)) / (2 * r) := by
          simp only [profileLim, h2.le, ↓reduceIte, max_eq_left hNA]
        rw [hPL]
        have hmain' : 2 / L * ((vecNormSq x ^ (-r) - B0 ^ (-r)) / (2 * r) * e x) =
            (vecNormSq x ^ (-r) - B0 ^ (-r)) * e x := by
          rw [show 2 / L * ((vecNormSq x ^ (-r) - B0 ^ (-r)) / (2 * r) * e x) =
            2 / L / (2 * r) * ((vecNormSq x ^ (-r) - B0 ^ (-r)) * e x) by ring, h2L, one_mul]
        rw [hmain']
        rcases eq_or_lt_of_le hNA with hEq | hlt
        · -- on the sphere `|x| = ρ₁`
          have hWL : weightLim r A0 B0 (vecNormSq x) = 0 := by
            simp only [weightLim, mem_Ioo, ← hEq, lt_irrefl, false_and, ↓reduceIte]
          rw [hWL, ← hEq]
          nlinarith [mul_nonneg hA0r he0]
        · have hNpos : 0 < vecNormSq x := hA0pos.trans hlt
          have hWL : weightLim r A0 B0 (vecNormSq x) * vecNormSq x =
              1 / 2 * vecNormSq x ^ (-r) := by
            simp only [weightLim, mem_Ioo, hlt, h2, and_self, ↓reduceIte]
            rw [mul_assoc, ← Real.rpow_add_one hNpos.ne']
            ring_nf
          have : weightLim r A0 B0 (vecNormSq x) * (vecNormSq x * e x) =
              1 / 2 * vecNormSq x ^ (-r) * e x := by
            rw [← hWL]; ring
          rw [this]
          nlinarith
      · have hout2 : x ∉ euclideanBall (0 : Vec 2) ρ2 := fun h => h2 ((hmemball x).1 h)
        rw [indicator_of_notMem hout2, mul_zero, neg_zero]
        have hBN : B0 ≤ vecNormSq x := not_lt.1 h2
        have hPL : profileLim r A0 B0 (vecNormSq x) = 0 := by
          unfold profileLim
          split_ifs with h3
          · have hEq : vecNormSq x = B0 := le_antisymm h3 hBN
            rw [hEq, max_eq_left hAB.le, sub_self, zero_div]
          · rfl
        have hWL : weightLim r A0 B0 (vecNormSq x) = 0 := by
          simp only [weightLim, mem_Ioo, not_lt.2 hBN, and_false, ↓reduceIte]
        rw [hPL, hWL]
        simp
  -- integrate the pointwise comparison
  have hJ1 : IntegrableOn (fun x =>
      ρ1 ^ (-(2 / L)) * (euclideanBall (0 : Vec 2) ρ1).indicator e x) 𝔹 :=
    (hIind ρ1).const_mul _
  have hJ2 : IntegrableOn (fun x =>
      ρ2 ^ (-(2 / L)) * (euclideanBall (0 : Vec 2) ρ2).indicator e x) 𝔹 :=
    (hIind ρ2).const_mul _
  have hJ3 : IntegrableOn (fun x => 2 / L * (profileLim r A0 B0 (vecNormSq x) * e x)) 𝔹 :=
    hI1.const_mul _
  have hJ4 : IntegrableOn (fun x =>
      2 * (weightLim r A0 B0 (vecNormSq x) * (vecNormSq x * e x))) 𝔹 :=
    hI2.const_mul _
  have hint : ∫ x in 𝔹, (ρ1 ^ (-(2 / L)) * (euclideanBall (0 : Vec 2) ρ1).indicator e x -
        ρ2 ^ (-(2 / L)) * (euclideanBall (0 : Vec 2) ρ2).indicator e x) ≤
      ∫ x in 𝔹, (2 / L * (profileLim r A0 B0 (vecNormSq x) * e x) -
        2 * (weightLim r A0 B0 (vecNormSq x) * (vecNormSq x * e x))) :=
    setIntegral_mono_on (hJ1.sub hJ2) (hJ3.sub hJ4) (measurableSet_euclideanBall _ _) hpt
  rw [integral_sub hJ1 hJ2, integral_sub hJ3 hJ4, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, hφ hρ1 (hρ12.trans hρ2),
    hφ (hρ1.trans hρ12) hρ2] at hint
  have hLmain := mul_le_mul_of_nonneg_left hmain (show (0 : ℝ) ≤ 2 / L by positivity)
  have hcancel : 2 / L * (L * ∫ x in 𝔹, weightLim r A0 B0 (vecNormSq x) *
      (vecNormSq x * e x)) = 2 * ∫ x in 𝔹, weightLim r A0 B0 (vecNormSq x) *
      (vecNormSq x * e x) := by
    field_simp
  rw [hcancel] at hLmain
  linarith

end Solution

/-- **Piccinini--Spagnolo monotonicity formula** (Theorem 4.24), in the
exact form of the statement `PDE.piccinini_spagnolo_monotonicity`, with the
Wirtinger inequality (Lemma 4.23) as the explicit hypothesis
`hWirtinger`. -/
theorem piccinini_spagnolo_monotonicity_full
    (hWirtinger : ∀ w : ℝ → ℝ, Function.Periodic w (2 * Real.pi) →
      AbsolutelyContinuousOnInterval w 0 (2 * Real.pi) →
      MemLp (deriv w) 2 (volume.restrict (Set.Icc 0 (2 * Real.pi))) →
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (w θ - (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..(2 * Real.pi), w t) ^ 2 ≤
        ∫ θ in (0 : ℝ)..(2 * Real.pi), (deriv w θ) ^ 2)
    (Λ : ℝ) (a : CoeffField 2)
    (hmeas : ∀ i j : Fin 2, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec 2) 1)))
    (hsymm : ∀ x ∈ euclideanBall (0 : Vec 2) 1, ∀ i j : Fin 2, a x i j = a x j i)
    (hell : ∀ x ∈ euclideanBall (0 : Vec 2) 1, IsEllipticMatrix 1 Λ (a x))
    (u : H1Function (euclideanBall (0 : Vec 2) 1))
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec 2) 1) u
      (0 : Vec 2 → ℝ) 0) :
    MonotoneOn
      (fun r : ℝ => r ^ (-(2 / Real.sqrt Λ)) *
        ∫ x in euclideanBall (0 : Vec 2) r, vecDot (u.grad x) (matVecMul (a x) (u.grad x)))
      (Set.Ioo 0 1) := by
  intro ρ1 hρ1 ρ2 hρ2 hle
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [heq]
  · exact rpow_mul_energy_le hWirtinger hmeas hsymm hell u hsol hρ1.1 hlt hρ2.2

end PDE.Ch4Spagnolo
