module

public import EllipticRegularity.Meyers.Assembly
public import PDEFoundation.Measure.EuclideanFieldMeasurability

/-!
# Assembly of the Meyers estimate: the Dirichlet estimate for `p ≥ 2`

Two steps of the proof of Theorem 4.4: the case `p = 2`
(tested with `u` itself) and the case `p > 2` (Gehring's lemma
(a) with `σ = 4` on zero extensions), and the single theorem
`meyers_interior_and_dirichlet_high` combining them with the interior clause.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

namespace MeyersAssembly

variable {d : ℕ}

local notation "𝔹" => euclideanBall (0 : Vec d) 1

section Dirichlet

theorem le_of_sq_le_sq {X Y : ℝ≥0∞} (h : X ^ 2 ≤ Y ^ 2) : X ≤ Y := by
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_two] at h
  exact (ENNReal.rpow_le_rpow_iff two_pos).1 h

theorem le_of_sq_le_mul {X Z : ℝ≥0∞} {b K : ℝ} (hb : b ≤ K ^ 2) (hK : 0 ≤ K)
    (h : X ^ 2 ≤ ENNReal.ofReal b * Z ^ 2) : X ≤ ENNReal.ofReal K * Z := by
  have := le_of_sq_le_add (X := X) (Y := 0) (Z := Z) (a := 0) (b := b) (K := K)
    (by positivity) hb hK (by simpa using h)
  simpa using this

theorem eLpNorm_two_sq_eq {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφ : AEStronglyMeasurable φ (volumeOn U)) (hnn : ∀ x, 0 ≤ φ x)
    (hint : IntegrableOn (fun x => φ x ^ 2) U) :
    eLpNorm φ 2 (volumeOn U) ^ 2 = ENNReal.ofReal (∫ x in U, φ x ^ 2) := by
  have h := eLpNorm_sq_eq hφ hnn (one_pos : (0 : ℝ) < 1)
  rw [ENNReal.ofReal_one, show 2 * (1 : ℝ) = 2 by norm_num] at h
  have e : ENNReal.ofReal 2 = 2 := by simp
  rw [e] at h
  rw [← h, eLpNorm_one_eq_lintegral_enorm,
    ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall
      fun x => sq_nonneg (φ x))]
  · refine lintegral_congr fun x => ?_
    rw [Real.enorm_of_nonneg (sq_nonneg _)]
  · exact hint.aestronglyMeasurable

theorem memVectorL2On_of_memLp {f : Vec d → Vec d}
    (hfm : ∀ i : Fin d, AEStronglyMeasurable (fun x => f x i)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hf2 : MemLp (fun x => vecEuclideanNorm (f x)) 2
      (volumeOn (euclideanBall (0 : Vec d) 1))) :
    MemVectorL2On (euclideanBall (0 : Vec d) 1) f := by
  intro i
  refine hf2.mono' (hfm i) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact abs_apply_le_vecEuclideanNorm (f x) i

/-- Theorem 4.4: the energy estimate `‖∇u‖_{L²} ≤ ‖f‖_{L²}` for `u ∈ H¹₀(B₁)`,
obtained by testing the equation with `u` itself. -/
theorem dirichlet_energy {Λ : ℝ} {a : CoeffField d}
    (ha : ∀ i j : Fin d,
      AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x))
    {f : Vec d → Vec d}
    (hfm : ∀ i : Fin d, AEStronglyMeasurable (fun x => f x i)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hf2 : MemLp (fun x => vecEuclideanNorm (f x)) 2
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (u : H10Function (euclideanBall (0 : Vec d) 1))
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1)
      u.toH1Function (0 : Vec d → ℝ) f) :
    eLpNorm (fun x => Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x)))) 2
        (volumeOn (euclideanBall (0 : Vec d) 1)) ≤
      eLpNorm (fun x => vecEuclideanNorm (f x)) 2 (volumeOn (euclideanBall (0 : Vec d) 1)) := by
  set w : Vec d → ℝ := fun x => Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x)))
    with hw_def
  have hF : MemVectorL2On 𝔹 f := memVectorL2On_of_memLp hfm hf2
  have hL2 : IsWeakDivergenceFormL2SolutionOn a 𝔹 u.toH1Function 0 f :=
    { flux_memL2 := memVectorL2On_flux ha hell u.gradMemL2
      source_memL2 := MeasureTheory.MemLp.zero
      forcing_memL2 := hF
      identity := fun φ => (hsol φ).2 }
  have htest := hL2.toH10SolutionOn u
  have hforce : IntegrableOn (fun x => vecDot (f x) (u.grad x)) 𝔹 :=
    (hL2.toDivergenceFormL2DataOn.h10_testable u).forcing_integrable
  have hint : IntegrableOn (fun x => w x ^ 2) 𝔹 := integrableOn_w_sq ha hell u.gradMemL2
  have hf_int : IntegrableOn (fun x => vecEuclideanNorm (f x) ^ 2) 𝔹 := hf2.integrable_sq
  have hwm : AEStronglyMeasurable w (volumeOn 𝔹) := aestronglyMeasurable_w ha hell u.gradMemL2
  have hw0 : ∀ x, 0 ≤ w x := fun x => Real.sqrt_nonneg _
  -- the identity `∫ w² = - ∫ f · ∇u`
  have hid : ∫ x in 𝔹, w x ^ 2 = -∫ x in 𝔹, vecDot (f x) (u.grad x) := by
    have h1 : ∫ x in 𝔹, w x ^ 2 = ∫ x in 𝔹, vecDot (matVecMul (a x) (u.grad x)) (u.grad x) := by
      refine setIntegral_congr_fun ball_measurableSet fun x hx => ?_
      simp only [hw_def]
      rw [energy_sq (hell x hx), vecDot_comm]
    have h2 := htest.2
    simp only [Pi.zero_apply, zero_mul, integral_zero, zero_sub] at h2
    rw [h1]
    exact h2
  have hbound : ∫ x in 𝔹, -vecDot (f x) (u.grad x) ≤
      ∫ x in 𝔹, (1 / 2 * vecEuclideanNorm (f x) ^ 2 + 1 / 2 * w x ^ 2) := by
    refine setIntegral_mono_on hforce.neg ((hf_int.const_mul _).add (hint.const_mul _))
      ball_measurableSet fun x hx => ?_
    have hgw := vecEuclideanNorm_le_energy (hell x hx) (u.grad x)
    have hcs := abs_vecDot_le_vecEuclideanNorm_mul (f x) (u.grad x)
    have hg0 := vecEuclideanNorm_nonneg (u.grad x)
    have hf0 := vecEuclideanNorm_nonneg (f x)
    have hwsq : w x ^ 2 ≥ vecEuclideanNorm (u.grad x) ^ 2 := by
      gcongr
    nlinarith [neg_abs_le (vecDot (f x) (u.grad x)), sq_nonneg (vecEuclideanNorm (f x) - vecEuclideanNorm (u.grad x)),
      mul_le_mul_of_nonneg_left hgw hf0]
  rw [integral_add (hf_int.const_mul _) (hint.const_mul _), integral_const_mul,
    integral_const_mul, integral_neg] at hbound
  have hWF : ∫ x in 𝔹, w x ^ 2 ≤ ∫ x in 𝔹, vecEuclideanNorm (f x) ^ 2 := by
    rw [hid]; linarith
  have hfm2 : AEStronglyMeasurable (fun x => vecEuclideanNorm (f x)) (volumeOn 𝔹) :=
    hf2.aestronglyMeasurable
  refine le_of_sq_le_sq ?_
  rw [eLpNorm_two_sq_eq hwm hw0 hint,
    eLpNorm_two_sq_eq hfm2 (fun x => vecEuclideanNorm_nonneg _) hf_int]
  exact ENNReal.ofReal_le_ofReal hWF

/-- The Dirichlet clause of Theorem 4.4: the Dirichlet estimate
for `2 ≤ p ≤ 2 + c / √Λ`, for fixed constants. -/
theorem dirichlet_clause {C₁ C₀ : ℝ} (hC₁ : 1 ≤ C₁) (hC₀ : 1 ≤ C₀)
    (hG : GehringWith d C₁) (hR : MeyersRHBoundaryWith d C₀)
    (Λ : ℝ) (a : CoeffField d)
    (ha : ∀ i j : Fin d,
      AEMeasurable (fun x => a x i j) (volumeOn 𝔹))
    (hell : ∀ x ∈ 𝔹, IsEllipticMatrix 1 Λ (a x))
    (p : ℝ) (hp : 2 ≤ p) (hpΛ : p ≤ 2 + (2 / (C₁ * C₀)) / Real.sqrt Λ)
    (f : Vec d → Vec d)
    (hfm : ∀ i : Fin d, AEStronglyMeasurable (fun x => f x i) (volumeOn 𝔹))
    (hf2 : MemLp (fun x => vecEuclideanNorm (f x)) 2 (volumeOn 𝔹))
    (hfp : MemLp (fun x => vecEuclideanNorm (f x)) (ENNReal.ofReal p) (volumeOn 𝔹))
    (u : H10Function 𝔹)
    (hsol : IsWeakDivergenceFormSolutionOn a 𝔹 u.toH1Function (0 : Vec d → ℝ) f) :
    eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p) (volumeOn 𝔹) ≤
      ENNReal.ofReal (C₁ * C₀ * 2 ^ d) *
        eLpNorm (fun x => vecEuclideanNorm (f x)) (ENNReal.ofReal p) (volumeOn 𝔹) := by
  set w : Vec d → ℝ := fun x => Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x)))
    with hw_def
  have hw0 : ∀ x, 0 ≤ w x := fun x => Real.sqrt_nonneg _
  have hwm : AEStronglyMeasurable w (volumeOn 𝔹) := aestronglyMeasurable_w ha hell u.gradMemL2
  have hΛ := one_le_of_elliptic hell
  have hK : 1 ≤ C₁ * C₀ := by nlinarith
  have hpow : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have hKle : C₁ * C₀ ≤ C₁ * C₀ * 2 ^ d := by nlinarith
  have hgrad : eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p) (volumeOn 𝔹) ≤
      eLpNorm w (ENNReal.ofReal p) (volumeOn 𝔹) := by
    have hae : ∀ᵐ x ∂(volumeOn 𝔹), ‖vecEuclideanNorm (u.grad x)‖ ≤ ‖w x‖ := by
      filter_upwards [ae_restrict_mem ball_measurableSet] with x hx
      rw [Real.norm_of_nonneg (vecEuclideanNorm_nonneg _), Real.norm_of_nonneg (hw0 x)]
      exact vecEuclideanNorm_le_energy (hell x hx) (u.grad x)
    exact eLpNorm_mono_ae
      (aestronglyMeasurable_vecEuclideanNorm_of_coord fun i =>
        (u.gradMemL2 i).aestronglyMeasurable) hae
  rcases hp.eq_or_lt with h2 | h2
  · subst h2
    have e2 : ENNReal.ofReal (2 : ℝ) = 2 := by simp
    rw [e2] at hgrad ⊢
    refine hgrad.trans ((dirichlet_energy ha hell hfm hf2 u hsol).trans ?_)
    calc _ = 1 * eLpNorm (fun x => vecEuclideanNorm (f x)) 2 (volumeOn 𝔹) := (one_mul _).symm
      _ ≤ _ := by
        gcongr
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (by linarith)
  · set ε : ℝ := (p - 2) / 2 with hε_def
    have hε : 0 < ε := by rw [hε_def]; linarith
    obtain ⟨hεle, hA⟩ := epsilon_le_of_le_exponent hC₁ hC₀ hΛ hpΛ
    have hf0 : ∀ x, 0 ≤ vecEuclideanNorm (f x) := fun x => vecEuclideanNorm_nonneg _
    have hfm2 : AEStronglyMeasurable (fun x => vecEuclideanNorm (f x)) (volumeOn 𝔹) :=
      hfp.aestronglyMeasurable
    have hint : IntegrableOn (fun x => w x ^ 2) 𝔹 := integrableOn_w_sq ha hell u.gradMemL2
    have hhmem : MemLp (fun x => vecEuclideanNorm (f x) ^ 2)
        (ENNReal.ofReal (1 + ε)) (volumeOn 𝔹) := memLp_sq_of_memLp h2 hfp hf0
    have hrh : ∀ (z : Vec d) (r : ℝ), 0 < r →
        ∫ x in centeredAxisCube z r, (Set.indicator 𝔹 (fun y => w y ^ 2)) x ≤
          (C₀ * Real.sqrt Λ) * (volume (centeredAxisCube z r)).toReal *
              (integralAverage (centeredAxisCube z (4 * r))
                (fun x => (Set.indicator 𝔹 (fun y => w y ^ 2)) x ^
                  ((d : ℝ) / ((d : ℝ) + 1)))) ^ (((d : ℝ) + 1) / (d : ℝ)) +
            C₀ * ∫ x in centeredAxisCube z (4 * r),
              (Set.indicator 𝔹 (fun y => vecEuclideanNorm (f y) ^ 2)) x :=
      fun z r hr => hR Λ a ha hell f hfm hf2 u hsol z r hr
    have hcpt : HasCompactSupport (Set.indicator 𝔹 (fun y => w y ^ 2)) := by
      refine HasCompactSupport.intro (isCompact_euclideanClosedBall (0 : Vec d) zero_le_one) ?_
      intro x hx
      exact Set.indicator_of_notMem
        (fun hx' => hx (euclideanBall_subset_euclideanClosedBall _ _ hx')) _
    have hmain := (hG 4 (Or.inr rfl) (C₀ * Real.sqrt Λ) C₀ ε hA (by linarith) hε hεle
      (Set.indicator 𝔹 (fun y => w y ^ 2)) (Set.indicator 𝔹 (fun y => vecEuclideanNorm (f y) ^ 2))
      (fun x => Set.indicator_nonneg (fun y _ => sq_nonneg _) x)
      (fun x => Set.indicator_nonneg (fun y _ => sq_nonneg _) x)).1
      ⟨(integrable_indicator_iff ball_measurableSet).2 hint, hcpt,
        (memLp_indicator_iff_restrict ball_measurableSet).2 hhmem, hrh⟩
    rw [eLpNorm_indicator_eq_eLpNorm_restrict ball_measurableSet,
      eLpNorm_indicator_eq_eLpNorm_restrict ball_measurableSet,
      eLpNorm_sq_eq hwm hw0 (by linarith), eLpNorm_sq_eq hfm2 hf0 (by linarith),
      ofReal_two_mul_one_add] at hmain
    refine hgrad.trans ((le_of_sq_le_mul (b := C₁ * C₀) (K := C₁ * C₀) (by nlinarith)
      (by linarith) hmain).trans ?_)
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hKle) le_rfl

end Dirichlet

/-- Interior estimate and Dirichlet estimate for `p ≥ 2` (parts (i) and (ii) with `p ≥ 2` of
Theorem 4.4), assuming the Gehring lemma and the two reverse Hölder inequalities. -/
theorem meyers_interior_and_dirichlet_high
    (d : ℕ) (hGEH : GehringConclusion d) (hRHI : MeyersRHInterior d)
    (hRHB : MeyersRHBoundary d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d,
        AEMeasurable (fun x => a x i j)
          (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      (∀ (p : ℝ), 2 ≤ p → p ≤ 2 + c / Real.sqrt Λ →
        ∀ (f : Vec d → Vec d),
        (∀ i : Fin d,
          AEStronglyMeasurable (fun x => f x i)
            (volumeOn (euclideanBall (0 : Vec d) 1))) →
        MemLp (fun x => vecEuclideanNorm (f x)) (ENNReal.ofReal p)
          (volumeOn (euclideanBall (0 : Vec d) 1)) →
        ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
        IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u
            (0 : Vec d → ℝ) f →
          eLpMeanNormOn (euclideanBall (0 : Vec d) (1 / 2)) (ENNReal.ofReal p)
              (fun x => Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x)))) ≤
            ENNReal.ofReal C *
              (eLpMeanNormOn (euclideanBall (0 : Vec d) 1) 2
                  (fun x => Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x)))) +
                euclideanFieldELpMeanNormOn (euclideanBall (0 : Vec d) 1)
                  (ENNReal.ofReal p) f)) ∧
      (∀ (p : ℝ), 2 ≤ p → p ≤ 2 + c / Real.sqrt Λ →
        ∀ (f : Vec d → Vec d),
        (∀ i : Fin d,
          AEStronglyMeasurable (fun x => f x i)
            (volumeOn (euclideanBall (0 : Vec d) 1))) →
        MemLp (fun x => vecEuclideanNorm (f x)) 2
          (volumeOn (euclideanBall (0 : Vec d) 1)) →
        MemLp (fun x => vecEuclideanNorm (f x)) (ENNReal.ofReal p)
          (volumeOn (euclideanBall (0 : Vec d) 1)) →
        ∀ u : H10Function (euclideanBall (0 : Vec d) 1),
        IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1)
            u.toH1Function (0 : Vec d → ℝ) f →
          eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
              (volumeOn (euclideanBall (0 : Vec d) 1)) ≤
            ENNReal.ofReal C *
              eLpNorm (fun x => vecEuclideanNorm (f x)) (ENNReal.ofReal p)
                (volumeOn (euclideanBall (0 : Vec d) 1))) := by
  obtain ⟨C₁, hC₁, hG⟩ := hGEH
  obtain ⟨C₀I, hC₀I, hRI⟩ := hRHI
  obtain ⟨C₀B, hC₀B, hRB⟩ := hRHB
  set M : ℝ := max C₀I C₀B with hM
  have hMI : C₀I ≤ M := le_max_left _ _
  have hMB : C₀B ≤ M := le_max_right _ _
  have hM1 : 1 ≤ M := hC₀I.trans hMI
  have hC₁0 : 0 < C₁ := by linarith
  have hpow : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have hrange : ∀ {C₀ : ℝ}, 1 ≤ C₀ → C₀ ≤ M → ∀ (Λ p : ℝ),
      p ≤ 2 + (2 / (C₁ * M)) / Real.sqrt Λ → p ≤ 2 + (2 / (C₁ * C₀)) / Real.sqrt Λ := by
    intro C₀ hC₀ hle Λ p hp
    refine hp.trans ?_
    gcongr
  refine ⟨2 / (C₁ * M), C₁ * M * 2 ^ d, by positivity, by positivity, ?_⟩
  intro Λ a ha hell
  refine ⟨fun p hp hpΛ f hfm hfp u hsol => ?_, fun p hp hpΛ f hfm hf2 hfp u hsol => ?_⟩
  · refine (interior_clause hC₁ hC₀I hG hRI Λ a ha hell p hp (hrange hC₀I hMI Λ p hpΛ)
      f hfm hfp u hsol).trans ?_
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by
      have : C₁ * C₀I ≤ C₁ * M := by gcongr
      have h2 : 0 < 2 ^ d := by positivity
      nlinarith)) le_rfl
  · refine (dirichlet_clause hC₁ hC₀B hG hRB Λ a ha hell p hp (hrange hC₀B hMB Λ p hpΛ)
      f hfm hf2 hfp u hsol).trans ?_
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by
      have : C₁ * C₀B ≤ C₁ * M := by gcongr
      have h2 : 0 < 2 ^ d := by positivity
      nlinarith)) le_rfl

end MeyersAssembly

end PDE
