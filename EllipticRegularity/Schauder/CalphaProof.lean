module

public import EllipticRegularity.Schauder.GradientLp
public import EllipticRegularity.Schauder.OneDimensional
public import PDEFoundation.Measure.NormalizedLp
public import PDEFoundation.Regularity.InteriorCampanatoHolder

/-!
# The quantitative `C^{0,alpha}` Schauder estimate

The target is manuscript Proposition 3.1, with its corrected
`C(d)/alpha` prefactor and the original coefficient smallness threshold.
-/

@[expose] public section

namespace PDE.SchauderCalphaProof

open MeasureTheory

noncomputable section

private theorem schauder_threshold_le_half
    {d : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (2 : ℝ) ^ (-3 - (d : ℝ) / 2) * (1 - α) ≤ 1 / 2 := by
  have hpow : (2 : ℝ) ^ (-3 - (d : ℝ) / 2) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d; linarith)
  norm_num at hpow
  have hgap : 0 ≤ 1 - α := by linarith
  calc
    _ ≤ (1 / 2 : ℝ) * (1 - α) := mul_le_mul_of_nonneg_right hpow hgap
    _ ≤ 1 / 2 := by linarith

private theorem holderRepresentative_mono_const
    {d : ℕ} {U : Set (Vec d)} {u : Vec d → ℝ} {α K L : ℝ}
    (h : HasEuclideanHolderRepresentativeOn U u α K) (hKL : K ≤ L) :
    HasEuclideanHolderRepresentativeOn U u α L := by
  obtain ⟨v, hv, hbound⟩ := h
  exact ⟨v, hv, hbound.mono_const hKL⟩

/-- Proposition 3.1 in dimension one, including its exact
coefficient threshold and its corrected visible endpoint dependence. -/
theorem schauderCalpha_oneDimensional
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {a : CoeffField 1}
    (u : H1Function (euclideanBall (0 : Vec 1) 1)) {F : Vec 1 → Vec 1}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec 1) 1)))
    (hclose : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec 1) 1),
      IsMatrixPerturbationLE ((2 : ℝ) ^ (-3 - (1 : ℝ) / 2) * (1 - α)) (a x) 1)
    (hFcoord : ∀ i : Fin 1, AEStronglyMeasurable (fun x => F x i)
      (volumeOn (euclideanBall (0 : Vec 1) 1)))
    (hF : MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal (1 / (1 - α)))
      (volumeOn (euclideanBall (0 : Vec 1) 1)))
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec 1) 1) u 0 F) :
    HasEuclideanHolderRepresentativeOn (euclideanBall (0 : Vec 1) (1 / 2)) u.toFun α
      ((8 / α) * (Real.sqrt (∫ x in euclideanBall (0 : Vec 1) 1, vecNormSq (u.grad x)) +
        euclideanFieldLpNormOn (euclideanBall (0 : Vec 1) 1)
          (ENNReal.ofReal (1 / (1 - α))) F hF / (1 - α))) := by
  have h := schauder_oneDimensional hα0 hα1
    (by simpa only [Nat.cast_one] using schauder_threshold_le_half (d := 1) hα0 hα1)
    u ha hclose (hFcoord 0) hF hsol
  apply holderRepresentative_mono_const h
  let N := euclideanFieldLpNormOn (euclideanBall (0 : Vec 1) 1)
    (ENNReal.ofReal (1 / (1 - α))) F hF
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hNgap : N ≤ N / (1 - α) := by
    apply (le_div_iff₀ (sub_pos.mpr hα1)).mpr
    exact mul_le_of_le_one_right hN (by linarith)
  have hcoef : (8 : ℝ) ≤ 8 / α := by
    apply (le_div_iff₀ hα0).mpr
    linarith
  change 8 * (Real.sqrt (∫ x in euclideanBall (0 : Vec 1) 1, vecNormSq (u.grad x)) + N) ≤ _
  calc
    _ ≤ 8 * (Real.sqrt (∫ x in euclideanBall (0 : Vec 1) 1, vecNormSq (u.grad x)) +
        N / (1 - α)) := mul_le_mul_of_nonneg_left (add_le_add le_rfl hNgap) (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef
      (add_nonneg (Real.sqrt_nonneg _) (div_nonneg hN (by linarith)))

/-- Manuscript Proposition 3.1, with corrected alpha dependence.

The constant is chosen before the exponent, coefficient field, solution, and
forcing. Matrix closeness is measured in the Euclidean operator norm, the
gradient energy is Euclidean, and the conclusion supplies an almost everywhere
equal Hölder representative on the native round half ball. The full range
`0 < alpha < 1` is covered in every positive dimension. -/
theorem result {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ}, 0 < α → α < 1 →
      ∀ {a : CoeffField d} (u : H1Function (euclideanBall (0 : Vec d) 1))
        {F : Vec d → Vec d},
      (∀ i j, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
        IsMatrixPerturbationLE ((2 : ℝ) ^ (-3 - (d : ℝ) / 2) * (1 - α)) (a x) 1) →
      (∀ i : Fin d, AEStronglyMeasurable (fun x => F x i)
        (volumeOn (euclideanBall (0 : Vec d) 1))) →
      ∀ hF : MemLp (fun x => vecEuclideanNorm (F x))
        (ENNReal.ofReal ((d : ℝ) / (1 - α))) (volumeOn (euclideanBall (0 : Vec d) 1)),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u 0 F →
      HasEuclideanHolderRepresentativeOn (euclideanBall (0 : Vec d) (1 / 2)) u.toFun α
        ((C / α) * (Real.sqrt (∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (u.grad x)) +
          euclideanFieldLpNormOn (euclideanBall (0 : Vec d) 1)
            (ENNReal.ofReal ((d : ℝ) / (1 - α))) F hF / (1 - α))) := by
  by_cases hd1 : d = 1
  · subst d
    refine ⟨8, by norm_num, ?_⟩
    intro α hα0 hα1 a u F ha hclose hFcoord hF hsol
    simp only [Nat.cast_one] at hclose hF ⊢
    exact schauderCalpha_oneDimensional hα0 hα1 u ha hclose hFcoord hF hsol
  · have hd2 : 2 ≤ d := by omega
    obtain ⟨Cg, hCg, hgradient⟩ := exists_schauder_interior_gradient_constant hd2
    obtain ⟨Cc, hCc, hcampanato⟩ := exists_interiorCampanato_holder_constant hd
    refine ⟨Cc * Cg, mul_pos hCc hCg, ?_⟩
    intro α hα0 hα1 a u F ha hclose hFcoord hF hsol
    let N := euclideanFieldLpNormOn (euclideanBall (0 : Vec d) 1)
      (ENNReal.ofReal ((d : ℝ) / (1 - α))) F hF
    let K := Cg * (Real.sqrt (∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (u.grad x)) +
      N / (1 - α))
    have hN : 0 ≤ N := ENNReal.toReal_nonneg
    have hK : 0 ≤ K := mul_nonneg hCg.le
      (add_nonneg (Real.sqrt_nonneg _) (div_nonneg hN (by linarith)))
    have hscale := hgradient hα0 hα1 u ha hclose hFcoord hF hsol
    have hrep := hcampanato hα0 hα1 hK u hscale
    have heq : Cc * K / α = (Cc * Cg / α) *
        (Real.sqrt (∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (u.grad x)) +
          N / (1 - α)) := by
      dsimp only [K]
      ring
    rw [heq] at hrep
    exact hrep

end

end PDE.SchauderCalphaProof
