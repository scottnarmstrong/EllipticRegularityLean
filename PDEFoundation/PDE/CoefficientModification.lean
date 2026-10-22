module

public import PDEFoundation.PDE.WeakDivergenceForm

/-!
# Measurable representatives of elliptic coefficient fields

An entrywise almost-everywhere measurable coefficient field can be changed on
one measurable null set to obtain a globally measurable representative while
preserving its pointwise ellipticity on the domain.
-/

@[expose] public section

namespace PDE

open MeasureTheory

private theorem isEllipticMatrix_one_of_one_le {d : ℕ} {Λ : ℝ}
    (hΛ : 1 ≤ Λ) : IsEllipticMatrix 1 Λ (1 : Mat d) := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le (by norm_num) hΛ
  have hmul (ξ : Vec d) : matVecMul (1 : Mat d) ξ = ξ := by
    change (1 : Mat d).mulVec ξ = ξ
    exact Matrix.one_mulVec _
  refine ⟨by norm_num, hΛ, ?_, ?_⟩
  · intro ξ
    rw [hmul]
    change 1 * vecNormSq ξ ≤ vecNormSq ξ
    exact le_of_eq (one_mul _)
  · intro ξ
    have hinv : (1 : Mat d)⁻¹ = 1 := by simp
    have hΛinv : Λ⁻¹ ≤ 1 := (inv_le_one₀ hΛpos).2 hΛ
    rw [hinv, hmul]
    change Λ⁻¹ * vecNormSq ξ ≤ vecNormSq ξ
    calc
      Λ⁻¹ * vecNormSq ξ ≤ 1 * vecNormSq ξ :=
        mul_le_mul_of_nonneg_right hΛinv (vecNormSq_nonneg ξ)
      _ = vecNormSq ξ := one_mul _

/-- Modify an entrywise a.e. measurable coefficient field on a measurable
null set to obtain a measurable, pointwise elliptic representative. -/
theorem exists_isEllipticFieldOn_coeffAEEqOn
    {d : ℕ} {U : Set (Vec d)} {Λ : ℝ} {a : CoeffField d}
    (hU : MeasurableSet U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x)) :
    ∃ b : CoeffField d,
      IsEllipticFieldOn 1 Λ U b ∧ CoeffAEEqOn U a b := by
  classical
  let c : CoeffField d := fun x i j => (ha i j).mk (fun x => a x i j) x
  have hcMeas : ∀ i j, Measurable (fun x => c x i j) := by
    intro i j
    dsimp [c]
    exact (ha i j).measurable_mk
  have hcae : c =ᵐ[volumeOn U] a := by
    have hEntry : ∀ i j,
        (fun x => c x i j) =ᵐ[volumeOn U] (fun x => a x i j) := by
      intro i j
      dsimp [c]
      exact (ha i j).ae_eq_mk.symm
    filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun j => hEntry i j]
      with x hx
    ext i j
    exact hx i j
  have hNdiff : volumeOn U {x | c x ≠ a x} = 0 := by
    rw [← ae_iff]
    filter_upwards [hcae] with x hx
    simpa only [ne_eq, not_not] using hx
  let Nbad : Set (Vec d) := U ∩ {x | c x ≠ a x}
  have hNbad : volume Nbad = 0 := by
    have h := hNdiff
    rw [volumeOn, Measure.restrict_apply' hU] at h
    simpa [Nbad, Set.inter_comm] using h
  obtain ⟨N, hNbadSub, hNmeas, hNnull⟩ :=
    exists_measurable_superset_of_null hNbad
  let b : CoeffField d := fun x i j =>
    if x ∈ N then (1 : Mat d) i j else c x i j
  have hbMeas : ∀ i j, Measurable (fun x => b x i j) := by
    intro i j
    change Measurable (N.piecewise (fun _ => (1 : Mat d) i j)
      (fun x => c x i j))
    exact measurable_const.piecewise hNmeas (hcMeas i j)
  have hBae : CoeffAEEqOn U a b := by
    have hNzeroOnU : volumeOn U N = 0 := by
      rw [volumeOn, Measure.restrict_apply' hU]
      exact measure_mono_null Set.inter_subset_left hNnull
    have hNae : ∀ᵐ x ∂volumeOn U, x ∉ N := by
      rw [ae_iff]
      have hset : {x : Vec d | ¬ x ∉ N} = N := by
        ext x
        simp
      rw [hset]
      exact hNzeroOnU
    filter_upwards [hcae, hNae] with x hcx hxN
    simpa [b, hxN] using hcx.symm
  have hIdEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (1 : Mat d) := by
    intro x hx
    exact isEllipticMatrix_one_of_one_le (hEll x hx).2.1
  have hEllB : ∀ x ∈ U, IsEllipticMatrix 1 Λ (b x) := by
    intro x hx
    by_cases hxN : x ∈ N
    · simpa [b, hxN] using hIdEll x hx
    · have hcx : c x = a x := by
        by_contra hne
        apply hxN
        exact hNbadSub (by
          change x ∈ U ∧ c x ≠ a x
          exact ⟨hx, hne⟩)
      have hbxa : b x = a x := by
        ext i j
        simp [b, hxN, hcx]
      rw [hbxa]
      exact hEll x hx
  refine ⟨b, ?_, hBae⟩
  refine ⟨?_, hEllB⟩
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  have hbij : Measurable (fun x => b x i j) := hbMeas i j
  have hext : Measurable (U.piecewise (fun x => b x i j) fun _ => (0 : ℝ)) :=
    hbij.piecewise hU measurable_const
  convert hext using 1
  funext x
  by_cases hx : x ∈ U <;> simp [hx]

/-- A weak divergence-form solution is unchanged by an almost-everywhere
change of its coefficient field on the domain. -/
theorem IsWeakDivergenceFormSolutionOn.of_coeffAEEqOn
    {d : ℕ} {U : Set (Vec d)} {a b : CoeffField d}
    {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hsol : IsWeakDivergenceFormSolutionOn a U u f F)
    (hab : CoeffAEEqOn U a b) :
    IsWeakDivergenceFormSolutionOn b U u f F :=
  hsol.of_ae_eq_coeff hab

/-- Constructing a measurable elliptic representative also transports a
weak solution to that representative. -/
theorem exists_isEllipticFieldOn_and_weakSolutionOn_coeffAEEqOn
    {d : ℕ} {U : Set (Vec d)} {Λ : ℝ} {a : CoeffField d}
    (hU : MeasurableSet U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hsol : IsWeakDivergenceFormSolutionOn a U u f F) :
    ∃ b : CoeffField d,
      IsEllipticFieldOn 1 Λ U b ∧ CoeffAEEqOn U a b ∧
        IsWeakDivergenceFormSolutionOn b U u f F := by
  obtain ⟨b, hEllB, hEq⟩ := exists_isEllipticFieldOn_coeffAEEqOn hU ha hEll
  exact ⟨b, hEllB, hEq, hsol.of_coeffAEEqOn hEq⟩

/-- The coefficient energy integrals agree on every subdomain
when the coefficients agree almost everywhere on the full domain. -/
theorem setIntegral_coefficientEnergy_eq_of_coeffAEEqOn
    {d : ℕ} {U S : Set (Vec d)} {a b : CoeffField d}
    {u : H1Function U} (hab : CoeffAEEqOn U a b) (hSU : S ⊆ U) :
    ∫ x in S, vecDot (u.grad x) (matVecMul (a x) (u.grad x)) =
      ∫ x in S, vecDot (u.grad x) (matVecMul (b x) (u.grad x)) := by
  have habS : a =ᵐ[volumeOn S] b :=
    ae_restrict_of_ae_restrict_of_subset hSU hab
  have henergy :
      (fun x => vecDot (u.grad x) (matVecMul (a x) (u.grad x))) =ᵐ[volumeOn S]
        fun x => vecDot (u.grad x) (matVecMul (b x) (u.grad x)) := by
    filter_upwards [habS] with x hx
    rw [hx]
  exact integral_congr_ae henergy

end PDE
