module

public import EllipticRegularity.Parabolic.NashLower.Core
public import EllipticRegularity.Parabolic.NashLower.Constants
public import Ch5NashStatements.OnDiagLower
public import Ch5NashStatements.CauchyPositivity
public import Ch5NashStatements.CauchyExistence
public import Ch5NashStatements.CauchyUniqueness
public import Ch5NashStatements.NashUpper

/-!
# Assembly of the Nash-Aronson lower bound from the local Harnack inequality

Only proved statements are imported (`onDiagLower`, `cauchyPositivity`, `cauchyExistence`,
`cauchyUniqueness`, `nashAronsonUpper`); the local Harnack inequality enters through the internal
predicate `LocalHarnackAt`.

**Adaptation of the manuscript argument.**  Corollary 5.14 compares `u(τ)` with
`u(τ + θ)` but needs the solution up to time `τ + 5θ/4`.  The manuscript runs the chain to time
exactly `t`, which would need the solution beyond `t`, whereas the Cauchy solution lives only on
`[s,t]`.  (Chaining to every `t' < t` and passing to `t` by weak time continuity does not work with
uniform constants: the last Harnack step to time `t'` needs `t' + θ/4 ≤ t`.)  Here the coefficients
are extended by the identity for times `> t`, the Cauchy problem is solved on `[s, 2t - s]` for the
extended coefficients, and uniqueness (`cauchyUniqueness` on `[s,t]`) identifies the restriction
with the given solution.  The chain then ends exactly at time `t` inside the longer interval.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.Parabolic.NashLower

theorem lower_core {d : ℕ} {Lam H : ℝ} (hLam : 1 ≤ Lam) (hH2 : 2 ≤ H)
    (hH : LocalHarnackAt d Lam H) {C₁ : ℝ} (hC₁ : 0 < C₁)
    (hOD : ∀ (a : ParCoeffField d) (s t : ℝ), s < t →
      IsParabolicCoeff 1 Lam a univ (Icc s t) →
      ∀ (y : Vec d) (ε : ℝ) (f : Vec d → ℝ),
      Integrable f volume → MemLp f 2 volume → (∀ᵐ x : Vec d, 0 ≤ f x) → ∫ x, f x = 1 →
      (∀ᵐ x : Vec d, x ∉ euclideanBall y ε → f x = 0) → ε ^ 2 ≤ Lam * (t - s) →
      ∀ u : ParH1Function (univ : Set (Vec d)) (Icc s t), IsCauchySolution a s t f u →
        (1 / 2 : ℝ) ≤ ∫ x in euclideanBall y
            (C₁ * Real.sqrt (Lam * (t - s) * Real.log (Real.exp 1 * Lam))), u.toFun (x, t))
    (hUp : ∀ (a : ParCoeffField d) (s t : ℝ), s < t →
      IsParabolicCoeff 1 Lam a univ (Icc s t) → ∀ (f g : Vec d → ℝ),
      Integrable f volume → MemLp f 2 volume → Integrable g volume → MemLp g 2 volume →
      ∀ u : ParH1Function (univ : Set (Vec d)) (Icc s t), IsCauchySolution a s t f u →
        Integrable (fun x => g x * u.toFun (x, t)) volume)
    {a : ParCoeffField d} {s t : ℝ} (hst : s < t)
    (ha : IsParabolicCoeff 1 Lam a univ (Icc s t)) (x y : Vec d) (f g : Vec d → ℝ)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume) (hg1 : Integrable g volume)
    (hg2 : MemLp g 2 volume) (hf0 : ∀ᵐ z : Vec d, 0 ≤ f z) (hg0 : ∀ᵐ z : Vec d, 0 ≤ g z)
    (hfs : ∀ᵐ z : Vec d, z ∉ euclideanBall y (Real.sqrt (t - s) / 8) → f z = 0)
    (hgs : ∀ᵐ z : Vec d, z ∉ euclideanBall x (Real.sqrt (t - s) / 8) → g z = 0)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s t)) (hu : IsCauchySolution a s t f u)
    (m : ℝ) (hm : 0 < m) (hmf : ∫ z, f z = m) :
    ∃ N : ℕ, (N : ℝ) ≤ 22 * (1 + (C₁ * Real.sqrt (Lam * Real.log (Real.exp 1 * Lam) / 4)) ^ 2 +
        euclideanSqDist x y / (t - s)) + 1 ∧
      (1 / (4 * (volume (euclideanBall y
        ((C₁ * Real.sqrt (Lam * Real.log (Real.exp 1 * Lam) / 4)) *
          Real.sqrt (t - s)))).toReal)) / H ^ N * (m * ∫ z, g z) ≤
        ∫ z, g z * u.toFun (z, t) := by
  have hh : 0 < t - s := sub_pos.2 hst
  have hL : 0 < Real.log (Real.exp 1 * Lam) := by
    apply Real.log_pos
    have : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.2 one_pos
    nlinarith
  set R₁ : ℝ := C₁ * Real.sqrt (Lam * Real.log (Real.exp 1 * Lam) / 4) with hR₁def
  have hR₁ : 0 < R₁ := by
    rw [hR₁def]; exact mul_pos hC₁ (Real.sqrt_pos.2 (by positivity))
  have hLam0 : 0 < Lam := by linarith
  -- the normalized datum and solution
  set f' : Vec d → ℝ := fun z => (1 / m) * f z with hf'def
  have hf'1 : Integrable f' volume := hf1.const_mul _
  have hf'2 : MemLp f' 2 volume := hf2.const_mul _
  have hf'0 : ∀ᵐ z : Vec d, 0 ≤ f' z := by
    filter_upwards [hf0] with z hz
    exact mul_nonneg (by positivity) hz
  have hf'int : ∫ z, f' z = 1 := by
    rw [hf'def, integral_const_mul, hmf]; field_simp
  have hf's : ∀ᵐ z : Vec d, z ∉ euclideanBall y (Real.sqrt (t - s) / 8) → f' z = 0 := by
    filter_upwards [hfs] with z hz hzn
    simp [hf'def, hz hzn]
  have hu' : IsCauchySolution a s t f' (smulParH1 (1 / m) u) := isCauchySolution_smul _ hu
  -- extension of the coefficients beyond `t`
  set T : ℝ := t + (t - s) with hTdef
  have hsT : s < T := by rw [hTdef]; linarith
  have htT : t ≤ T := by rw [hTdef]; linarith
  have hã : IsParabolicCoeff 1 Lam (extCoeff a t) univ (Icc s T) := isParabolicCoeff_ext hLam ha
  obtain ⟨w, hw⟩ := PDE.cauchyExistence d 1 Lam (extCoeff a t) s T hsT hã f' hf'2
  have hwr := isCauchySolution_of_ext htT hw
  have huniq := PDE.cauchyUniqueness d 1 Lam a s t hst ha f' hf'2 _ _ hwr hu'
  have hwt : ∀ᵐ z : Vec d, w.toFun (z, t) = (1 / m) * u.toFun (z, t) :=
    huniq.1 t (right_mem_Icc.2 hst.le)
  have hwpos : ∀ τ ∈ Icc s T, ∀ᵐ z : Vec d, 0 ≤ w.toFun (z, τ) := fun τ hτ =>
    PDE.cauchyPositivity d 1 Lam (extCoeff a t) s T hsT hã f' hf'2 hf'0 w hw τ hτ
  -- mass at time `s + (t-s)/4`
  have hq4 : s + (t - s) / 4 ≤ T := by rw [hTdef]; linarith
  have hcoef_m : IsParabolicCoeff 1 Lam (extCoeff a t) univ (Icc s (s + (t - s) / 4)) :=
    isParabolicCoeff_mono hã (subset_refl _) (Icc_subset_Icc_right hq4)
  have hcauchy_m : IsCauchySolution (extCoeff a t) s (s + (t - s) / 4) f'
      (restrictParH1 (subset_refl _) (Icc_subset_Icc_right hq4) w) :=
    ⟨isParabolicWeakSolution_restrict _ _ hw.1, hw.2⟩
  have hε : (Real.sqrt (t - s) / 8) ^ 2 ≤ Lam * (s + (t - s) / 4 - s) := by
    rw [div_pow, Real.sq_sqrt hh.le]
    nlinarith
  have hmass0 := hOD (extCoeff a t) s (s + (t - s) / 4) (by linarith) hcoef_m y
    (Real.sqrt (t - s) / 8) f' hf'1 hf'2 hf'0 hf'int hf's hε _ hcauchy_m
  have hrad : C₁ * Real.sqrt (Lam * (s + (t - s) / 4 - s) * Real.log (Real.exp 1 * Lam)) =
      R₁ * Real.sqrt (t - s) := by
    have e : Lam * (s + (t - s) / 4 - s) * Real.log (Real.exp 1 * Lam) =
        (Lam * Real.log (Real.exp 1 * Lam) / 4) * (t - s) := by ring
    rw [e, Real.sqrt_mul (by positivity), hR₁def]; ring
  rw [hrad] at hmass0
  obtain ⟨N, hN, hae⟩ := chain_to_final_time hH2 hH hst (le_of_eq hTdef.symm) hã w hw.1 hwpos x y hR₁
    hmass0
  refine ⟨N, hN, ?_⟩
  set mstar : ℝ := (1 / (4 * (volume (euclideanBall y (R₁ * Real.sqrt (t - s)))).toReal)) / H ^ N
    with hmstar
  have hae' : ∀ᵐ z : Vec d, z ∈ euclideanBall x (Real.sqrt (t - s) / 8) →
      mstar ≤ w.toFun (z, t) :=
    (ae_restrict_iff' (measurableSet_euclideanBall _ _)).1 hae
  have hint := hUp a s t hst ha f g hf1 hf2 hg1 hg2 u hu
  have hclaim : ∀ᵐ z : Vec d, g z * (m * mstar) ≤ g z * u.toFun (z, t) := by
    filter_upwards [hae', hwt, hg0, hgs] with z h1 h2 h3 h4
    by_cases hz : z ∈ euclideanBall x (Real.sqrt (t - s) / 8)
    · apply mul_le_mul_of_nonneg_left _ h3
      have h5 := h1 hz
      have : u.toFun (z, t) = m * w.toFun (z, t) := by rw [h2]; field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left h5 hm.le
    · simp [h4 hz]
  have hmono := integral_mono_ae (hg1.mul_const (m * mstar)) hint hclaim
  rw [integral_mul_const] at hmono
  calc mstar * (m * ∫ z, g z) = (∫ z, g z) * (m * mstar) := by ring
    _ ≤ _ := hmono

end PDE.Parabolic.NashLower
