module

public import PDEFoundation.Sobolev.Ch4.ChainRule
public import PDEFoundation.PDE.DGNM.Composites
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The composites `log u`, `u⁻¹`, `u ^ s` on bounded open sets

Open-set versions of `PDE.DGNM.compOfLowerBound`, `compOfBounds`, `logOfLowerBound`,
`invOfLowerBound`, `rpowOfLowerBound`, `rpowOfBounds`: same values and gradient formulas, on an
arbitrary bounded open set `U` (via `compOpen`).
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory

namespace PDE.Ch4Infra

variable {d : ℕ} {U : Set (Vec d)}

/-- `G(u)` for `u ≥ δ > 0` a.e., when `G` has a continuous derivative `G'` on
`(0, ∞)` bounded by `B` on `[δ/2, ∞)`. Value `G (u x)`, gradient
`G' (u x) • ∇u x`. -/
noncomputable def compOfLowerBoundOpen (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H1Function U) {δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x) (G G' : ℝ → ℝ)
    (hGd : ∀ t, 0 < t → HasDerivAt G (G' t) t)
    (hG'c : ContinuousOn G' (Set.Ioi 0)) {B : ℝ}
    (hB : ∀ t, δ / 2 ≤ t → |G' t| ≤ B) : H1Function U :=
  have hTpos : ∀ t, 0 < DGNM.lowerClamp δ t := fun t =>
    lt_of_lt_of_le (by positivity) (DGNM.half_le_lowerClamp hδ t)
  have hext := DGNM.comp_clamp_contDiff hGd hG'c (DGNM.lowerClamp_contDiff δ) hTpos
  have hbound : ∀ t, |deriv (G ∘ DGNM.lowerClamp δ) t| ≤ B := fun t => by
    rw [hext.2 t, abs_mul]
    have h1 := hB _ (DGNM.half_le_lowerClamp hδ t)
    have h2 := DGNM.deriv_lowerClamp_mem δ t
    rw [abs_of_nonneg h2.1]
    calc |G' (DGNM.lowerClamp δ t)| * deriv (DGNM.lowerClamp δ) t ≤ B * 1 :=
          mul_le_mul h1 h2.2 h2.1 ((abs_nonneg _).trans h1)
      _ = B := mul_one B
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hbound 0)
  let v := compOpen hU hfin u hext.1 hB0 hbound
  DGNM.H1ofAEEq v (fun x => G (u x))
    (hu.mono fun x hx => by
      change G (u x) = G (DGNM.lowerClamp δ (u x))
      rw [DGNM.lowerClamp_eq hδ (by linarith)])
    (fun x => G' (u x) • u.grad x)
    (fun i => hu.mono fun x hx => by
      change G' (u x) * u.grad x i = deriv (G ∘ DGNM.lowerClamp δ) (u x) * u.grad x i
      rw [hext.2, DGNM.lowerClamp_eq hδ (by linarith), DGNM.deriv_lowerClamp_eq_one hδ (by linarith),
        mul_one])

@[simp]
theorem compOfLowerBoundOpen_toFun (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H1Function U) {δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x) (G G' : ℝ → ℝ)
    (hGd : ∀ t, 0 < t → HasDerivAt G (G' t) t)
    (hG'c : ContinuousOn G' (Set.Ioi 0)) {B : ℝ}
    (hB : ∀ t, δ / 2 ≤ t → |G' t| ≤ B) :
    (compOfLowerBoundOpen hU hfin u hδ hu G G' hGd hG'c hB).toFun = fun x => G (u x) :=
  rfl

@[simp]
theorem compOfLowerBoundOpen_grad (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H1Function U) {δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x) (G G' : ℝ → ℝ)
    (hGd : ∀ t, 0 < t → HasDerivAt G (G' t) t)
    (hG'c : ContinuousOn G' (Set.Ioi 0)) {B : ℝ}
    (hB : ∀ t, δ / 2 ≤ t → |G' t| ≤ B) :
    (compOfLowerBoundOpen hU hfin u hδ hu G G' hGd hG'c hB).grad =
      fun x => G' (u x) • u.grad x :=
  rfl

/-! ### Composition for `δ ≤ u ≤ M` -/

/-- `G(u)` for `δ ≤ u ≤ M` a.e. (`0 < δ ≤ M`), when `G` has a continuous
derivative `G'` on `(0, ∞)`. Value `G (u x)`, gradient `G' (u x) • ∇u x`. -/
noncomputable def compOfBoundsOpen (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H1Function U) {δ M : ℝ} (hδ : 0 < δ) (hδM : δ ≤ M)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x ∧ u x ≤ M) (G G' : ℝ → ℝ)
    (hGd : ∀ t, 0 < t → HasDerivAt G (G' t) t)
    (hG'c : ContinuousOn G' (Set.Ioi 0)) : H1Function U :=
  have hT : ContDiff ℝ 1 (fun t => DGNM.upperClamp M (DGNM.lowerClamp δ t)) := by
    rw [contDiff_one_iff_deriv]
    have hd : ∀ t, HasDerivAt (fun t => DGNM.upperClamp M (DGNM.lowerClamp δ t))
        (deriv (DGNM.upperClamp M) (DGNM.lowerClamp δ t) * deriv (DGNM.lowerClamp δ) t) t := fun t =>
      ((DGNM.upperClamp_hasDerivAt M _).congr_deriv DGNM.deriv_upperClamp.symm).comp t
        ((DGNM.lowerClamp_hasDerivAt δ t).congr_deriv DGNM.deriv_lowerClamp.symm)
    refine ⟨fun t => (hd t).differentiableAt, ?_⟩
    rw [show deriv (fun t => DGNM.upperClamp M (DGNM.lowerClamp δ t)) = fun t =>
      deriv (DGNM.upperClamp M) (DGNM.lowerClamp δ t) * deriv (DGNM.lowerClamp δ) t from
      funext fun t => (hd t).deriv]
    have hcu : Continuous (deriv (DGNM.upperClamp M)) := by
      rw [show deriv (DGNM.upperClamp M) = fun t => 1 - smoothPositivePartStep 0 1 (t - (M + 1))
        from funext fun t => DGNM.deriv_upperClamp]
      exact continuous_const.sub ((smoothPositivePartStep_continuous 0 1).comp
        (continuous_id.sub continuous_const))
    exact (hcu.comp (DGNM.lowerClamp_contDiff δ).continuous).mul
      ((DGNM.lowerClamp_contDiff δ).continuous_deriv le_rfl)
  have hTrange : ∀ t, δ / 2 ≤ DGNM.upperClamp M (DGNM.lowerClamp δ t) ∧
      DGNM.upperClamp M (DGNM.lowerClamp δ t) ≤ M + 3 := fun t =>
    ⟨le_trans (le_min (DGNM.half_le_lowerClamp hδ t) (by linarith))
      (DGNM.min_le_upperClamp M _), DGNM.upperClamp_le M _⟩
  have hTpos : ∀ t, 0 < DGNM.upperClamp M (DGNM.lowerClamp δ t) := fun t =>
    lt_of_lt_of_le (by positivity) (hTrange t).1
  have hext := DGNM.comp_clamp_contDiff hGd hG'c hT hTpos
  have hBex : ∃ B, ∀ t ∈ Set.Icc (δ / 2) (M + 3), ‖G' t‖ ≤ B :=
    isCompact_Icc.exists_bound_of_continuousOn
      (hG'c.mono fun t ht => lt_of_lt_of_le (by positivity) ht.1)
  have hbound : ∀ t, |deriv (G ∘ fun t => DGNM.upperClamp M (DGNM.lowerClamp δ t)) t| ≤
      hBex.choose := fun t => by
    rw [hext.2 t, abs_mul]
    have h1 : |G' (DGNM.upperClamp M (DGNM.lowerClamp δ t))| ≤ hBex.choose :=
      hBex.choose_spec _ (hTrange t)
    have hdT : deriv (fun t => DGNM.upperClamp M (DGNM.lowerClamp δ t)) t =
        deriv (DGNM.upperClamp M) (DGNM.lowerClamp δ t) * deriv (DGNM.lowerClamp δ) t :=
      (((DGNM.upperClamp_hasDerivAt M _).congr_deriv DGNM.deriv_upperClamp.symm).comp t
        ((DGNM.lowerClamp_hasDerivAt δ t).congr_deriv DGNM.deriv_lowerClamp.symm)).deriv
    have hu1 := DGNM.deriv_upperClamp_mem M (DGNM.lowerClamp δ t)
    have hl1 := DGNM.deriv_lowerClamp_mem δ t
    have h2 : |deriv (fun t => DGNM.upperClamp M (DGNM.lowerClamp δ t)) t| ≤ 1 := by
      rw [hdT, abs_of_nonneg (mul_nonneg hu1.1 hl1.1)]
      nlinarith
    calc |G' (DGNM.upperClamp M (DGNM.lowerClamp δ t))| *
          |deriv (fun t => DGNM.upperClamp M (DGNM.lowerClamp δ t)) t| ≤ hBex.choose * 1 :=
          mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
      _ = hBex.choose := mul_one _
  have hB0 : 0 ≤ hBex.choose := (abs_nonneg _).trans (hbound 0)
  let v := compOpen hU hfin u hext.1 hB0 hbound
  DGNM.H1ofAEEq v (fun x => G (u x))
    (hu.mono fun x hx => by
      change G (u x) = G (DGNM.upperClamp M (DGNM.lowerClamp δ (u x)))
      rw [DGNM.lowerClamp_eq hδ (by linarith [hx.1]), DGNM.upperClamp_eq (by linarith [hx.2])])
    (fun x => G' (u x) • u.grad x)
    (fun i => hu.mono fun x hx => by
      change G' (u x) * u.grad x i =
        deriv (G ∘ fun t => DGNM.upperClamp M (DGNM.lowerClamp δ t)) (u x) * u.grad x i
      have hdT : deriv (fun t => DGNM.upperClamp M (DGNM.lowerClamp δ t)) (u x) =
          deriv (DGNM.upperClamp M) (DGNM.lowerClamp δ (u x)) * deriv (DGNM.lowerClamp δ) (u x) :=
        (((DGNM.upperClamp_hasDerivAt M _).congr_deriv DGNM.deriv_upperClamp.symm).comp (u x)
          ((DGNM.lowerClamp_hasDerivAt δ (u x)).congr_deriv DGNM.deriv_lowerClamp.symm)).deriv
      rw [hext.2, hdT, DGNM.lowerClamp_eq hδ (by linarith [hx.1]),
        DGNM.upperClamp_eq (by linarith [hx.2]),
        DGNM.deriv_lowerClamp_eq_one hδ (by linarith [hx.1]),
        DGNM.deriv_upperClamp_eq_one (by linarith [hx.2]), mul_one, mul_one])

@[simp]
theorem compOfBoundsOpen_toFun (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H1Function U) {δ M : ℝ} (hδ : 0 < δ) (hδM : δ ≤ M)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x ∧ u x ≤ M) (G G' : ℝ → ℝ)
    (hGd : ∀ t, 0 < t → HasDerivAt G (G' t) t)
    (hG'c : ContinuousOn G' (Set.Ioi 0)) :
    (compOfBoundsOpen hU hfin u hδ hδM hu G G' hGd hG'c).toFun = fun x => G (u x) :=
  rfl

@[simp]
theorem compOfBoundsOpen_grad (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H1Function U) {δ M : ℝ} (hδ : 0 < δ) (hδM : δ ≤ M)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x ∧ u x ≤ M) (G G' : ℝ → ℝ)
    (hGd : ∀ t, 0 < t → HasDerivAt G (G' t) t)
    (hG'c : ContinuousOn G' (Set.Ioi 0)) :
    (compOfBoundsOpen hU hfin u hδ hδM hu G G' hGd hG'c).grad =
      fun x => G' (u x) • u.grad x :=
  rfl


private theorem inv_le_two_div' {δ t : ℝ} (hδ : 0 < δ) (ht : δ / 2 ≤ t) :
    t⁻¹ ≤ 2 / δ := by
  have htpos : 0 < t := lt_of_lt_of_le (by positivity) ht
  rw [inv_le_comm₀ htpos (by positivity)]
  field_simp
  linarith

/-- `log u` for `u ≥ δ > 0` a.e.: value `Real.log (u x)`, gradient
`(u x)⁻¹ • ∇u x`. -/
noncomputable def logOfLowerBoundOpen (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H1Function U) {δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x) : H1Function U :=
  compOfLowerBoundOpen hU hfin u hδ hu Real.log (fun t => t⁻¹)
    (fun _ ht => Real.hasDerivAt_log (ne_of_gt ht))
    (continuousOn_inv₀.mono fun _ ht => ne_of_gt ht)
    (B := 2 / δ) (fun t ht => by
      have htpos : 0 < t := lt_of_lt_of_le (by positivity) ht
      rw [abs_of_pos (inv_pos.mpr htpos)]
      exact inv_le_two_div' hδ ht)

@[simp]
theorem logOfLowerBoundOpen_toFun (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H1Function U) {δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x) :
    (logOfLowerBoundOpen hU hfin u hδ hu).toFun = fun x => Real.log (u x) :=
  rfl

@[simp]
theorem logOfLowerBoundOpen_grad (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H1Function U) {δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x) :
    (logOfLowerBoundOpen hU hfin u hδ hu).grad = fun x => (u x)⁻¹ • u.grad x :=
  rfl

/-- `u⁻¹` for `u ≥ δ > 0` a.e.: value `(u x)⁻¹`, gradient
`(-((u x) ^ 2)⁻¹) • ∇u x`. -/
noncomputable def invOfLowerBoundOpen (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H1Function U) {δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x) : H1Function U :=
  compOfLowerBoundOpen hU hfin u hδ hu (fun t => t⁻¹) (fun t => -(t ^ 2)⁻¹)
    (fun _ ht => hasDerivAt_inv (ne_of_gt ht))
    (((continuousOn_pow 2).inv₀ fun _ ht => pow_ne_zero 2 (ne_of_gt ht)).neg)
    (B := (2 / δ) ^ 2) (fun t ht => by
      have htpos : 0 < t := lt_of_lt_of_le (by positivity) ht
      rw [abs_neg, abs_of_pos (inv_pos.mpr (pow_pos htpos 2)), ← inv_pow]
      exact pow_le_pow_left₀ (inv_nonneg.mpr htpos.le) (inv_le_two_div' hδ ht) 2)

@[simp]
theorem invOfLowerBoundOpen_toFun (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H1Function U) {δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x) :
    (invOfLowerBoundOpen hU hfin u hδ hu).toFun = fun x => (u x)⁻¹ :=
  rfl

@[simp]
theorem invOfLowerBoundOpen_grad (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H1Function U) {δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x) :
    (invOfLowerBoundOpen hU hfin u hδ hu).grad = fun x => (-((u x) ^ 2)⁻¹) • u.grad x :=
  rfl

theorem rpow_hasDerivAt' (s t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => t ^ s) (s * t ^ (s - 1)) t :=
  Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht))

theorem rpow_deriv_continuousOn' (s : ℝ) :
    ContinuousOn (fun t : ℝ => s * t ^ (s - 1)) (Set.Ioi 0) :=
  continuousOn_const.mul
    (continuousOn_id.rpow_const fun _ ht => Or.inl (ne_of_gt ht))

/-- `u ^ s` for `u ≥ δ > 0` a.e. and `s ≤ 1`: value `u x ^ s`, gradient
`(s * u x ^ (s - 1)) • ∇u x`. -/
noncomputable def rpowOfLowerBoundOpen (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H1Function U) {δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x) (s : ℝ) (hs : s ≤ 1) : H1Function U :=
  compOfLowerBoundOpen hU hfin u hδ hu (fun t => t ^ s) (fun t => s * t ^ (s - 1))
    (rpow_hasDerivAt' s) (rpow_deriv_continuousOn' s)
    (B := |s| * (δ / 2) ^ (s - 1)) (fun t ht => by
      have htpos : 0 < t := lt_of_lt_of_le (by positivity) ht
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos htpos _)]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by positivity) ht (by linarith)) (abs_nonneg s))

@[simp]
theorem rpowOfLowerBoundOpen_toFun (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H1Function U) {δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x) (s : ℝ) (hs : s ≤ 1) :
    (rpowOfLowerBoundOpen hU hfin u hδ hu s hs).toFun = fun x => u x ^ s :=
  rfl

@[simp]
theorem rpowOfLowerBoundOpen_grad (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H1Function U) {δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x) (s : ℝ) (hs : s ≤ 1) :
    (rpowOfLowerBoundOpen hU hfin u hδ hu s hs).grad =
      fun x => (s * u x ^ (s - 1)) • u.grad x :=
  rfl

/-- `u ^ s` for `δ ≤ u ≤ M` a.e. (`0 < δ ≤ M`) and any real `s`: value
`u x ^ s`, gradient `(s * u x ^ (s - 1)) • ∇u x`. -/
noncomputable def rpowOfBoundsOpen (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H1Function U) {δ M : ℝ} (hδ : 0 < δ) (hδM : δ ≤ M)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x ∧ u x ≤ M) (s : ℝ) : H1Function U :=
  compOfBoundsOpen hU hfin u hδ hδM hu (fun t => t ^ s) (fun t => s * t ^ (s - 1))
    (rpow_hasDerivAt' s) (rpow_deriv_continuousOn' s)

@[simp]
theorem rpowOfBoundsOpen_toFun (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H1Function U) {δ M : ℝ} (hδ : 0 < δ) (hδM : δ ≤ M)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x ∧ u x ≤ M) (s : ℝ) :
    (rpowOfBoundsOpen hU hfin u hδ hδM hu s).toFun = fun x => u x ^ s :=
  rfl

@[simp]
theorem rpowOfBoundsOpen_grad (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H1Function U) {δ M : ℝ} (hδ : 0 < δ) (hδM : δ ≤ M)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x ∧ u x ≤ M) (s : ℝ) :
    (rpowOfBoundsOpen hU hfin u hδ hδM hu s).grad =
      fun x => (s * u x ^ (s - 1)) • u.grad x :=
  rfl


end PDE.Ch4Infra
