module

public import PDEFoundation.Sobolev.H1.Composition
public import PDEFoundation.Sobolev.W1p.Truncation

/-!
# Chain rules `G(u)` for `u` bounded below (and above)

The repository chain rule `H1Function.compContDiffOfDerivBounded` needs a
globally `C¹` function with bounded derivative. For the De Giorgi-Nash-Moser
tests we need `G(u)` for functions `G` which are only `C¹` on `(0, ∞)`
(`log t`, `t⁻¹`, `t ^ s`), applied to `u ≥ δ > 0` a.e. (and `u ≤ M` a.e. when
`G'` is unbounded at infinity).

We compose `G` with a smooth clamp `T` that is the identity on `[δ, M]`
(resp. `[δ, ∞)`), takes values in `[δ/2, M+3]` (resp. `[δ/2, ∞)`), and has
`0 ≤ T' ≤ 1`; then `G ∘ T` is globally `C¹` with bounded derivative, and we
replace the value and gradient representatives by the a.e.-equal literal
`G (u x)` and `G' (u x) • ∇u x` (`H1ofAEEq`).
-/

@[expose] public section

namespace PDE

namespace DGNM

open MeasureTheory

variable {d : ℕ} {U : Set (Vec d)}

/-! ### Almost-everywhere replacement of representatives -/

/-- Replace the value and gradient representatives of an `H1Function` by
a.e.-equal functions. -/
def H1ofAEEq (v : H1Function U) (f : Vec d → ℝ)
    (hf : f =ᵐ[volumeOn U] v.toFun) (g : Vec d → Vec d)
    (hg : ∀ i, (fun x => g x i) =ᵐ[volumeOn U] fun x => v.grad x i) :
    H1Function U where
  toFun := f
  grad := g
  memL2 := v.memL2.ae_eq hf.symm
  gradMemL2 := fun i => (v.gradMemL2 i).ae_eq (hg i).symm
  hasWeakGradient := by
    intro i φ hφ hφc hφU
    have h := v.hasWeakGradient i φ hφ hφc hφU
    have h1 : ∫ x in U, f x * (fderiv ℝ φ x) (basisVec i) =
        ∫ x in U, v.toFun x * (fderiv ℝ φ x) (basisVec i) := by
      refine integral_congr_ae (hf.mono fun x hx => ?_)
      show f x * (fderiv ℝ φ x) (basisVec i) = v.toFun x * (fderiv ℝ φ x) (basisVec i)
      rw [hx]
    have h2 : ∫ x in U, v.grad x i * φ x = ∫ x in U, g x i * φ x := by
      refine integral_congr_ae ((hg i).mono fun x hx => ?_)
      show v.grad x i * φ x = g x i * φ x
      rw [show g x i = v.grad x i from hx]
    rw [h1, h]
    exact congrArg Neg.neg h2

@[simp]
theorem H1ofAEEq_toFun (v : H1Function U) (f : Vec d → ℝ)
    (hf : f =ᵐ[volumeOn U] v.toFun) (g : Vec d → Vec d)
    (hg : ∀ i, (fun x => g x i) =ᵐ[volumeOn U] fun x => v.grad x i) :
    (H1ofAEEq v f hf g hg).toFun = f :=
  rfl

@[simp]
theorem H1ofAEEq_grad (v : H1Function U) (f : Vec d → ℝ)
    (hf : f =ᵐ[volumeOn U] v.toFun) (g : Vec d → Vec d)
    (hg : ∀ i, (fun x => g x i) =ᵐ[volumeOn U] fun x => v.grad x i) :
    (H1ofAEEq v f hf g hg).grad = g :=
  rfl

/-! ### Smooth clamps -/

/-- Lower smooth clamp: equal to `t` for `t ≥ 3δ/4`, at least `δ/2`
everywhere, with derivative in `[0, 1]`, equal to `1` for `t ≥ 5δ/8`. -/
noncomputable def lowerClamp (δ t : ℝ) : ℝ :=
  t + smoothPositivePartApprox 0 (δ / 8) (3 * δ / 4 - t)

theorem lowerClamp_hasDerivAt (δ t : ℝ) :
    HasDerivAt (lowerClamp δ)
      (1 - smoothPositivePartStep 0 (δ / 8) (3 * δ / 4 - t)) t := by
  have h1 := (smoothPositivePartApprox_hasDerivAt 0 (δ / 8) (3 * δ / 4 - t)).comp t
    ((hasDerivAt_id' t).const_sub (3 * δ / 4))
  have h2 := (hasDerivAt_id' t).add h1
  exact h2.congr_deriv (by ring)

theorem lowerClamp_eq {δ t : ℝ} (hδ : 0 < δ) (ht : 3 * δ / 4 ≤ t) :
    lowerClamp δ t = t := by
  rw [lowerClamp, smoothPositivePartApprox_eq_zero_of_le (by positivity) (by linarith),
    add_zero]

theorem half_le_lowerClamp {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : δ / 2 ≤ lowerClamp δ t := by
  rcases le_total (3 * δ / 4) t with ht | ht
  · rw [lowerClamp_eq hδ ht]
    linarith
  · have h := abs_smoothPositivePartApprox_sub_le (c := 0) (δ := δ / 8) (by positivity)
      (3 * δ / 4 - t)
    rw [sub_zero, max_eq_left (by linarith), abs_le] at h
    rw [lowerClamp]
    linarith [h.1]

theorem deriv_lowerClamp {δ t : ℝ} :
    deriv (lowerClamp δ) t = 1 - smoothPositivePartStep 0 (δ / 8) (3 * δ / 4 - t) :=
  (lowerClamp_hasDerivAt δ t).deriv

theorem deriv_lowerClamp_eq_one {δ t : ℝ} (hδ : 0 < δ) (ht : 5 * δ / 8 ≤ t) :
    deriv (lowerClamp δ) t = 1 := by
  rw [deriv_lowerClamp, smoothPositivePartStep_eq_zero (by positivity) (by linarith),
    sub_zero]

theorem deriv_lowerClamp_mem (δ t : ℝ) :
    0 ≤ deriv (lowerClamp δ) t ∧ deriv (lowerClamp δ) t ≤ 1 := by
  rw [deriv_lowerClamp]
  have h0 := smoothPositivePartStep_nonneg 0 (δ / 8) (3 * δ / 4 - t)
  have h1 := smoothPositivePartStep_le_one 0 (δ / 8) (3 * δ / 4 - t)
  constructor <;> linarith

theorem lowerClamp_contDiff (δ : ℝ) : ContDiff ℝ 1 (lowerClamp δ) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (lowerClamp_hasDerivAt δ t).differentiableAt, ?_⟩
  have : deriv (lowerClamp δ) =
      fun t => 1 - smoothPositivePartStep 0 (δ / 8) (3 * δ / 4 - t) :=
    funext fun t => deriv_lowerClamp
  rw [this]
  exact continuous_const.sub ((smoothPositivePartStep_continuous 0 (δ / 8)).comp
    (continuous_const.sub continuous_id))

/-- Upper smooth clamp: equal to `t` for `t ≤ M + 1`, at most `M + 3`, with
derivative in `[0, 1]`, equal to `1` for `t ≤ M + 2`. -/
noncomputable def upperClamp (M t : ℝ) : ℝ :=
  t - smoothPositivePartApprox 0 1 (t - (M + 1))

theorem upperClamp_hasDerivAt (M t : ℝ) :
    HasDerivAt (upperClamp M) (1 - smoothPositivePartStep 0 1 (t - (M + 1))) t := by
  have h1 := (smoothPositivePartApprox_hasDerivAt 0 1 (t - (M + 1))).comp t
    ((hasDerivAt_id' t).sub_const (M + 1))
  have h2 := (hasDerivAt_id' t).sub h1
  exact h2.congr_deriv (by ring)

theorem upperClamp_eq {M t : ℝ} (ht : t ≤ M + 1) : upperClamp M t = t := by
  rw [upperClamp, smoothPositivePartApprox_eq_zero_of_le one_pos (by linarith), sub_zero]

theorem upperClamp_le (M t : ℝ) : upperClamp M t ≤ M + 3 := by
  rcases le_total t (M + 1) with ht | ht
  · rw [upperClamp_eq ht]
    linarith
  · have h := abs_smoothPositivePartApprox_sub_le (c := 0) (δ := 1) one_pos (t - (M + 1))
    rw [sub_zero, max_eq_left (by linarith), abs_le] at h
    rw [upperClamp]
    linarith [h.1]

theorem min_le_upperClamp (M t : ℝ) : min t (M + 1) ≤ upperClamp M t := by
  rcases le_total t (M + 1) with ht | ht
  · rw [upperClamp_eq ht]
    exact min_le_left _ _
  · have h := abs_smoothPositivePartApprox_le 0 1 (t - (M + 1))
    rw [sub_zero, abs_of_nonneg (by linarith : 0 ≤ t - (M + 1)), abs_le] at h
    rw [upperClamp]
    linarith [h.2, min_le_right t (M + 1)]

theorem deriv_upperClamp {M t : ℝ} :
    deriv (upperClamp M) t = 1 - smoothPositivePartStep 0 1 (t - (M + 1)) :=
  (upperClamp_hasDerivAt M t).deriv

theorem deriv_upperClamp_eq_one {M t : ℝ} (ht : t ≤ M + 2) :
    deriv (upperClamp M) t = 1 := by
  rw [deriv_upperClamp, smoothPositivePartStep_eq_zero one_pos (by linarith), sub_zero]

theorem deriv_upperClamp_mem (M t : ℝ) :
    0 ≤ deriv (upperClamp M) t ∧ deriv (upperClamp M) t ≤ 1 := by
  rw [deriv_upperClamp]
  have h0 := smoothPositivePartStep_nonneg 0 1 (t - (M + 1))
  have h1 := smoothPositivePartStep_le_one 0 1 (t - (M + 1))
  constructor <;> linarith

/-! ### `C¹` extension of `G` along a clamp -/

/-- If `G` has a derivative `G'` on `(0, ∞)` which is continuous there, and
`T` is a `C¹` map into `(0, ∞)` with `|T'| ≤ 1`, then `G ∘ T` is `C¹` with
derivative `G'(T t) T'(t)`. -/
theorem comp_clamp_contDiff {G G' T : ℝ → ℝ}
    (hGd : ∀ t, 0 < t → HasDerivAt G (G' t) t)
    (hG'c : ContinuousOn G' (Set.Ioi 0))
    (hT : ContDiff ℝ 1 T) (hTpos : ∀ t, 0 < T t) :
    ContDiff ℝ 1 (G ∘ T) ∧
      ∀ t, deriv (G ∘ T) t = G' (T t) * deriv T t := by
  have hTd : ∀ t, HasDerivAt T (deriv T t) t := fun t =>
    ((hT.differentiable (by simp)) t).hasDerivAt
  have hcomp : ∀ t, HasDerivAt (G ∘ T) (G' (T t) * deriv T t) t := fun t =>
    (hGd (T t) (hTpos t)).comp t (hTd t)
  have hderiv : ∀ t, deriv (G ∘ T) t = G' (T t) * deriv T t := fun t =>
    (hcomp t).deriv
  refine ⟨?_, hderiv⟩
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hcomp t).differentiableAt, ?_⟩
  rw [show deriv (G ∘ T) = fun t => G' (T t) * deriv T t from funext hderiv]
  exact (hG'c.comp_continuous hT.continuous fun t => hTpos t).mul
    (hT.continuous_deriv le_rfl)

/-! ### Composition for `u ≥ δ` -/

variable (hU : IsOpenBoundedConvexDomain U)

/-- `G(u)` for `u ≥ δ > 0` a.e., when `G` has a continuous derivative `G'` on
`(0, ∞)` bounded by `B` on `[δ/2, ∞)`. Value `G (u x)`, gradient
`G' (u x) • ∇u x`. -/
noncomputable def compOfLowerBound (u : H1Function U) {δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x) (G G' : ℝ → ℝ)
    (hGd : ∀ t, 0 < t → HasDerivAt G (G' t) t)
    (hG'c : ContinuousOn G' (Set.Ioi 0)) {B : ℝ}
    (hB : ∀ t, δ / 2 ≤ t → |G' t| ≤ B) : H1Function U :=
  have hTpos : ∀ t, 0 < lowerClamp δ t := fun t =>
    lt_of_lt_of_le (by positivity) (half_le_lowerClamp hδ t)
  have hext := comp_clamp_contDiff hGd hG'c (lowerClamp_contDiff δ) hTpos
  have hbound : ∀ t, |deriv (G ∘ lowerClamp δ) t| ≤ B := fun t => by
    rw [hext.2 t, abs_mul]
    have h1 := hB _ (half_le_lowerClamp hδ t)
    have h2 := deriv_lowerClamp_mem δ t
    rw [abs_of_nonneg h2.1]
    calc |G' (lowerClamp δ t)| * deriv (lowerClamp δ) t ≤ B * 1 :=
          mul_le_mul h1 h2.2 h2.1 ((abs_nonneg _).trans h1)
      _ = B := mul_one B
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hbound 0)
  let v := u.compContDiffOfDerivBounded hU hext.1 hB0 hbound
  H1ofAEEq v (fun x => G (u x))
    (hu.mono fun x hx => by
      change G (u x) = G (lowerClamp δ (u x))
      rw [lowerClamp_eq hδ (by linarith)])
    (fun x => G' (u x) • u.grad x)
    (fun i => hu.mono fun x hx => by
      change G' (u x) * u.grad x i = deriv (G ∘ lowerClamp δ) (u x) * u.grad x i
      rw [hext.2, lowerClamp_eq hδ (by linarith), deriv_lowerClamp_eq_one hδ (by linarith),
        mul_one])

@[simp]
theorem compOfLowerBound_toFun (u : H1Function U) {δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x) (G G' : ℝ → ℝ)
    (hGd : ∀ t, 0 < t → HasDerivAt G (G' t) t)
    (hG'c : ContinuousOn G' (Set.Ioi 0)) {B : ℝ}
    (hB : ∀ t, δ / 2 ≤ t → |G' t| ≤ B) :
    (compOfLowerBound hU u hδ hu G G' hGd hG'c hB).toFun = fun x => G (u x) :=
  rfl

@[simp]
theorem compOfLowerBound_grad (u : H1Function U) {δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x) (G G' : ℝ → ℝ)
    (hGd : ∀ t, 0 < t → HasDerivAt G (G' t) t)
    (hG'c : ContinuousOn G' (Set.Ioi 0)) {B : ℝ}
    (hB : ∀ t, δ / 2 ≤ t → |G' t| ≤ B) :
    (compOfLowerBound hU u hδ hu G G' hGd hG'c hB).grad =
      fun x => G' (u x) • u.grad x :=
  rfl

/-! ### Composition for `δ ≤ u ≤ M` -/

/-- `G(u)` for `δ ≤ u ≤ M` a.e. (`0 < δ ≤ M`), when `G` has a continuous
derivative `G'` on `(0, ∞)`. Value `G (u x)`, gradient `G' (u x) • ∇u x`. -/
noncomputable def compOfBounds (u : H1Function U) {δ M : ℝ} (hδ : 0 < δ) (hδM : δ ≤ M)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x ∧ u x ≤ M) (G G' : ℝ → ℝ)
    (hGd : ∀ t, 0 < t → HasDerivAt G (G' t) t)
    (hG'c : ContinuousOn G' (Set.Ioi 0)) : H1Function U :=
  have hT : ContDiff ℝ 1 (fun t => upperClamp M (lowerClamp δ t)) := by
    rw [contDiff_one_iff_deriv]
    have hd : ∀ t, HasDerivAt (fun t => upperClamp M (lowerClamp δ t))
        (deriv (upperClamp M) (lowerClamp δ t) * deriv (lowerClamp δ) t) t := fun t =>
      ((upperClamp_hasDerivAt M _).congr_deriv deriv_upperClamp.symm).comp t
        ((lowerClamp_hasDerivAt δ t).congr_deriv deriv_lowerClamp.symm)
    refine ⟨fun t => (hd t).differentiableAt, ?_⟩
    rw [show deriv (fun t => upperClamp M (lowerClamp δ t)) = fun t =>
      deriv (upperClamp M) (lowerClamp δ t) * deriv (lowerClamp δ) t from
      funext fun t => (hd t).deriv]
    have hcu : Continuous (deriv (upperClamp M)) := by
      rw [show deriv (upperClamp M) = fun t => 1 - smoothPositivePartStep 0 1 (t - (M + 1))
        from funext fun t => deriv_upperClamp]
      exact continuous_const.sub ((smoothPositivePartStep_continuous 0 1).comp
        (continuous_id.sub continuous_const))
    exact (hcu.comp (lowerClamp_contDiff δ).continuous).mul
      ((lowerClamp_contDiff δ).continuous_deriv le_rfl)
  have hTrange : ∀ t, δ / 2 ≤ upperClamp M (lowerClamp δ t) ∧
      upperClamp M (lowerClamp δ t) ≤ M + 3 := fun t =>
    ⟨le_trans (le_min (half_le_lowerClamp hδ t) (by linarith))
      (min_le_upperClamp M _), upperClamp_le M _⟩
  have hTpos : ∀ t, 0 < upperClamp M (lowerClamp δ t) := fun t =>
    lt_of_lt_of_le (by positivity) (hTrange t).1
  have hext := comp_clamp_contDiff hGd hG'c hT hTpos
  have hBex : ∃ B, ∀ t ∈ Set.Icc (δ / 2) (M + 3), ‖G' t‖ ≤ B :=
    isCompact_Icc.exists_bound_of_continuousOn
      (hG'c.mono fun t ht => lt_of_lt_of_le (by positivity) ht.1)
  have hbound : ∀ t, |deriv (G ∘ fun t => upperClamp M (lowerClamp δ t)) t| ≤
      hBex.choose := fun t => by
    rw [hext.2 t, abs_mul]
    have h1 : |G' (upperClamp M (lowerClamp δ t))| ≤ hBex.choose :=
      hBex.choose_spec _ (hTrange t)
    have hdT : deriv (fun t => upperClamp M (lowerClamp δ t)) t =
        deriv (upperClamp M) (lowerClamp δ t) * deriv (lowerClamp δ) t :=
      (((upperClamp_hasDerivAt M _).congr_deriv deriv_upperClamp.symm).comp t
        ((lowerClamp_hasDerivAt δ t).congr_deriv deriv_lowerClamp.symm)).deriv
    have hu1 := deriv_upperClamp_mem M (lowerClamp δ t)
    have hl1 := deriv_lowerClamp_mem δ t
    have h2 : |deriv (fun t => upperClamp M (lowerClamp δ t)) t| ≤ 1 := by
      rw [hdT, abs_of_nonneg (mul_nonneg hu1.1 hl1.1)]
      nlinarith
    calc |G' (upperClamp M (lowerClamp δ t))| *
          |deriv (fun t => upperClamp M (lowerClamp δ t)) t| ≤ hBex.choose * 1 :=
          mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
      _ = hBex.choose := mul_one _
  have hB0 : 0 ≤ hBex.choose := (abs_nonneg _).trans (hbound 0)
  let v := u.compContDiffOfDerivBounded hU hext.1 hB0 hbound
  H1ofAEEq v (fun x => G (u x))
    (hu.mono fun x hx => by
      change G (u x) = G (upperClamp M (lowerClamp δ (u x)))
      rw [lowerClamp_eq hδ (by linarith [hx.1]), upperClamp_eq (by linarith [hx.2])])
    (fun x => G' (u x) • u.grad x)
    (fun i => hu.mono fun x hx => by
      change G' (u x) * u.grad x i =
        deriv (G ∘ fun t => upperClamp M (lowerClamp δ t)) (u x) * u.grad x i
      have hdT : deriv (fun t => upperClamp M (lowerClamp δ t)) (u x) =
          deriv (upperClamp M) (lowerClamp δ (u x)) * deriv (lowerClamp δ) (u x) :=
        (((upperClamp_hasDerivAt M _).congr_deriv deriv_upperClamp.symm).comp (u x)
          ((lowerClamp_hasDerivAt δ (u x)).congr_deriv deriv_lowerClamp.symm)).deriv
      rw [hext.2, hdT, lowerClamp_eq hδ (by linarith [hx.1]),
        upperClamp_eq (by linarith [hx.2]),
        deriv_lowerClamp_eq_one hδ (by linarith [hx.1]),
        deriv_upperClamp_eq_one (by linarith [hx.2]), mul_one, mul_one])

@[simp]
theorem compOfBounds_toFun (u : H1Function U) {δ M : ℝ} (hδ : 0 < δ) (hδM : δ ≤ M)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x ∧ u x ≤ M) (G G' : ℝ → ℝ)
    (hGd : ∀ t, 0 < t → HasDerivAt G (G' t) t)
    (hG'c : ContinuousOn G' (Set.Ioi 0)) :
    (compOfBounds hU u hδ hδM hu G G' hGd hG'c).toFun = fun x => G (u x) :=
  rfl

@[simp]
theorem compOfBounds_grad (u : H1Function U) {δ M : ℝ} (hδ : 0 < δ) (hδM : δ ≤ M)
    (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u x ∧ u x ≤ M) (G G' : ℝ → ℝ)
    (hGd : ∀ t, 0 < t → HasDerivAt G (G' t) t)
    (hG'c : ContinuousOn G' (Set.Ioi 0)) :
    (compOfBounds hU u hδ hδM hu G G' hGd hG'c).grad =
      fun x => G' (u x) • u.grad x :=
  rfl

end DGNM

end PDE
