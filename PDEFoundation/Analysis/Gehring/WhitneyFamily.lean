module

public import PDEFoundation.Analysis.Gehring.Overlap
public import PDEFoundation.Sobolev.Mean

/-!
# The Whitney family of the level sets of `V = (M (g ^ θ)) ^ (1 / θ)`

For `g ≥ 0` integrable with compact support, `θ = d / (d + 1)`, `V = (M (g ^ θ)) ^ (1 / θ)` and
`E_t = {V > t}`, the level set `E_t` is open and (for `t > 0`) bounded. A `WhitneyFamily d g t σ`
is a Whitney cover of `E_t` on which, in addition, the averages of `g ^ θ` over the dilates
`σ Q` satisfy `(⨍_{σQ} g ^ θ) ^ (1 / θ) ≤ H t` with `H = (9/2) ^ (d + 1)`.
-/

@[expose] public section

namespace PDE.Gehring

open Set MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- The Gehring exponent `θ = d / (d + 1)`. -/
noncomputable def gehringTheta (d : ℕ) : ℝ := (d : ℝ) / ((d : ℝ) + 1)

/-- The Gehring constant `H = (9/2) ^ (d + 1)`. -/
noncomputable def gehringH (d : ℕ) : ℝ := (9 / 2 : ℝ) ^ (d + 1)

theorem gehringTheta_pos (hd : 0 < d) : 0 < gehringTheta d := by
  unfold gehringTheta; positivity

theorem gehringTheta_lt_one (d : ℕ) : gehringTheta d < 1 := by
  unfold gehringTheta
  rw [div_lt_one (by positivity)]; linarith

/-- `V = (M (g ^ θ)) ^ (1 / θ)`. -/
noncomputable def gehringV (g : Vec d → ℝ) (x : Vec d) : ℝ≥0∞ :=
  (cubeMaximal (fun y => g y ^ gehringTheta d) x) ^ (1 / gehringTheta d)

/-- The level set `E_t = {V > t}`. -/
def gehringE (g : Vec d → ℝ) (t : ℝ) : Set (Vec d) :=
  {x | ENNReal.ofReal t < gehringV g x}

theorem mem_gehringE_iff (hd : 0 < d) (g : Vec d → ℝ) {t : ℝ} (ht : 0 ≤ t) (x : Vec d) :
    x ∈ gehringE g t ↔
      ENNReal.ofReal (t ^ gehringTheta d) < cubeMaximal (fun y => g y ^ gehringTheta d) x := by
  have hθ := gehringTheta_pos hd
  show ENNReal.ofReal t < gehringV g x ↔ _
  unfold gehringV
  rw [← ENNReal.rpow_lt_rpow_iff hθ, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hθ.ne',
    ENNReal.rpow_one, ENNReal.ofReal_rpow_of_nonneg ht hθ.le]

theorem isOpen_gehringE (hd : 0 < d) (g : Vec d → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    IsOpen (gehringE g t) := by
  have : gehringE g t = {x | ENNReal.ofReal (t ^ gehringTheta d) <
      cubeMaximal (fun y => g y ^ gehringTheta d) x} := by
    ext x; exact mem_gehringE_iff hd g ht x
  rw [this]
  exact isOpen_lt_cubeMaximal _ _

/-- `g ^ θ` is integrable when `g ≥ 0` is integrable with compact support. -/
theorem integrable_rpow_theta (hd : 0 < d) {g : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hg : Integrable g volume) (hc : HasCompactSupport g) :
    Integrable (fun y => g y ^ gehringTheta d) volume := by
  have hθ := gehringTheta_pos hd
  have hθ1 := gehringTheta_lt_one d
  have hK : Integrable ((tsupport g).indicator (fun _ => (1 : ℝ))) volume :=
    (integrable_indicator_iff hc.isCompact.measurableSet).2
      (integrableOn_const hc.isCompact.measure_lt_top.ne)
  refine Integrable.mono' (hK.add hg) ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (hg.aemeasurable.pow_const _).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (Real.rpow_nonneg (hg0 x) _)]
    rw [Pi.add_apply]
    by_cases hx : x ∈ tsupport g
    · rw [Set.indicator_of_mem hx]
      show g x ^ gehringTheta d ≤ 1 + g x
      by_cases h1 : g x ≤ 1
      · have := Real.rpow_le_one (hg0 x) h1 hθ.le
        linarith [hg0 x]
      · push Not at h1
        have := Real.rpow_le_rpow_of_exponent_le h1.le hθ1.le
        rw [Real.rpow_one] at this
        linarith [hg0 x]
    · have : g x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [Set.indicator_of_notMem hx]
      simp [this, hθ.ne']

theorem isBounded_gehringE (hd : 0 < d) {g : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hg : Integrable g volume) (hc : HasCompactSupport g) {t : ℝ} (ht : 0 < t) :
    Bornology.IsBounded (gehringE g t) := by
  have hθ := gehringTheta_pos hd
  set f : Vec d → ℝ := fun y => g y ^ gehringTheta d with hfdef
  have hf : Integrable f volume := integrable_rpow_theta hd hg0 hg hc
  set I := ∫⁻ y, ‖f y‖ₑ with hIdef
  have hI : I ≠ ∞ := hf.hasFiniteIntegral.ne
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).1 hc.isCompact.isBounded
  have htθ : 0 < t ^ gehringTheta d := Real.rpow_pos_of_pos ht _
  set τ := ENNReal.ofReal (t ^ gehringTheta d) with hτdef
  have hτ0 : τ ≠ 0 := (ENNReal.ofReal_pos.2 htθ).ne'
  have hτtop : τ ≠ ∞ := ENNReal.ofReal_ne_top
  set Mx := (I / τ).toReal with hMx
  refine (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).2 ⟨R + 2 * max 1 Mx, fun x hx => ?_⟩
  rw [mem_gehringE_iff hd g ht.le] at hx
  obtain ⟨c, r, hr, hxc, hlt⟩ := (lt_cubeMaximal_iff _ x _).1 hx
  have hz : ∃ z ∈ closedCenteredAxisCube c r, z ∈ tsupport g := by
    by_contra hcon
    push Not at hcon
    have h0 : ∫⁻ y in closedCenteredAxisCube c r, ‖f y‖ₑ = 0 := by
      rw [setLIntegral_congr_fun (g := fun _ => 0)
        (isClosed_closedCenteredAxisCube c r).measurableSet ?_]
      · simp
      · intro y hy
        have : g y = 0 := image_eq_zero_of_notMem_tsupport (hcon y hy)
        simp [hfdef, this, hθ.ne']
    have : cubeAvg f c r = 0 := by unfold cubeAvg; rw [h0]; simp
    rw [this] at hlt
    exact not_lt_zero hlt
  obtain ⟨z, hzc, hzK⟩ := hz
  have hzR : ‖z‖ ≤ R := mem_closedBall_zero_iff.1 (hR hzK)
  have hV : volume (closedCenteredAxisCube c r) = ENNReal.ofReal ((2 * r) ^ d) :=
    volume_closedCenteredAxisCube c hr.le
  have hbound : (2 * r) ^ d ≤ Mx := by
    unfold cubeAvg at hlt
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl (volume_closedCenteredAxisCube_pos c hr).ne')
      (Or.inl (volume_closedCenteredAxisCube_ne_top c r))] at hlt
    have h1 : volume (closedCenteredAxisCube c r) ≤ I / τ := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hτ0) (Or.inl hτtop), mul_comm]
      exact hlt.le.trans (setLIntegral_le_lintegral _ _)
    have := ENNReal.toReal_mono (ENNReal.div_ne_top hI hτ0) h1
    rwa [volume_closedCenteredAxisCube_toReal c hr.le] at this
  have hr' : r ≤ max 1 Mx := by
    by_cases h3 : 2 * r ≤ 1
    · exact (by linarith : r ≤ 1).trans (le_max_left _ _)
    · push Not at h3
      have : 2 * r ≤ (2 * r) ^ d := le_self_pow₀ h3.le hd.ne'
      exact (by linarith : r ≤ Mx).trans (le_max_right _ _)
  rw [mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg (by have := le_max_left 1 Mx; linarith [norm_nonneg z])).2 fun i => ?_
  have h1 := hxc i (mem_univ i)
  have h2 := hzc i (mem_univ i)
  have h3 : |z i| ≤ R := (Real.norm_eq_abs _ ▸ norm_le_pi_norm z i).trans hzR
  simp only [mem_Icc] at h1 h2
  rw [Real.norm_eq_abs, abs_le]
  have := abs_le.1 h3
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- A Whitney family for the level set `E_t = {V > t}` of `V = (M (g ^ θ)) ^ (1 / θ)`:
a Whitney cover of `E_t` (see `WhitneyCover`) such that for every cube `Q`
`(⨍_{σ Q} g ^ θ) ^ (1 / θ) ≤ H t`, with `θ = d / (d + 1)`, `H = (9/2) ^ (d + 1)`. -/
structure WhitneyFamily (d : ℕ) (g : Vec d → ℝ) (t : ℝ) (σ : ℝ)
    extends WhitneyCover (gehringE g t) σ where
  /-- `(⨍_{σ Q} g ^ θ) ^ (1 / θ) ≤ H t`, using `1 / θ = (d + 1) / d`. -/
  avg_le : ∀ i : ι,
    (integralAverage (centeredAxisCube (dyadicCenter (scale i) (index i))
        (σ * 2 ^ scale i / 2)) (fun x => g x ^ gehringTheta d)) ^ (((d : ℝ) + 1) / d) ≤
      gehringH d * t

end PDE.Gehring
