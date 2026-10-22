module

public import PDEFoundation.Analysis.Gehring.TailSum

/-!
# The global tail estimate (4.32)

For `g ≥ 0` integrable with compact support and the reverse Hölder inequality on all cubes,
for every `t > 0`
`∫_{g>t} g ≤ D_d A t^{1-θ} ∫_{g > 2^{-1/θ} t} g^θ + B N_σ ∫_{E_t} h`.
-/

@[expose] public section

namespace PDE.Gehring

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

/-- The level `2^{-1/θ}`. -/
noncomputable def gehringC (d : ℕ) : ℝ := (2 : ℝ) ^ (-(1 / gehringTheta d))

theorem gehringC_pos (d : ℕ) : 0 < gehringC d := by unfold gehringC; positivity

theorem gehringC_le_one (hd : 0 < d) : gehringC d ≤ 1 := by
  have := gehringTheta_pos hd
  unfold gehringC
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by
    have : 0 < 1 / gehringTheta d := by positivity
    linarith)

theorem gehringC_rpow_theta (hd : 0 < d) : gehringC d ^ gehringTheta d = 1 / 2 := by
  have hθ := gehringTheta_pos hd
  unfold gehringC
  rw [← Real.rpow_mul (by norm_num)]
  rw [show -(1 / gehringTheta d) * gehringTheta d = -1 by field_simp]
  rw [Real.rpow_neg_one]; norm_num

/-- The two superlevel sets agree: `{g^θ > t^θ/2} = {g > 2^{-1/θ} t}`. -/
theorem setOf_rpow_theta_eq (hd : 0 < d) {g : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x) {t : ℝ}
    (ht : 0 ≤ t) :
    {y | t ^ gehringTheta d / 2 < g y ^ gehringTheta d} = {y | gehringC d * t < g y} := by
  have hθ := gehringTheta_pos hd
  ext y
  have h1 : (gehringC d * t) ^ gehringTheta d = t ^ gehringTheta d / 2 := by
    rw [Real.mul_rpow (gehringC_pos d).le ht, gehringC_rpow_theta hd]; ring
  simp only [Set.mem_ofPred_eq]
  rw [← h1, Real.rpow_lt_rpow_iff (by have := gehringC_pos d; positivity) (hg0 y) hθ]

theorem ae_lt_mem_gehringE (hd : 0 < d) {g : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hg : Integrable g volume) (hc : HasCompactSupport g) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), t < g x → x ∈ gehringE g t := by
  have hθ := gehringTheta_pos hd
  have hloc : LocallyIntegrable (fun y => g y ^ gehringTheta d) volume :=
    (integrable_rpow_theta hd hg0 hg hc).locallyIntegrable
  filter_upwards [ae_enorm_le_cubeMaximal hloc] with x hx hgt
  rw [mem_gehringE_iff hd g ht.le]
  refine lt_of_lt_of_le ?_ hx
  rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (hg0 x) _)]
  exact (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos (ht.trans hgt) _)).2
    (Real.rpow_lt_rpow ht.le hgt hθ)

/-- The weak-type bound for `E_t = {V > t}`, in terms of `∫_{g > 2^{-1/θ} t} g^θ`. -/
theorem volume_gehringE_le (hd : 0 < d) {g : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hg : Integrable g volume) {t : ℝ} (ht : 0 < t) :
    volume (gehringE g t) ≤ ENNReal.ofReal (2 * 3 ^ d / t ^ gehringTheta d) *
      ∫⁻ y in {y | gehringC d * t < g y}, ENNReal.ofReal (g y ^ gehringTheta d) := by
  have hθ := gehringTheta_pos hd
  have htθ : 0 < t ^ gehringTheta d := Real.rpow_pos_of_pos ht _
  have hE : gehringE g t = {x | ENNReal.ofReal (t ^ gehringTheta d) <
      cubeMaximal (fun y => g y ^ gehringTheta d) x} := by
    ext x; exact mem_gehringE_iff hd g ht.le x
  rw [hE]
  have := volume_lt_cubeMaximal_le_setLIntegral hd (k := fun y => g y ^ gehringTheta d)
    (fun y => Real.rpow_nonneg (hg0 y) _) (hg.aemeasurable.pow_const _) htθ
  rw [setOf_rpow_theta_eq hd hg0 ht.le] at this
  refine this.trans (le_of_eq ?_)
  congr 1
  refine lintegral_congr fun y => ?_
  exact Real.enorm_eq_ofReal (Real.rpow_nonneg (hg0 y) _)

/-- **(4.32)** (global form): with `T = univ`, `D = univ`.
For every `t > 0`,
`∫_{g>t} g ≤ D_d A t^{1-θ} ∫_{g > 2^{-1/θ} t} g^θ + B N_σ ∫_{E_t} h`. -/
theorem tail_global (hd : 0 < d) {g h : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hh0 : ∀ x, 0 ≤ h x) (hg : Integrable g volume) (hc : HasCompactSupport g)
    (hh : LocallyIntegrable h volume)
    {σ A B t : ℝ} (hσ : σ = 2 ∨ σ = 4) (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 < t)
    (hrh : ∀ (z : Vec d) (r : ℝ), 0 < r → GehringRH d σ A B g h z r) :
    ∫⁻ x in {x | t < g x}, ENNReal.ofReal (g x) ≤
      ENNReal.ofReal (gehringD d * A * t ^ (1 - gehringTheta d)) *
          (∫⁻ y in {y | gehringC d * t < g y}, ENNReal.ofReal (g y ^ gehringTheta d)) +
        ENNReal.ofReal (B * gehringN σ d) * ∫⁻ x in gehringE g t, ENNReal.ofReal (h x) := by
  obtain ⟨F⟩ := exists_whitneyFamily hd hg0 hg hc ht hσ
  have h1 := lintegral_gt_le_family hd hg0 hh0 hg hh hσ hA hB ht.le F Set.univ Set.univ
    (fun i _ => hrh _ _ (by have := F.toWhitneyCover.side_pos i; positivity))
    (by
      have hnull := F.toWhitneyCover.volume_diff_iUnion_cube_eq_zero
      filter_upwards [ae_lt_mem_gehringE hd hg0 hg hc ht, measure_eq_zero_iff_ae_notMem.1 hnull]
        with x hx1 hx2 hx3
      have hxE := hx1 hx3.1
      by_contra hcon
      exact hx2 ⟨hxE, fun hm => hcon (by simpa using hm)⟩)
  rw [Set.inter_univ] at h1
  refine h1.trans (add_le_add ?_ le_rfl)
  have h2 := volume_gehringE_le hd hg0 hg ht
  have hH := gehringH_pos d
  calc ENNReal.ofReal (A * gehringH d * t) * volume (gehringE g t)
      ≤ ENNReal.ofReal (A * gehringH d * t) * (ENNReal.ofReal (2 * 3 ^ d / t ^ gehringTheta d) *
          ∫⁻ y in {y | gehringC d * t < g y}, ENNReal.ofReal (g y ^ gehringTheta d)) := by
        gcongr
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [Real.rpow_sub ht, Real.rpow_one, gehringD]
        field_simp

end PDE.Gehring
