module

public import PDEFoundation.Analysis.Gehring.CubeMaximal
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Covering.DensityTheorem

/-!
# Weak-type (1,1) bound for the cube maximal function (Vitali covering)

The constant is the sharp `3 ^ d`, obtained by letting the Vitali enlargement factor tend to one.
-/

@[expose] public section

namespace PDE.Gehring

open MeasureTheory Set Filter Topology
open scoped ENNReal

private theorem measurable_closedCube {d : ℕ} (c : Vec d) (r : ℝ) :
    MeasurableSet (closedCenteredAxisCube c r) :=
  (isClosed_closedCenteredAxisCube c r).measurableSet

/-- Weak-type `(1,1)` for `τ`-enlargement: an intermediate bound with the constant
`(1 + 2τ) ^ d`. -/
theorem volume_lt_cubeMaximal_le_aux {d : ℕ} (hd : 0 < d) (k : Vec d → ℝ) {s : ℝ}
    (hs : 0 < s) {τ : ℝ} (hτ : 1 < τ) (hI : ∫⁻ y, ‖k y‖ₑ ≠ ∞) :
    volume {x | ENNReal.ofReal s < cubeMaximal k x} ≤
      ENNReal.ofReal ((1 + 2 * τ) ^ d) * ((∫⁻ y, ‖k y‖ₑ) / ENNReal.ofReal s) := by
  set I := ∫⁻ y, ‖k y‖ₑ with hIdef
  have hs' : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.2 hs).ne'
  set T : Set (Vec d × ℝ) :=
    {a | 0 < a.2 ∧ ENNReal.ofReal s < cubeAvg k a.1 a.2} with hT
  let B : Vec d × ℝ → Set (Vec d) := fun a => closedCenteredAxisCube a.1 a.2
  -- key bound on the volume of a cube in `T`
  have hVle : ∀ a ∈ T, volume (B a) ≤ (∫⁻ y in B a, ‖k y‖ₑ) / ENNReal.ofReal s := by
    intro a ha
    have h := ha.2
    unfold cubeAvg at h
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl (volume_closedCenteredAxisCube_pos a.1 ha.1).ne')
      (Or.inl (volume_closedCenteredAxisCube_ne_top a.1 a.2))] at h
    rw [ENNReal.le_div_iff_mul_le (Or.inl hs') (Or.inl ENNReal.ofReal_ne_top)]
    rw [mul_comm]
    exact h.le
  have hbdd : ∀ a ∈ T, a.2 ≤ max 1 (I / ENNReal.ofReal s).toReal := by
    intro a ha
    have h1 : volume (B a) ≤ I / ENNReal.ofReal s :=
      (hVle a ha).trans (ENNReal.div_le_div_right (setLIntegral_le_lintegral _ _) _)
    have hfin : I / ENNReal.ofReal s ≠ ∞ := ENNReal.div_ne_top hI hs'
    have h2 : (2 * a.2) ^ d ≤ (I / ENNReal.ofReal s).toReal := by
      have := ENNReal.toReal_mono hfin h1
      rwa [volume_closedCenteredAxisCube_toReal a.1 ha.1.le] at this
    by_cases h3 : 2 * a.2 ≤ 1
    · exact (by linarith : a.2 ≤ 1).trans (le_max_left _ _)
    · push Not at h3
      have : 2 * a.2 ≤ (2 * a.2) ^ d := le_self_pow₀ h3.le hd.ne'
      exact (by linarith : a.2 ≤ _).trans (le_max_right _ _)
  obtain ⟨u, huT, hudisj, hucov⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement B T (fun a => a.2) τ hτ
      (fun a ha => ha.1.le) _ hbdd
      (fun a ha => ⟨a.1, fun i _ => ⟨by linarith [ha.1], by linarith [ha.1]⟩⟩)
  have hucount : u.Countable := by
    refine hudisj.countable_of_nonempty_interior fun a ha => ?_
    have hr := (huT ha).1
    have hsub : centeredAxisCube a.1 a.2 ⊆ B a := by
      intro y hy i _
      have := hy i (mem_univ i)
      exact ⟨this.1.le, this.2.le⟩
    refine ⟨a.1, interior_maximal hsub (isOpen_centeredAxisCube a.1 a.2) ?_⟩
    intro i _
    exact ⟨by linarith, by linarith⟩
  have : Countable u := hucount.to_subtype
  have hcov : {x | ENNReal.ofReal s < cubeMaximal k x} ⊆
      ⋃ b ∈ u, closedCenteredAxisCube b.1 ((1 + 2 * τ) * b.2) := by
    intro x hx
    obtain ⟨c, r, hr, hxc, hlt⟩ := (lt_cubeMaximal_iff k x _).1 hx
    obtain ⟨b, hbu, ⟨y, hya, hyb⟩, hab⟩ := hucov (c, r) ⟨hr, hlt⟩
    have hb := (huT hbu).1
    simp only at hab
    rw [mem_iUnion₂]
    refine ⟨b, hbu, fun i _ => ?_⟩
    have h1 := hxc i (mem_univ i)
    have h2 := hya i (mem_univ i)
    have h3 := hyb i (mem_univ i)
    simp only [mem_Icc] at h1 h2 h3 ⊢
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, hb]
  have hterm : ∀ b : u, volume (closedCenteredAxisCube (b : Vec d × ℝ).1
      ((1 + 2 * τ) * (b : Vec d × ℝ).2)) ≤
      ENNReal.ofReal ((1 + 2 * τ) ^ d) *
        ((∫⁻ y in B b, ‖k y‖ₑ) / ENNReal.ofReal s) := by
    intro b
    have hb := (huT b.2).1
    rw [volume_closedCenteredAxisCube _ (by nlinarith)]
    have : (2 * ((1 + 2 * τ) * (b : Vec d × ℝ).2)) ^ d =
        (1 + 2 * τ) ^ d * (2 * (b : Vec d × ℝ).2) ^ d := by
      rw [← mul_pow]; congr 1; ring
    rw [this, ENNReal.ofReal_mul (by positivity),
      ← volume_closedCenteredAxisCube _ hb.le]
    exact mul_le_mul_right (hVle b (huT b.2)) _
  have hdisj : Pairwise (Function.onFun Disjoint fun b : u => B b) := by
    intro a b hab
    exact hudisj a.2 b.2 (fun h => hab (Subtype.ext h))
  calc volume {x | ENNReal.ofReal s < cubeMaximal k x}
      ≤ volume (⋃ b ∈ u, closedCenteredAxisCube b.1 ((1 + 2 * τ) * b.2)) :=
        measure_mono hcov
    _ ≤ ∑' b : u, volume (closedCenteredAxisCube (b : Vec d × ℝ).1
          ((1 + 2 * τ) * (b : Vec d × ℝ).2)) :=
        measure_biUnion_le volume hucount _
    _ ≤ ∑' b : u, ENNReal.ofReal ((1 + 2 * τ) ^ d) *
          ((∫⁻ y in B b, ‖k y‖ₑ) / ENNReal.ofReal s) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal ((1 + 2 * τ) ^ d) *
          ((∑' b : u, ∫⁻ y in B b, ‖k y‖ₑ) / ENNReal.ofReal s) := by
        rw [ENNReal.tsum_mul_left]
        congr 1
        simp only [div_eq_mul_inv]
        rw [ENNReal.tsum_mul_right]
    _ ≤ ENNReal.ofReal ((1 + 2 * τ) ^ d) * (I / ENNReal.ofReal s) := by
        gcongr
        rw [← lintegral_iUnion (fun b : u => measurable_closedCube _ _) hdisj]
        exact setLIntegral_le_lintegral _ _

/-- **Weak-type `(1,1)` bound** (`x.vitali`) for the uncentered maximal function over closed
axis cubes, with the sharp constant `3 ^ d`. -/
theorem volume_lt_cubeMaximal_le {d : ℕ} (hd : 0 < d) (k : Vec d → ℝ) {s : ℝ} (hs : 0 < s) :
    volume {x | ENNReal.ofReal s < cubeMaximal k x} ≤
      ENNReal.ofReal (3 ^ d / s) * ∫⁻ y, ‖k y‖ₑ := by
  by_cases hI : ∫⁻ y, ‖k y‖ₑ = ∞
  · rw [hI, ENNReal.mul_top]
    · exact le_top
    · exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  set I := ∫⁻ y, ‖k y‖ₑ with hIdef
  have hlim : Tendsto (fun τ : ℝ => ENNReal.ofReal ((1 + 2 * τ) ^ d) * (I / ENNReal.ofReal s))
      (𝓝[>] 1) (𝓝 (ENNReal.ofReal ((1 + 2 * 1) ^ d) * (I / ENNReal.ofReal s))) := by
    have hc : Continuous fun τ : ℝ => (1 + 2 * τ) ^ d := by fun_prop
    refine ENNReal.Tendsto.mul_const ?_ (Or.inl ?_)
    · exact (ENNReal.tendsto_ofReal (hc.tendsto 1)).mono_left nhdsWithin_le_nhds
    · exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have := ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun τ (hτ : 1 < τ) =>
    volume_lt_cubeMaximal_le_aux hd k hs hτ hI)
  refine this.trans (le_of_eq ?_)
  norm_num only
  rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos hs, div_eq_mul_inv, ENNReal.ofReal_mul (by positivity)]
  ring

end PDE.Gehring
