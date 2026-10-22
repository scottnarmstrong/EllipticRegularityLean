module

public import PDEFoundation.Monotonicity.FriedlandHayman.Symm.Compact

/-!
# Friedland--Hayman: the zonal rearrangement

A maximizer of the height moment over the polarization hull is height-monotone, and inherits the
invariants of the hull. This gives `exists_zonal_rearrangement`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

namespace PDE.FHLane

noncomputable section

namespace Rearr

variable {D : ℕ}

theorem le_of_inner_lt {g : C(Sph D, ℝ)} {e : HilbertVec D} {k : C(Sph D, ℝ)} (hk : k ∈ Hull g e)
    (hmax : ∀ k' ∈ Hull g e, moment e k' ≤ moment e k) {x y : Sph D}
    (hxy : inner ℝ (x : HilbertVec D) e < inner ℝ (y : HilbertVec D) e) : k x ≤ k y := by
  by_contra hlt
  rw [not_le] at hlt
  set v : HilbertVec D := (y : HilbertVec D) - x with hvdef
  have hv : v ≠ 0 := by
    intro h
    have : (y : HilbertVec D) = x := sub_eq_zero.1 h
    rw [this] at hxy
    exact lt_irrefl _ hxy
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  set n := ‖v‖ with hndef
  set u : HilbertVec D := n⁻¹ • v with hudef
  have hu : ‖u‖ = 1 := by
    rw [hudef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hx1 : ‖(x : HilbertVec D)‖ = 1 := by simp
  have hy1 : ‖(y : HilbertVec D)‖ = 1 := by simp
  have hn2 : n ^ 2 = 2 - 2 * inner ℝ (y : HilbertVec D) (x : HilbertVec D) := by
    rw [hndef, ← real_inner_self_eq_norm_sq, hvdef, inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hx1, hy1,
      real_inner_comm (x : HilbertVec D) y]
    ring
  have hue : inner ℝ u e = n⁻¹ * (inner ℝ (y : HilbertVec D) e - inner ℝ (x : HilbertVec D) e) := by
    rw [hudef, inner_smul_left, hvdef, inner_sub_left]; simp
  have hyu : inner ℝ (y : HilbertVec D) u = n / 2 := by
    rw [hudef, inner_smul_right, hvdef, inner_sub_right, real_inner_self_eq_norm_sq, hy1]
    field_simp
    nlinarith
  have hue' : 0 < inner ℝ u e := by
    rw [hue]; exact mul_pos (inv_pos.2 hn) (by linarith)
  have hρ : Symm.rho u hu y = x := by
    apply Subtype.ext
    rw [Symm.coe_rho, hyu, hudef, smul_smul, show 2 * (n / 2) * n⁻¹ = 1 by field_simp, one_smul]
    simp [hvdef]
  have hgt := integral_polarize_mul_inner_gt u hu k hue' (x₀ := y) (by rw [hyu]; positivity)
    (by show k y < k (Symm.rho u hu y); rw [hρ]; exact hlt)
  have := hmax _ (polarize_mem_hull hk u hu hue'.le)
  unfold moment at this
  linarith

theorem inner_eq_smul_of_sq_eq_one {e : HilbertVec D} (he : ‖e‖ = 1) {x : Sph D} {h : ℝ}
    (hx : inner ℝ (x : HilbertVec D) e = h) : ‖(x : HilbertVec D) - h • e‖ ^ 2 = 1 - h ^ 2 := by
  have hx1 : ‖(x : HilbertVec D)‖ = 1 := by simp
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, hx1, he, conj_trivial]
  rw [real_inner_comm (x : HilbertVec D) e, hx]
  ring

theorem abs_inner_lt_or {e : HilbertVec D} (he : ‖e‖ = 1) {x : Sph D} :
    |inner ℝ (x : HilbertVec D) e| < 1 ∨ (x : HilbertVec D) = inner ℝ (x : HilbertVec D) e • e := by
  have h := inner_eq_smul_of_sq_eq_one he (x := x) rfl
  have h0 : 0 ≤ 1 - inner ℝ (x : HilbertVec D) e ^ 2 := by rw [← h]; positivity
  rcases h0.lt_or_eq with h1 | h1
  · left
    exact abs_lt_of_sq_lt_sq (by nlinarith) zero_le_one
  · right
    rw [← h1] at h
    have : ‖(x : HilbertVec D) - inner ℝ (x : HilbertVec D) e • e‖ = 0 := by
      simpa using h
    exact sub_eq_zero.1 (norm_eq_zero.1 this)

theorem mem_closure_cap {e : HilbertVec D} (he : ‖e‖ = 1) {y : Sph D}
    (hy : |inner ℝ (y : HilbertVec D) e| < 1) :
    y ∈ closure {z : Sph D | inner ℝ (y : HilbertVec D) e < inner ℝ (z : HilbertVec D) e} := by
  set h := inner ℝ (y : HilbertVec D) e with hh
  have hy1 : ‖(y : HilbertVec D)‖ = 1 := by simp
  set w : ℝ → HilbertVec D := fun t => ‖(y : HilbertVec D) + t • e‖⁻¹ • ((y : HilbertVec D) + t • e)
    with hw
  have hw0 : w 0 = y := by simp [hw, hy1]
  have hcont : ContinuousAt w 0 := by
    refine ContinuousAt.smul (ContinuousAt.inv₀ (f := fun t : ℝ => ‖(y : HilbertVec D) + t • e‖)
      ?_ ?_) ?_
    · fun_prop
    · simp [hy1]
    · fun_prop
  have htend : Tendsto w (𝓝[>] 0) (𝓝 (y : HilbertVec D)) := by
    rw [← hw0]; exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), w t ∈
      ((↑) : Sph D → HilbertVec D) '' {z : Sph D | h < inner ℝ (z : HilbertVec D) e} := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have hN1 : 1 - t ≤ ‖(y : HilbertVec D) + t • e‖ := by
      have := norm_sub_norm_le (y : HilbertVec D) (-(t • e))
      rw [sub_neg_eq_add, norm_neg, norm_smul, he, hy1, Real.norm_eq_abs, abs_of_pos ht] at this
      linarith
    have hN2 : ‖(y : HilbertVec D) + t • e‖ ≤ 1 + t := by
      have := norm_add_le (y : HilbertVec D) (t • e)
      rwa [norm_smul, he, hy1, Real.norm_eq_abs, abs_of_pos ht, mul_one] at this
    have hNpos : 0 < ‖(y : HilbertVec D) + t • e‖ := by
      refine norm_pos_iff.2 fun h0 => ?_
      have h1 : (y : HilbertVec D) = -(t • e) := eq_neg_of_add_eq_zero_left h0
      have h2 : t = 1 := by
        have := congrArg norm h1
        rwa [hy1, norm_neg, norm_smul, he, Real.norm_eq_abs, abs_of_pos ht, mul_one, eq_comm] at this
      have h3 : h = -1 := by
        rw [hh, h1, inner_neg_left, inner_smul_left, real_inner_self_eq_norm_sq, he, h2]
        simp
      rw [h3] at hy
      norm_num at hy
    have hmem : w t ∈ Metric.sphere (0 : HilbertVec D) 1 := by
      rw [mem_sphere_zero_iff_norm, hw]
      dsimp only
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hNpos.ne']
    refine ⟨⟨w t, hmem⟩, ?_, rfl⟩
    show h < inner ℝ (w t) e
    rw [hw, inner_smul_left, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq, he, ← hh]
    simp only [conj_trivial, one_pow, mul_one, map_inv₀]
    rw [← div_eq_inv_mul, lt_div_iff₀ hNpos]
    have hab := abs_lt.1 hy
    have h3 : |h * (1 - ‖(y : HilbertVec D) + t • e‖)| < t := by
      rw [abs_mul]
      have h4 : |1 - ‖(y : HilbertVec D) + t • e‖| ≤ t := by
        rw [abs_le]; constructor <;> linarith
      calc |h| * |1 - ‖(y : HilbertVec D) + t • e‖| ≤ |h| * t :=
            mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
        _ < 1 * t := mul_lt_mul_of_pos_right hy ht
        _ = t := one_mul t
    have h5 := abs_lt.1 h3
    nlinarith
  have hcl := mem_closure_of_tendsto htend hev
  rw [IsInducing.subtypeVal.closure_eq_preimage_closure_image]
  exact hcl

theorem le_of_inner_le {g : C(Sph D, ℝ)} {e : HilbertVec D} (he : ‖e‖ = 1) {k : C(Sph D, ℝ)}
    (hk : k ∈ Hull g e) (hmax : ∀ k' ∈ Hull g e, moment e k' ≤ moment e k) {x y : Sph D}
    (hxy : inner ℝ (x : HilbertVec D) e ≤ inner ℝ (y : HilbertVec D) e) : k x ≤ k y := by
  rcases hxy.lt_or_eq with h | h
  · exact le_of_inner_lt hk hmax h
  · by_cases hy : |inner ℝ (y : HilbertVec D) e| < 1
    · have hcl := mem_closure_cap he hy
      have hclosed : IsClosed {z : Sph D | k x ≤ k z} :=
        isClosed_le continuous_const k.continuous
      refine (closure_minimal (fun z hz => le_of_inner_lt hk hmax ?_) hclosed) hcl
      rw [h]
      exact hz
    · have hx := (abs_inner_lt_or he (x := x)).resolve_left (by rw [h]; exact hy)
      have hy' := (abs_inner_lt_or he (x := y)).resolve_left hy
      have : x = y := Subtype.ext (by rw [hx, hy', h])
      rw [this]

/-- The truncations `min 1 ((n+1) max t 0)` of the indicator of `(0, ∞)`. -/
def trunc (n : ℕ) : C(ℝ, ℝ) :=
  ⟨fun t => min 1 ((n + 1) * max t 0), by fun_prop⟩

theorem trunc_nonneg (n : ℕ) (t : ℝ) : 0 ≤ trunc n t := by
  show 0 ≤ min 1 ((n + 1) * max t 0)
  exact le_min zero_le_one (by positivity)

theorem trunc_le_indicator (n : ℕ) (g : C(Sph D, ℝ)) (x : Sph D) :
    trunc n (g x) ≤ {z : Sph D | 0 < g z}.indicator 1 x := by
  by_cases h : 0 < g x
  · rw [indicator_of_mem (show x ∈ {z : Sph D | 0 < g z} from h)]
    exact min_le_left _ _
  · rw [indicator_of_notMem (show x ∉ {z : Sph D | 0 < g z} from h)]
    have : max (g x) 0 = 0 := max_eq_right (not_lt.1 h)
    show min 1 ((n + 1) * max (g x) 0) ≤ _
    rw [this]; simp

theorem indicator_le_trunc (n : ℕ) {k : C(Sph D, ℝ)} (x : Sph D) :
    {z : Sph D | 1 / ((n : ℝ) + 1) ≤ k z}.indicator 1 x ≤ trunc n (k x) := by
  by_cases h : 1 / ((n : ℝ) + 1) ≤ k x
  · rw [indicator_of_mem (show x ∈ {z : Sph D | 1 / ((n : ℝ) + 1) ≤ k z} from h)]
    show (1 : ℝ) ≤ min 1 ((n + 1) * max (k x) 0)
    refine le_min le_rfl ?_
    have hpos : (0 : ℝ) < n + 1 := by positivity
    have : 1 ≤ ((n : ℝ) + 1) * k x := by
      rw [div_le_iff₀ hpos] at h; linarith
    exact this.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hpos.le)
  · rw [indicator_of_notMem (show x ∉ {z : Sph D | 1 / ((n : ℝ) + 1) ≤ k z} from h)]
    exact trunc_nonneg n _

theorem measure_ge_le {g : C(Sph D, ℝ)} {L : NNReal} {M : ℝ} {k : C(Sph D, ℝ)}
    (hk : Inv g L M k) (n : ℕ) :
    sphMeasure D {z | 1 / ((n : ℝ) + 1) ≤ k z} ≤ sphMeasure D {z | 0 < g z} := by
  have hm1 : MeasurableSet {z : Sph D | 1 / ((n : ℝ) + 1) ≤ k z} :=
    (isClosed_le continuous_const k.continuous).measurableSet
  have hm2 : MeasurableSet {z : Sph D | 0 < g z} :=
    (isOpen_lt continuous_const g.continuous).measurableSet
  have hfin : ∀ s : Set (Sph D), sphMeasure D s ≠ ⊤ := fun s => measure_ne_top _ s
  rw [← ENNReal.toReal_le_toReal (hfin _) (hfin _)]
  show (sphMeasure D).real _ ≤ (sphMeasure D).real _
  rw [← integral_indicator_one hm1, ← integral_indicator_one hm2]
  calc ∫ x, {z : Sph D | 1 / ((n : ℝ) + 1) ≤ k z}.indicator 1 x ∂(sphMeasure D)
      ≤ ∫ x, trunc n (k x) ∂(sphMeasure D) :=
        integral_mono ((integrable_const (1 : ℝ)).indicator hm1)
          (Symm.integrable_of_continuous ((trunc n).continuous.comp k.continuous))
          fun x => indicator_le_trunc n x
    _ = ∫ x, trunc n (g x) ∂(sphMeasure D) := hk.2.2.2.1 (trunc n)
    _ ≤ _ := integral_mono (Symm.integrable_of_continuous ((trunc n).continuous.comp g.continuous))
          ((integrable_const (1 : ℝ)).indicator hm2) fun x => trunc_le_indicator n g x

theorem measure_pos_le {g : C(Sph D, ℝ)} {L : NNReal} {M : ℝ} {k : C(Sph D, ℝ)}
    (hk : Inv g L M k) : sphMeasure D {z | 0 < k z} ≤ sphMeasure D {z | 0 < g z} := by
  have hU : {z : Sph D | 0 < k z} = ⋃ n : ℕ, {z | 1 / ((n : ℝ) + 1) ≤ k z} := by
    ext z
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hz
      exact ⟨n, hn.le⟩
    · rintro ⟨n, hn⟩
      exact lt_of_lt_of_le (by positivity) hn
  have hmono : Monotone (fun n : ℕ => {z : Sph D | 1 / ((n : ℝ) + 1) ≤ k z}) := by
    intro a b hab z hz
    refine le_trans ?_ (show z ∈ {z : Sph D | _ ≤ _} from hz)
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
  rw [hU, hmono.measure_iUnion]
  exact iSup_le fun n => measure_ge_le hk n

end Rearr

open Rearr in
/-- Zonal (height-monotone) rearrangement of a nonnegative Lipschitz function on the sphere. -/
theorem exists_zonal_rearrangement {D : ℕ} (_hD : 2 ≤ D) (g : C(Sph D, ℝ)) (hg0 : ∀ x, 0 ≤ g x)
    {L : NNReal} (hL : LipschitzWith L g) {e : HilbertVec D} (he : ‖e‖ = 1) :
    ∃ k : C(Sph D, ℝ), (∀ x, 0 ≤ k x) ∧ LipschitzWith L k ∧
      (∀ x y : Sph D, inner ℝ (x : HilbertVec D) e ≤ inner ℝ (y : HilbertVec D) e → k x ≤ k y) ∧
      (∫ x, k x ^ 2 ∂(sphMeasure D) = ∫ x, g x ^ 2 ∂(sphMeasure D)) ∧
      (∀ ε, nlEnergy ε k ≤ nlEnergy ε g) ∧
      sphMeasure D {x | 0 < k x} ≤ sphMeasure D {x | 0 < g x} := by
  have hg : Inv g L ‖g‖ g := ⟨hg0, fun x => (le_abs_self _).trans (g.norm_coe_le_norm x),
    hL, fun _ => rfl, fun _ => le_rfl⟩
  obtain ⟨k, hk, hmax⟩ := exists_max_moment hg e
  obtain ⟨h0, -, hLk, hΦ, hE⟩ := hull_inv hg hk
  exact ⟨k, h0, hLk, fun x y hxy => le_of_inner_le he hk hmax hxy,
    hΦ ⟨fun t => t ^ 2, by fun_prop⟩, hE, measure_pos_le (hull_inv hg hk)⟩

end

end PDE.FHLane
