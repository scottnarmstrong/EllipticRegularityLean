module

public import PDEFoundation.Monotonicity.FriedlandHayman.Local.Upper

/-!
# Friedland--Hayman: the pointwise lower bound for the cap energy of a zonal function

If `k y = g (⟪y, e₀⟫)` and `g` has derivative `d` at `a = ⟪x, e₀⟫`, then for small `ε`
`∫_{cap about x} (k x - k y)² ≥ (d² (1 - a²) - η) m_ε`.  The proof linearizes `k` at `x`
(`k y - k x = d ⟪e₀, y - x⟫ + o(|y - x|)`) and uses the cap second moment identity.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PDE.FHLane

noncomputable section

namespace Local

variable {D : ℕ}

theorem sq_lower_bound {A r n d ρ : ℝ} (hA : |A| ≤ |d| * n) (hr : |r| ≤ ρ * n) (hn : 0 ≤ n) : A ^ 2 - 2 * |d| * ρ * n ^ 2 ≤ (A + r) ^ 2 := by
  have h1 : |A| * |r| ≤ (|d| * n) * (ρ * n) :=
    mul_le_mul hA hr (abs_nonneg _) (mul_nonneg (abs_nonneg d) hn)
  have h2 : -(|A| * |r|) ≤ A * r := by
    have := neg_abs_le (A * r)
    rwa [abs_mul] at this
  linarith [sq_nonneg r]

/-- Pointwise lower bound for the inner energy of a function of the height. -/
theorem inner_energy_ge (hD : 2 ≤ D) [NeZero D] (k : C(Sph D, ℝ)) {g : ℝ → ℝ} (x : Sph D) {d : ℝ}
    (hg : HasDerivAt g d (inner ℝ (x : HilbertVec D) (pole D)))
    (hk : ∀ y : Sph D, k y = g (inner ℝ (y : HilbertVec D) (pole D))) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (d ^ 2 * (1 - inner ℝ (x : HilbertVec D) (pole D) ^ 2) - η) * capMom D ε ≤
        ∫ y : Sph D, (if Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D) then
          (k x - k y) ^ 2 else 0) ∂(sphMeasure D) := by
  set a : ℝ := inner ℝ (x : HilbertVec D) (pole D) with ha
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  set ρ : ℝ := η / (2 * (|d| + 1) * D) with hρdef
  have hρ : 0 < ρ := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 (hg.isLittleO.def hρ)
  have hev1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Set.Ioo (0 : ℝ) (min δ (Real.pi / 2)) :=
    Ioo_mem_nhdsGT (lt_min hδ (by positivity [Real.pi_pos]))
  have hev2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), capMom' D ε / capMom D ε < 1 :=
    (tendsto_capMom'_div_capMom hD).eventually (gt_mem_nhds one_pos)
  filter_upwards [hev1, hev2] with ε hε hr
  have hε0 := hε.1
  have hεδ : ε < δ := lt_of_lt_of_le hε.2 (min_le_left _ _)
  have hεπ : ε < Real.pi := by
    have := lt_of_lt_of_le hε.2 (min_le_right _ _); linarith [Real.pi_pos]
  have hm := capMom_pos hD hε0 hεπ
  have hm'0 := capMom'_nonneg hD hε0 hεπ.le
  have hm'm : capMom' D ε ≤ capMom D ε := by
    rw [div_lt_iff₀ hm] at hr; linarith
  set v : HilbertVec D := d • pole D with hv
  have hpt : ∀ y : Sph D, Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D) →
      inner ℝ v ((y : HilbertVec D) - x) ^ 2 - 2 * |d| * ρ * ‖(y : HilbertVec D) - x‖ ^ 2 ≤
        (k x - k y) ^ 2 := by
    intro y hxy
    have hn := norm_sub_lt hε0 hxy
    set n : ℝ := ‖(y : HilbertVec D) - x‖ with hndef
    have hA : inner ℝ v ((y : HilbertVec D) - x) =
        d * (inner ℝ (y : HilbertVec D) (pole D) - a) := by
      rw [hv, real_inner_smul_left, inner_sub_right, real_inner_comm (y : HilbertVec D) (pole D),
        real_inner_comm (x : HilbertVec D) (pole D)]
    have hdist : |inner ℝ (y : HilbertVec D) (pole D) - a| ≤ n := by
      have : inner ℝ (y : HilbertVec D) (pole D) - a = inner ℝ ((y : HilbertVec D) - x) (pole D) := by
        rw [inner_sub_left]
      rw [this]
      have h := abs_real_inner_le_norm ((y : HilbertVec D) - x) (pole D)
      rwa [norm_pole, mul_one] at h
    have hlit := hδ' (y := inner ℝ (y : HilbertVec D) (pole D))
      (by rw [Real.dist_eq]; exact lt_of_le_of_lt hdist (hn.trans hεδ))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul] at hlit
    set r : ℝ := k y - k x - inner ℝ v ((y : HilbertVec D) - x) with hrdef
    have hr1 : |r| ≤ ρ * n := by
      refine le_trans ?_ (mul_le_mul_of_nonneg_left hdist hρ.le)
      have e : r = g (inner ℝ (y : HilbertVec D) (pole D)) - g a -
          (inner ℝ (y : HilbertVec D) (pole D) - a) * d := by
        rw [hrdef, hA, hk y, hk x]; ring
      rw [e]; exact hlit
    have hA1 : |inner ℝ v ((y : HilbertVec D) - x)| ≤ |d| * n := by
      rw [hA, abs_mul]
      exact mul_le_mul_of_nonneg_left hdist (abs_nonneg _)
    have key := sq_lower_bound hA1 hr1 (norm_nonneg _)
    have e2 : (k x - k y) ^ 2 = (inner ℝ v ((y : HilbertVec D) - x) + r) ^ 2 := by
      rw [hrdef]; ring
    rw [e2]
    exact key
  have hcA : Continuous fun y : Sph D => inner ℝ v ((y : HilbertVec D) - x) ^ 2 :=
    (continuous_const.inner (continuous_subtype_val.sub continuous_const)).pow 2
  have hcn : Continuous fun y : Sph D => ‖(y : HilbertVec D) - x‖ ^ 2 :=
    (continuous_subtype_val.sub continuous_const).norm.pow 2
  have hck : Continuous fun y : Sph D => (k x - k y) ^ 2 :=
    (continuous_const.sub k.continuous).pow 2
  have i1 := integrable_cap_at x hcA ε
  have i2 := (integrable_cap_at x hcn ε).const_mul (2 * |d| * ρ)
  have key : ∫ y : Sph D, ((if Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D) then
        inner ℝ v ((y : HilbertVec D) - x) ^ 2 else 0) -
        (2 * |d| * ρ) * (if Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D) then
        ‖(y : HilbertVec D) - x‖ ^ 2 else 0)) ∂(sphMeasure D) ≤
      ∫ y : Sph D, (if Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D) then
        (k x - k y) ^ 2 else 0) ∂(sphMeasure D) := by
    refine integral_mono (i1.sub i2) (integrable_cap_at x hck ε) fun y => ?_
    by_cases hy : Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D)
    · simp only [hy, ↓reduceIte]
      have := hpt y hy
      linarith
    · simp [hy]
  refine le_trans ?_ key
  rw [integral_sub i1 i2, integral_const_mul, cap_second_moment hD x v hε0 hεπ,
    cap_trace hD x hε0 hεπ]
  have hvx : inner ℝ v (x : HilbertVec D) = d * a := by
    rw [hv, real_inner_smul_left, real_inner_comm (x : HilbertVec D) (pole D)]
  have hvn : ‖v‖ ^ 2 = d ^ 2 := by
    rw [hv, norm_smul, mul_pow, norm_pole, Real.norm_eq_abs, sq_abs]; ring
  rw [hvx, hvn]
  have hρD : 2 * |d| * ρ * D ≤ η := by
    rw [hρdef]
    have : 2 * |d| * (η / (2 * (|d| + 1) * D)) * D = η * (|d| / (|d| + 1)) := by
      field_simp
    rw [this]
    have : |d| / (|d| + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    nlinarith
  have hc0 : 0 ≤ 2 * |d| * ρ := by positivity
  have h3 : 2 * |d| * ρ * (((D : ℝ) - 1) * capMom D ε + capMom' D ε) ≤
      2 * |d| * ρ * (D * capMom D ε) := by
    refine mul_le_mul_of_nonneg_left ?_ hc0
    linarith
  have h4 : 2 * |d| * ρ * (D * capMom D ε) ≤ η * capMom D ε := by
    calc 2 * |d| * ρ * (D * capMom D ε) = (2 * |d| * ρ * D) * capMom D ε := by ring
      _ ≤ η * capMom D ε := by gcongr
  have h5 : 0 ≤ capMom' D ε * (d * a) ^ 2 := by positivity
  linarith [h3, h4, h5]

end Local

end

end PDE.FHLane
