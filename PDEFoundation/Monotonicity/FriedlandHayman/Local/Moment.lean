module

public import PDEFoundation.Monotonicity.FriedlandHayman.Local.CapInt

/-!
# Friedland--Hayman: the cap second moment

For `x` on the unit sphere and any vector `v`,
`∫_{cos ε < ⟪x, y⟫} ⟪v, y - x⟫² dσ(y) = m_ε (|v|² - ⟪v, x⟫²) + m'_ε ⟪v, x⟫²`.
The case `x = e₀` follows from the zonal formula and the symmetry of the cap under the isometries
fixing `e₀`: a reflection kills the cross term and swapping coordinates equalizes the transverse
second moments, whose sum is `∫_cap (1 - ⟪y, e₀⟫²)`.  The general case rotates `x` to `e₀`.
-/

@[expose] public section

open MeasureTheory

namespace PDE.FHLane

noncomputable section

namespace Local

variable {D : ℕ} [NeZero D]

theorem capInt_scale {Φ : HilbertVec D → ℝ} (hΦ : Continuous Φ) (α ε : ℝ) :
    capInt D ε (fun y => α * Φ y) = α * capInt D ε Φ := by
  have := capInt_lin hΦ hΦ hΦ α 0 0 ε
  simpa using this

theorem capInt_congr_sphere {Φ Ψ : HilbertVec D → ℝ} (h : ∀ y : Sph D, Φ y = Ψ y) (ε : ℝ) :
    capInt D ε Φ = capInt D ε Ψ := by
  unfold capInt
  simp only [h]

theorem capInt_finset_sum {ι : Type*} (s : Finset ι) {Φ : ι → HilbertVec D → ℝ}
    (hΦ : ∀ i, Continuous (Φ i)) (ε : ℝ) :
    capInt D ε (fun y => ∑ i ∈ s, Φ i y) = ∑ i ∈ s, capInt D ε (Φ i) := by
  unfold capInt
  have e : ∀ y : Sph D, (if Real.cos ε < inner ℝ (y : HilbertVec D) (pole D) then
      ∑ i ∈ s, Φ i y else 0) = ∑ i ∈ s, (if Real.cos ε < inner ℝ (y : HilbertVec D) (pole D)
      then Φ i y else 0) := by
    intro y
    split_ifs <;> simp
  simp_rw [e]
  exact integral_finsetSum _ fun i _ => integrable_cap (hΦ i) ε

theorem inner_pole_pole : inner ℝ (pole D) (pole D) = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_pole]; norm_num

theorem perp_cases {w : HilbertVec D} (hw : inner ℝ w (pole D) = 0) :
    w = 0 ∨ ∃ u : HilbertVec D, ‖u‖ = 1 ∧ inner ℝ u (pole D) = 0 ∧ w = ‖w‖ • u := by
  by_cases h : w = 0
  · exact Or.inl h
  · right
    have hn : 0 < ‖w‖ := norm_pos_iff.2 h
    refine ⟨‖w‖⁻¹ • w, ?_, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm]; exact inv_mul_cancel₀ hn.ne'
    · rw [inner_smul_left, hw]; simp
    · rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]

/-- Transverse second moments of unit vectors orthogonal to the pole are all `m_ε`. -/
theorem capInt_sq_perp (hD : 2 ≤ D) {u : HilbertVec D} (hu : ‖u‖ = 1)
    (hup : inner ℝ u (pole D) = 0) {ε : ℝ} (hε : 0 < ε) (hε' : ε < Real.pi) :
    capInt D ε (fun y => inner ℝ u y ^ 2) = capMom D ε := by
  have hcont : ∀ w : HilbertVec D, Continuous fun y : HilbertVec D => inner ℝ w y ^ 2 :=
    fun w => (continuous_const.inner continuous_id).pow 2
  have hbas : ∀ i : Fin D, i ≠ 0 →
      capInt D ε (fun y => inner ℝ (bas D i) y ^ 2) = capInt D ε (fun y => inner ℝ u y ^ 2) := by
    intro i hi
    have hpb : inner ℝ (pole D) (bas D i) = 0 := by
      rw [real_inner_comm]; exact inner_bas_pole hi
    obtain ⟨L, hLu, hLz⟩ := exists_swap hu (norm_bas (D := D) i)
    have hLe : L (pole D) = pole D := hLz _ (by rw [real_inner_comm, hup, hpb])
    rw [← capInt_comp hLe (hcont (bas D i)) ε]
    refine congrArg (capInt D ε) (funext fun y => ?_)
    rw [← hLu, LinearIsometryEquiv.inner_map_map]
  have hsum : capInt D ε (fun y => 1 - (inner ℝ y (pole D)) ^ 2) =
      ∑ i ∈ Finset.univ.erase (0 : Fin D), capInt D ε (fun y => inner ℝ (bas D i) y ^ 2) := by
    rw [← capInt_finset_sum _ (fun i => hcont (bas D i))]
    refine capInt_congr_sphere (fun y => ?_) ε
    have h1 := sum_sq_sphere y
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin D))] at h1
    have h2 : ∀ i : Fin D, inner ℝ (bas D i) (y : HilbertVec D) = (y : HilbertVec D) i := fun i => by
      rw [real_inner_comm, inner_bas]
    have h3 : inner ℝ (y : HilbertVec D) (pole D) = (y : HilbertVec D) 0 := inner_pole _
    simp only [h2, h3]
    linarith
  have hzon : capInt D ε (fun y => 1 - (inner ℝ y (pole D)) ^ 2) =
      sphereArea (D - 1) * ∫ φ in (0 : ℝ)..ε, Real.sin φ ^ D := by
    refine (integral_cap_zonal_eq hD (F := fun t : ℝ => 1 - t ^ 2) (by fun_prop) hε hε').trans ?_
    congr 1
    refine intervalIntegral.integral_congr fun φ _ => ?_
    obtain ⟨k, hk⟩ : ∃ k, D = k + 2 := ⟨D - 2, by omega⟩
    simp only [hk, Nat.add_sub_cancel]
    have : 1 - Real.cos φ ^ 2 = Real.sin φ ^ 2 := by rw [Real.sin_sq]
    rw [this]; ring
  rw [Finset.sum_congr rfl (fun i hi => hbas i (Finset.ne_of_mem_erase hi)), Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    at hsum
  have hD1 : ((D - 1 : ℕ) : ℝ) = (D : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hD2 : (0 : ℝ) < (D : ℝ) - 1 := by
    have : (2 : ℝ) ≤ D := by exact_mod_cast hD
    linarith
  rw [hzon, hD1] at hsum
  unfold capMom
  field_simp
  linarith

/-- The cross term vanishes by reflection. -/
theorem capInt_cross {u : HilbertVec D} (hu : ‖u‖ = 1) (hup : inner ℝ u (pole D) = 0) (ε : ℝ) :
    capInt D ε (fun y => (inner ℝ y (pole D) - 1) * inner ℝ u y) = 0 := by
  have hcont : Continuous fun y : HilbertVec D => (inner ℝ y (pole D) - 1) * inner ℝ u y :=
    ((continuous_id.inner continuous_const).sub continuous_const).mul
      (continuous_const.inner continuous_id)
  have hRe : reflection' u hu (pole D) = pole D := by
    rw [reflection'_apply, real_inner_comm, hup]; simp
  have h1 := capInt_comp hRe hcont ε
  have h2 : (fun y => (inner ℝ (reflection' u hu y) (pole D) - 1) *
      inner ℝ u (reflection' u hu y)) =
      fun y => (-1 : ℝ) * ((inner ℝ y (pole D) - 1) * inner ℝ u y) := by
    funext y
    have e1 : inner ℝ (reflection' u hu y) (pole D) = inner ℝ y (pole D) := by
      conv_lhs => rw [← hRe]
      exact LinearIsometryEquiv.inner_map_map _ _ _
    have e2 : inner ℝ u (reflection' u hu y) = - inner ℝ u y := by
      rw [reflection'_apply, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hu,
        real_inner_comm y u]
      ring
    rw [e1, e2]; ring
  rw [h2, capInt_scale hcont] at h1
  linarith

theorem capInt_cross_gen {w : HilbertVec D} (hw : inner ℝ w (pole D) = 0) (ε : ℝ) :
    capInt D ε (fun y => (inner ℝ y (pole D) - 1) * inner ℝ w y) = 0 := by
  rcases perp_cases hw with h | ⟨u, hu, hup, hwu⟩
  · subst h
    simp [capInt]
  · have hc : Continuous fun y : HilbertVec D => (inner ℝ y (pole D) - 1) * inner ℝ u y :=
      ((continuous_id.inner continuous_const).sub continuous_const).mul
        (continuous_const.inner continuous_id)
    have : (fun y : HilbertVec D => (inner ℝ y (pole D) - 1) * inner ℝ w y) =
        fun y => ‖w‖ * ((inner ℝ y (pole D) - 1) * inner ℝ u y) := by
      funext y
      conv_lhs => rw [hwu]
      rw [inner_smul_left]
      simp only [conj_trivial]
      ring
    rw [this, capInt_scale hc, capInt_cross hu hup, mul_zero]

theorem capInt_sq_gen (hD : 2 ≤ D) {w : HilbertVec D} (hw : inner ℝ w (pole D) = 0) {ε : ℝ}
    (hε : 0 < ε) (hε' : ε < Real.pi) :
    capInt D ε (fun y => inner ℝ w y ^ 2) = ‖w‖ ^ 2 * capMom D ε := by
  rcases perp_cases hw with h | ⟨u, hu, hup, hwu⟩
  · subst h
    simp [capInt]
  · have hc : Continuous fun y : HilbertVec D => inner ℝ u y ^ 2 :=
      (continuous_const.inner continuous_id).pow 2
    have : (fun y : HilbertVec D => inner ℝ w y ^ 2) =
        fun y => ‖w‖ ^ 2 * (inner ℝ u y ^ 2) := by
      funext y
      conv_lhs => rw [hwu]
      rw [inner_smul_left]
      simp only [conj_trivial]
      ring
    rw [this, capInt_scale hc, capInt_sq_perp hD hu hup hε hε']

theorem capInt_pole_moment (hD : 2 ≤ D) (v : HilbertVec D) {ε : ℝ} (hε : 0 < ε)
    (hε' : ε < Real.pi) :
    capInt D ε (fun y => inner ℝ v (y - pole D) ^ 2) =
      capMom D ε * (‖v‖ ^ 2 - inner ℝ v (pole D) ^ 2) + capMom' D ε * inner ℝ v (pole D) ^ 2 := by
  set a : ℝ := inner ℝ v (pole D) with ha
  set w : HilbertVec D := v - a • pole D with hwdef
  have hw : inner ℝ w (pole D) = 0 := by
    rw [hwdef, inner_sub_left, inner_smul_left, inner_pole_pole, ← ha]; simp
  have hnorm : ‖v‖ ^ 2 = a ^ 2 + ‖w‖ ^ 2 := by
    have : ‖w‖ ^ 2 = ‖v‖ ^ 2 - 2 * a * a + a ^ 2 := by
      rw [hwdef, norm_sub_sq_real, norm_smul, inner_smul_right, ← ha, mul_pow, norm_pole,
        Real.norm_eq_abs, sq_abs]
      ring
    linarith
  have hpt : ∀ y : HilbertVec D, inner ℝ v (y - pole D) ^ 2 =
      a ^ 2 * (inner ℝ y (pole D) - 1) ^ 2 + (2 * a) * ((inner ℝ y (pole D) - 1) * inner ℝ w y) +
        1 * inner ℝ w y ^ 2 := by
    intro y
    have hv : v = w + a • pole D := by rw [hwdef]; abel
    have hvy : inner ℝ v y = inner ℝ w y + a * inner ℝ y (pole D) := by
      conv_lhs => rw [hv]
      rw [inner_add_left, inner_smul_left, real_inner_comm y (pole D)]
      simp only [conj_trivial]
    have e : inner ℝ v (y - pole D) = a * (inner ℝ y (pole D) - 1) + inner ℝ w y := by
      rw [inner_sub_right, hvy, ← ha]
      ring
    rw [e]; ring
  have c1 : Continuous fun y : HilbertVec D => (inner ℝ y (pole D) - 1) ^ 2 :=
    ((continuous_id.inner continuous_const).sub continuous_const).pow 2
  have c2 : Continuous fun y : HilbertVec D => (inner ℝ y (pole D) - 1) * inner ℝ w y :=
    ((continuous_id.inner continuous_const).sub continuous_const).mul
      (continuous_const.inner continuous_id)
  have c3 : Continuous fun y : HilbertVec D => inner ℝ w y ^ 2 :=
    (continuous_const.inner continuous_id).pow 2
  simp_rw [hpt]
  rw [capInt_lin c1 c2 c3, capInt_cross_gen hw, capInt_sq_gen hD hw hε hε']
  have hz : capInt D ε (fun y => (inner ℝ y (pole D) - 1) ^ 2) = capMom' D ε := by
    refine (integral_cap_zonal_eq hD (F := fun t : ℝ => (t - 1) ^ 2) (by fun_prop) hε hε').trans ?_
    unfold capMom'
    congr 1
    refine intervalIntegral.integral_congr fun φ _ => ?_
    ring
  rw [hz, hnorm]
  ring

end Local

open Local

/-- The cap second moment `m'_ε` is `capMom'` and the cap second moment identity holds about
any point `x` of the sphere. -/
theorem cap_second_moment {D : ℕ} (hD : 2 ≤ D) [NeZero D] (x : Sph D) (v : HilbertVec D) {ε : ℝ}
    (hε : 0 < ε) (hε' : ε < Real.pi) :
    ∫ y : Sph D, (if Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D) then
        inner ℝ v ((y : HilbertVec D) - x) ^ 2 else 0) ∂(sphMeasure D) =
      capMom D ε * (‖v‖ ^ 2 - inner ℝ v (x : HilbertVec D) ^ 2) +
        capMom' D ε * inner ℝ v (x : HilbertVec D) ^ 2 := by
  have hx : ‖(x : HilbertVec D)‖ = 1 := by simp
  obtain ⟨L, hLx, -⟩ := exists_swap hx (norm_pole D)
  have hmeas : Measurable fun y : Sph D =>
      if Real.cos ε < inner ℝ (y : HilbertVec D) (pole D) then
        inner ℝ (L v) ((y : HilbertVec D) - pole D) ^ 2 else 0 :=
    Measurable.ite (measurableSet_cap ε)
      ((((continuous_const.inner (continuous_subtype_val.sub continuous_const))).pow 2).measurable)
      measurable_const
  have h1 := integral_comp_sphMap L hmeas.aestronglyMeasurable
  have h2 := capInt_pole_moment hD (L v) hε hε'
  have hn : ‖L v‖ = ‖v‖ := L.norm_map v
  have hi : inner ℝ (L v) (pole D) = inner ℝ v (x : HilbertVec D) := by
    rw [← hLx]; exact LinearIsometryEquiv.inner_map_map _ _ _
  rw [hn, hi] at h2
  refine Eq.trans ?_ (h1.trans h2)
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [coe_sphMap, ← hLx, ← map_sub, LinearIsometryEquiv.inner_map_map,
    real_inner_comm (x : HilbertVec D) (y : HilbertVec D)]

end

end PDE.FHLane
