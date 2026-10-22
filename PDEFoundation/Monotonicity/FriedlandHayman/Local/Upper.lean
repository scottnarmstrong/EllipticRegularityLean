module

public import PDEFoundation.Monotonicity.FriedlandHayman.Local.UpperAbs
public import PDEFoundation.Monotonicity.FriedlandHayman.Local.Taylor

/-!
# Friedland--Hayman: the upper local limit of the nonlocal energy

For a `C¹` function `f`, `limsup_{ε → 0} E_ε(f) / m_ε ≤ ∫_{S^{D-1}} |∇_T f|²`, stated as
`E_ε(f|_S) ≤ (∫ |∇_T f|² + η) m_ε` for all small `ε`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PDE.FHLane

noncomputable section

/-- The restriction of an ambient function to the sphere. -/
def sphRestrict {D : ℕ} (f : Vec D → ℝ) (hf : Continuous f) : C(Sph D, ℝ) :=
  ⟨fun ω => f (ω : HilbertVec D).toVec, hf.comp (continuous_toVec.comp continuous_subtype_val)⟩

namespace Local

variable {D : ℕ}

theorem sq_bound {a r n M η : ℝ} (hn : 0 ≤ n) (ha : |a| ≤ M * n) (hr : |r| ≤ η * n) (hM : 0 ≤ M) :
    (a + r) ^ 2 ≤ a ^ 2 + (2 * M * η + η ^ 2) * n ^ 2 := by
  have h1 : a * r ≤ (M * n) * (η * n) :=
    calc a * r ≤ |a * r| := le_abs_self _
      _ = |a| * |r| := abs_mul _ _
      _ ≤ (M * n) * (η * n) := mul_le_mul ha hr (abs_nonneg _) (by positivity)
  have h2 : r ^ 2 ≤ (η * n) ^ 2 :=
    calc r ^ 2 = |r| ^ 2 := (sq_abs r).symm
      _ ≤ (η * n) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hr 2
  nlinarith

theorem choose_eta {M S Dd η : ℝ} (hM : 0 ≤ M) (hS : 0 ≤ S) (hD : 0 ≤ Dd) (hη : 0 < η) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ (2 * M * t + t ^ 2) * S * Dd ≤ η / 2 := by
  set K : ℝ := (2 * M + 1) * S * Dd + 1 with hK
  have hK0 : 0 < K := by positivity
  refine ⟨min 1 (η / (2 * K)), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  set t := min 1 (η / (2 * K)) with ht
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht0 : 0 ≤ t := (lt_min one_pos (by positivity)).le
  have ht2 : t ≤ η / (2 * K) := min_le_right _ _
  have h1 : 2 * M * t + t ^ 2 ≤ (2 * M + 1) * t := by nlinarith
  have h2 : t * K ≤ η / 2 := by
    calc t * K ≤ η / (2 * K) * K := by gcongr
      _ = η / 2 := by field_simp
  calc (2 * M * t + t ^ 2) * S * Dd ≤ (2 * M + 1) * t * S * Dd := by gcongr
    _ = t * ((2 * M + 1) * S * Dd) := by ring
    _ ≤ t * K := by gcongr; linarith
    _ ≤ η / 2 := h2

theorem final_arith {m m' q M2 κ S Dm1 η : ℝ} (hm : 0 < m) (hq : m' ≤ q * m) (hq1 : q ≤ 1)
    (hM2 : 0 ≤ M2) (hκ : 0 ≤ κ) (hS : 0 ≤ S)
    (h1 : q * (M2 * S) ≤ η / 2) (h2 : κ * S * (Dm1 + 1) ≤ η / 2) :
    (m' * M2 + κ * (Dm1 * m + m')) * S ≤ η * m := by
  have e1 : m' * M2 * S ≤ q * m * M2 * S := by gcongr
  have e2 : κ * S * m' ≤ κ * S * (q * m) := by gcongr
  have e3 : m * (κ * S * (Dm1 + q)) ≤ m * (κ * S * (Dm1 + 1)) := by gcongr
  have e4 : m * (q * (M2 * S)) ≤ m * (η / 2) := by gcongr
  have e5 : m * (κ * S * (Dm1 + 1)) ≤ m * (η / 2) := by gcongr
  nlinarith

theorem tgn_eq (f : Vec D → ℝ) (x : Sph D) :
    tangentialGradientNormSq f (x : HilbertVec D).toVec =
      ‖gradH f x‖ ^ 2 - inner ℝ (gradH f x) (x : HilbertVec D) ^ 2 := by
  unfold tangentialGradientNormSq
  have h1 : vecNormSq (classicalGradient f (x : HilbertVec D).toVec) = ‖gradH f x‖ ^ 2 := by
    rw [← vecEuclideanNorm_sq, Vec.vecEuclideanNorm_eq_norm_toHilbertVec]; rfl
  have h2 : vecDot (classicalGradient f (x : HilbertVec D).toVec) (x : HilbertVec D).toVec =
      inner ℝ (gradH f x) (x : HilbertVec D) := by
    rw [vecDot_comm]
    exact (inner_toHilbertVec (classicalGradient f (x : HilbertVec D).toVec)
      (x : HilbertVec D).toVec).symm
  rw [h1, h2]

theorem continuous_gradH {f : Vec D → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (gradH f) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin D => ℝ)).comp
    ((PDE.ContDiff.continuous_classicalGradient hf).comp
      (continuous_toVec.comp continuous_subtype_val))

theorem norm_sub_lt {x y : Sph D} {ε : ℝ} (hε : 0 < ε)
    (h : Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D)) :
    ‖(y : HilbertVec D) - x‖ < ε := by
  have hx : ‖(x : HilbertVec D)‖ = 1 := by simp
  have hy : ‖(y : HilbertVec D)‖ = 1 := by simp
  have h1 : ‖(y : HilbertVec D) - x‖ ^ 2 = 2 - 2 * inner ℝ (x : HilbertVec D) (y : HilbertVec D) := by
    rw [norm_sub_sq_real, hx, hy, real_inner_comm]; ring
  have h2 := Real.one_sub_sq_div_two_le_cos (x := ε)
  have h3 : ‖(y : HilbertVec D) - x‖ ^ 2 < ε ^ 2 := by nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 hε.le h3

end Local

open Local

/-- Upper local limit: `limsup_{ε → 0} E_ε(f) / m_ε ≤ ∫ |∇_T f|²`. -/
theorem nlEnergy_le_tgn {D : ℕ} (hD : 2 ≤ D) [NeZero D] {f : Vec D → ℝ} (hf : ContDiff ℝ 1 f)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), nlEnergy ε (sphRestrict f hf.continuous) ≤
      (sphereIntegral (0 : Vec D) 1 (tangentialGradientNormSq f) + η) * capMom D ε := by
  have hgc := continuous_gradH hf
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Sph D)).exists_bound_of_continuousOn
    hgc.norm.continuousOn
  set M : ℝ := max C 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ x : Sph D, ‖gradH f x‖ ≤ M := fun x => by
    have h := hC x (Set.mem_univ x)
    rw [norm_norm] at h
    exact h.trans (le_max_left _ _)
  set S : ℝ := (sphMeasure D).real Set.univ with hSdef
  have hS0 : 0 ≤ S := measureReal_nonneg
  have hDd : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  obtain ⟨t, ht0, ht1, hκS⟩ := choose_eta (M := M) (S := S) (Dd := (D : ℝ)) hM0 hS0 hDd hη
  obtain ⟨δ, hδ, -, hT⟩ := taylor_sph hf ht0
  set κ : ℝ := 2 * M * t + t ^ 2 with hκdef
  have hκ0 : 0 ≤ κ := by positivity
  set q₀ : ℝ := min 1 (η / (2 * (M ^ 2 * S + 1))) with hq₀
  have hq₀pos : 0 < q₀ := lt_min one_pos (by positivity)
  have hq₀1 : q₀ ≤ 1 := min_le_left _ _
  have hq₀2 : q₀ ≤ η / (2 * (M ^ 2 * S + 1)) := min_le_right _ _
  have hev1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Set.Ioo (0 : ℝ) (min δ (Real.pi / 2)) :=
    Ioo_mem_nhdsGT (lt_min hδ (by positivity [Real.pi_pos]))
  have hev2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), capMom' D ε / capMom D ε < q₀ :=
    (tendsto_capMom'_div_capMom hD).eventually (gt_mem_nhds hq₀pos)
  filter_upwards [hev1, hev2] with ε hε hr
  have hε0 := hε.1
  have hεδ : ε < δ := lt_of_lt_of_le hε.2 (min_le_left _ _)
  have hεπ : ε < Real.pi := by
    have := lt_of_lt_of_le hε.2 (min_le_right _ _); linarith [Real.pi_pos]
  have hm := capMom_pos hD hε0 hεπ
  have hpt : ∀ x y : Sph D, Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D) →
      (sphRestrict f hf.continuous x - sphRestrict f hf.continuous y) ^ 2 ≤
        inner ℝ (gradH f x) ((y : HilbertVec D) - x) ^ 2 + κ * ‖(y : HilbertVec D) - x‖ ^ 2 := by
    intro x y hxy
    have hn := norm_sub_lt hε0 hxy
    have h1 := hT x y (hn.trans hεδ)
    have h2 : |inner ℝ (gradH f x) ((y : HilbertVec D) - x)| ≤ M * ‖(y : HilbertVec D) - x‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _))
    have h3 := sq_bound (norm_nonneg _) h2 h1 hM0
    have e : (sphRestrict f hf.continuous x - sphRestrict f hf.continuous y) ^ 2 =
        (inner ℝ (gradH f x) ((y : HilbertVec D) - x) +
          (f (y : HilbertVec D).toVec - f (x : HilbertVec D).toVec -
            inner ℝ (gradH f x) ((y : HilbertVec D) - x))) ^ 2 := by
      show (f (x : HilbertVec D).toVec - f (y : HilbertVec D).toVec) ^ 2 = _
      ring
    rw [e]
    exact h3
  have hmain := nlEnergy_le_of_pointwise hD (sphRestrict f hf.continuous) (gradH f) hgc
    (κ := κ) (M := M) hε0 hεπ hM hpt
  have hI : ∫ x : Sph D, (‖gradH f x‖ ^ 2 - inner ℝ (gradH f x) (x : HilbertVec D) ^ 2)
      ∂(sphMeasure D) = sphereIntegral (0 : Vec D) 1 (tangentialGradientNormSq f) := by
    unfold sphereIntegral
    simp only [one_pow, one_mul, zero_add, one_smul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    exact (tgn_eq f x).symm
  rw [hI] at hmain
  have hq : capMom' D ε ≤ q₀ * capMom D ε := by
    rw [div_lt_iff₀ hm] at hr
    exact hr.le
  have hfin := final_arith (m := capMom D ε) (m' := capMom' D ε) (q := q₀) (M2 := M ^ 2) (κ := κ)
    (S := S) (Dm1 := (D : ℝ) - 1) (η := η) hm hq hq₀1 (by positivity) hκ0 hS0
    (by
      calc q₀ * (M ^ 2 * S) ≤ η / (2 * (M ^ 2 * S + 1)) * (M ^ 2 * S) := by gcongr
        _ ≤ η / (2 * (M ^ 2 * S + 1)) * (M ^ 2 * S + 1) := by gcongr; linarith
        _ = η / 2 := by field_simp)
    (by
      have : (D : ℝ) - 1 + 1 = D := by ring
      rw [this]; exact hκS)
  calc nlEnergy ε (sphRestrict f hf.continuous) ≤ _ := hmain
    _ ≤ _ := by nlinarith [hfin]

end

end PDE.FHLane
