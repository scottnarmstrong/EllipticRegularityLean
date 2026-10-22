module

public import PDEFoundation.Monotonicity.FriedlandHayman.Local.CapAsymp
public import PDEFoundation.Monotonicity.FriedlandHayman.Symm.Polarization
public import PDEFoundation.Monotonicity.FriedlandHayman.Symm.Split

/-!
# Friedland--Hayman: cap integrals about the pole and symmetry tools

The cap integral `capInt ε Φ = ∫_{cos ε < ⟪y, e₀⟫} Φ(y) dσ(y)`, its linearity, its invariance
under isometries fixing the pole, the isometry swapping two unit vectors, and the coordinate unit
vectors `bas i`.
-/

@[expose] public section

open MeasureTheory

namespace PDE.FHLane

noncomputable section

namespace Local

variable {D : ℕ} [NeZero D]

/-- The integral over the cap of angular radius `ε` about the pole. -/
def capInt (D : ℕ) [NeZero D] (ε : ℝ) (Φ : HilbertVec D → ℝ) : ℝ :=
  ∫ y : Sph D, (if Real.cos ε < inner ℝ (y : HilbertVec D) (pole D) then Φ y else 0)
    ∂(sphMeasure D)

theorem measurableSet_cap (ε : ℝ) :
    MeasurableSet {y : Sph D | Real.cos ε < inner ℝ (y : HilbertVec D) (pole D)} :=
  (isOpen_lt continuous_const (continuous_subtype_val.inner continuous_const)).measurableSet

theorem integrable_cap {Φ : HilbertVec D → ℝ} (hΦ : Continuous Φ) (ε : ℝ) :
    Integrable (fun y : Sph D => if Real.cos ε < inner ℝ (y : HilbertVec D) (pole D) then Φ y
      else 0) (sphMeasure D) := by
  have h := (Symm.integrable_of_continuous (F := fun y : Sph D => Φ y)
    (hΦ.comp continuous_subtype_val)).indicator (measurableSet_cap (D := D) ε)
  refine h.congr (ae_of_all _ fun y => ?_)
  by_cases hy : Real.cos ε < inner ℝ (y : HilbertVec D) (pole D)
  · simp [hy]
  · simp [hy]

theorem capInt_lin {Φ₁ Φ₂ Φ₃ : HilbertVec D → ℝ} (h₁ : Continuous Φ₁) (h₂ : Continuous Φ₂)
    (h₃ : Continuous Φ₃) (α β γ ε : ℝ) :
    capInt D ε (fun y => α * Φ₁ y + β * Φ₂ y + γ * Φ₃ y) =
      α * capInt D ε Φ₁ + β * capInt D ε Φ₂ + γ * capInt D ε Φ₃ := by
  unfold capInt
  have e : ∀ y : Sph D, (if Real.cos ε < inner ℝ (y : HilbertVec D) (pole D) then
      α * Φ₁ y + β * Φ₂ y + γ * Φ₃ y else 0) =
      α * (if Real.cos ε < inner ℝ (y : HilbertVec D) (pole D) then Φ₁ y else 0) +
      β * (if Real.cos ε < inner ℝ (y : HilbertVec D) (pole D) then Φ₂ y else 0) +
      γ * (if Real.cos ε < inner ℝ (y : HilbertVec D) (pole D) then Φ₃ y else 0) := by
    intro y
    split_ifs <;> simp
  simp_rw [e]
  set c₁ : Sph D → ℝ := fun y => if Real.cos ε < inner ℝ (y : HilbertVec D) (pole D) then Φ₁ y
    else 0 with hc₁
  set c₂ : Sph D → ℝ := fun y => if Real.cos ε < inner ℝ (y : HilbertVec D) (pole D) then Φ₂ y
    else 0 with hc₂
  set c₃ : Sph D → ℝ := fun y => if Real.cos ε < inner ℝ (y : HilbertVec D) (pole D) then Φ₃ y
    else 0 with hc₃
  have i₁ : Integrable (fun y => α * c₁ y) (sphMeasure D) := (integrable_cap h₁ ε).const_mul α
  have i₂ : Integrable (fun y => β * c₂ y) (sphMeasure D) := (integrable_cap h₂ ε).const_mul β
  have i₃ : Integrable (fun y => γ * c₃ y) (sphMeasure D) := (integrable_cap h₃ ε).const_mul γ
  have i₁₂ : Integrable (fun y => α * c₁ y + β * c₂ y) (sphMeasure D) := i₁.add i₂
  rw [integral_add i₁₂ i₃, integral_add i₁ i₂, integral_const_mul, integral_const_mul,
    integral_const_mul]

theorem capInt_comp {L : HilbertVec D ≃ₗᵢ[ℝ] HilbertVec D} (hL : L (pole D) = pole D)
    {Φ : HilbertVec D → ℝ} (hΦ : Continuous Φ) (ε : ℝ) :
    capInt D ε (fun y => Φ (L y)) = capInt D ε Φ := by
  unfold capInt
  have hm : Measurable fun y : Sph D => if Real.cos ε < inner ℝ (y : HilbertVec D) (pole D)
      then Φ y else 0 :=
    Measurable.ite (measurableSet_cap ε) (hΦ.comp continuous_subtype_val).measurable
      measurable_const
  rw [← integral_comp_sphMap L hm.aestronglyMeasurable]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  have : inner ℝ (L (y : HilbertVec D)) (pole D) = inner ℝ (y : HilbertVec D) (pole D) := by
    conv_lhs => rw [← hL]
    exact LinearIsometryEquiv.inner_map_map _ _ _
  simp only [coe_sphMap, this]

theorem integral_cap_zonal_eq {D : ℕ} (hD : 2 ≤ D) [NeZero D] {F : ℝ → ℝ} (hF : Continuous F)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < Real.pi) :
    capInt D ε (fun y => F (inner ℝ y (pole D))) =
      sphereArea (D - 1) * ∫ φ in (0 : ℝ)..ε, F (Real.cos φ) * Real.sin φ ^ (D - 2) :=
  integral_cap_zonal hD hF hε hε'

omit [NeZero D] in
/-- An isometry exchanging two unit vectors and fixing everything orthogonal to their
difference. -/
theorem exists_swap {x y : HilbertVec D} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∃ L : HilbertVec D ≃ₗᵢ[ℝ] HilbertVec D, L x = y ∧
      ∀ z, inner ℝ z x = inner ℝ z y → L z = z := by
  by_cases hxy : x = y
  · exact ⟨LinearIsometryEquiv.refl ℝ _, by simp [hxy], fun z _ => rfl⟩
  · have hn : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
    set n := ‖x - y‖ with hndef
    set u : HilbertVec D := n⁻¹ • (x - y) with hudef
    have hu : ‖u‖ = 1 := by
      rw [hudef, norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ hn.ne'
    refine ⟨reflection' u hu, ?_, ?_⟩
    · rw [reflection'_apply]
      have hn2 : n ^ 2 = 2 - 2 * inner ℝ x y := by
        rw [hndef, norm_sub_sq_real, hx, hy]; ring
      have hxu : inner ℝ x u = n⁻¹ * (1 - inner ℝ x y) := by
        rw [hudef, inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq, hx]
        ring
      have h1 : 2 * inner ℝ x u * n⁻¹ = 1 := by
        rw [hxu]
        field_simp
        linarith
      rw [hudef, smul_smul, h1, one_smul]
      abel
    · intro z hz
      rw [reflection'_apply]
      have : inner ℝ z u = 0 := by
        rw [hudef, inner_smul_right, inner_sub_right, hz]; simp
      simp [this]

/-- The `i`-th coordinate unit vector. -/
def bas (D : ℕ) (i : Fin D) : HilbertVec D := Vec.toHilbertVec (Pi.single i 1 : Vec D)

omit [NeZero D] in
theorem inner_bas (y : HilbertVec D) (i : Fin D) : inner ℝ y (bas D i) = y i := by
  rw [PiLp.inner_apply, Finset.sum_eq_single i]
  · simp [bas]
  · intro b _ hb
    simp [bas, hb]
  · simp

omit [NeZero D] in
theorem norm_bas (i : Fin D) : ‖bas D i‖ = 1 := by
  rw [PiLp.norm_eq_of_L2, Real.sqrt_eq_one, Finset.sum_eq_single i]
  · simp [bas]
  · intro b _ hb
    simp [bas, hb]
  · simp

theorem bas_zero : bas D 0 = pole D := rfl

theorem inner_bas_pole {i : Fin D} (hi : i ≠ 0) : inner ℝ (bas D i) (pole D) = 0 := by
  rw [← bas_zero, inner_bas]
  simp [bas, hi.symm]

omit [NeZero D] in
theorem sum_sq_sphere (y : Sph D) : ∑ i : Fin D, ((y : HilbertVec D) i) ^ 2 = 1 := by
  have h : ‖(y : HilbertVec D)‖ ^ 2 = 1 := by simp
  rw [PiLp.norm_sq_eq_of_L2] at h
  simpa using h

end Local

end

end PDE.FHLane
