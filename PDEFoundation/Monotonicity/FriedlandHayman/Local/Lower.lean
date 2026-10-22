module

public import PDEFoundation.Monotonicity.FriedlandHayman.Local.LowerPointwise
public import Mathlib.Analysis.BoundedVariation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Friedland--Hayman: the lower local limit for Lipschitz zonal functions

For `k = h ∘ arccos ⟪·, e₀⟫` with `h` Lipschitz, `liminf_{ε → 0} E_ε(k) / m_ε` is at least
`σ_{D-2} ∫_0^π h'² sin^{D-2}`.  The pointwise limit is `inner_energy_ge` at the points where `h`
is differentiable at the angle (almost every point of the sphere, by Rademacher in one variable
and the zonal formula), and Fatou's lemma along the filter `ε → 0+` finishes.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PDE.FHLane

noncomputable section

namespace Local

variable {D : ℕ}

/-- The inner energy at `x`. -/
def innerEnergy (ε : ℝ) (k : C(Sph D, ℝ)) (x : Sph D) : ℝ :=
  ∫ y : Sph D, (if Real.cos ε < inner ℝ (x : HilbertVec D) (y : HilbertVec D) then
    (k x - k y) ^ 2 else 0) ∂(sphMeasure D)

theorem innerEnergy_nonneg (ε : ℝ) (k : C(Sph D, ℝ)) (x : Sph D) : 0 ≤ innerEnergy ε k x :=
  integral_nonneg fun y => by split_ifs <;> positivity

theorem nlEnergy_eq_integral (ε : ℝ) (k : C(Sph D, ℝ)) :
    nlEnergy ε k = ∫ x, innerEnergy ε k x ∂(sphMeasure D) := rfl

theorem measurable_innerEnergy (ε : ℝ) (k : C(Sph D, ℝ)) : Measurable (innerEnergy ε k) :=
  (Symm.measurable_kern ε k).stronglyMeasurable.integral_prod_right'.measurable

theorem integrable_innerEnergy (ε : ℝ) (k : C(Sph D, ℝ)) :
    Integrable (innerEnergy ε k) (sphMeasure D) := by
  have h : Integrable (fun p : Sph D × Sph D => Symm.kern ε k p.1 p.2)
      ((sphMeasure D).prod (sphMeasure D)) :=
    Symm.integrable_of_bdd (Symm.measurable_kern ε k) fun p => Symm.abs_kern_le ε k p.1 p.2
  exact h.integral_prod_left

theorem nlEnergy_nonneg (ε : ℝ) (k : C(Sph D, ℝ)) : 0 ≤ nlEnergy ε k :=
  integral_nonneg (innerEnergy_nonneg ε k)

/-- Almost every point of the sphere is a point where `h` is differentiable at the polar
angle. -/
theorem ae_differentiableAt_angle (hD : 2 ≤ D) [NeZero D] {h : ℝ → ℝ} {K : NNReal}
    (hh : LipschitzWith K h) :
    ∀ᵐ x : Sph D ∂(sphMeasure D), inner ℝ (x : HilbertVec D) (pole D) ∈ Set.Ioo (-1 : ℝ) 1 ∧
      DifferentiableAt ℝ h (Real.arccos (inner ℝ (x : HilbertVec D) (pole D))) := by
  set S : Set ℝ := {t | t ∈ Set.Ioo (-1 : ℝ) 1 ∧ DifferentiableAt ℝ h (Real.arccos t)} with hS
  have hSm : MeasurableSet S :=
    measurableSet_Ioo.inter
      ((measurableSet_of_differentiableAt ℝ h).preimage Real.continuous_arccos.measurable)
  set G : ℝ → ℝ := Sᶜ.indicator (fun _ => (1 : ℝ)) with hG
  have hGm : Measurable G := measurable_const.indicator hSm.compl
  have hGb : ∃ C, ∀ t, |G t| ≤ C := ⟨1, fun t => by
    by_cases ht : t ∈ Sᶜ
    · simp [hG, ht]
    · simp [hG, ht]⟩
  have hz := integral_zonal hD G hGm hGb
  have h0 : ∫ φ in (0 : ℝ)..Real.pi, G (Real.cos φ) * Real.sin φ ^ (D - 2) = 0 := by
    have hae : ∀ᵐ φ : ℝ, φ ∈ Set.uIoc 0 Real.pi → G (Real.cos φ) * Real.sin φ ^ (D - 2) = 0 := by
      filter_upwards [LipschitzWith.ae_differentiableAt_real hh,
        (Set.toFinite ({0, Real.pi} : Set ℝ)).countable.ae_notMem volume] with φ hφ hne hmem
      rw [Set.uIoc_of_le Real.pi_pos.le] at hmem
      have hφ0 : 0 < φ := hmem.1
      have hφπ : φ < Real.pi := lt_of_le_of_ne hmem.2 fun h' => hne (by simp [h'])
      have hcS : Real.cos φ ∈ S := by
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · have := Real.cos_lt_cos_of_nonneg_of_le_pi hφ0.le le_rfl hφπ
          rw [Real.cos_pi] at this; exact this
        · have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hφπ.le hφ0
          rw [Real.cos_zero] at this; exact this
        · rw [Real.arccos_cos hφ0.le hφπ.le]; exact hφ
      have : G (Real.cos φ) = 0 := by
        simp [hG, Set.indicator_of_notMem (fun h' : Real.cos φ ∈ Sᶜ => h' hcS)]
      rw [this, zero_mul]
    rw [intervalIntegral.integral_congr_ae hae]
    simp
  rw [h0, mul_zero] at hz
  have hGi : Integrable (fun x : Sph D => G (inner ℝ (x : HilbertVec D) (pole D))) (sphMeasure D) := by
    obtain ⟨C, hC⟩ := hGb
    exact Symm.integrable_of_bdd (hGm.comp
      (continuous_subtype_val.inner continuous_const).measurable) fun x => hC _
  have hnn : 0 ≤ fun x : Sph D => G (inner ℝ (x : HilbertVec D) (pole D)) := fun x => by
    by_cases ht : inner ℝ (x : HilbertVec D) (pole D) ∈ Sᶜ
    · simp [hG, ht]
    · simp [hG, ht]
  have := (integral_eq_zero_iff_of_nonneg hnn hGi).1 hz
  filter_upwards [this] with x hx
  by_contra hS'
  have : G (inner ℝ (x : HilbertVec D) (pole D)) = 1 := by
    simp [hG, Set.indicator_of_mem (show inner ℝ (x : HilbertVec D) (pole D) ∈ Sᶜ from hS')]
  simp [this] at hx

theorem hasDerivAt_height {h : ℝ → ℝ} {a : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : DifferentiableAt ℝ h (Real.arccos a)) :
    HasDerivAt (fun s => h (Real.arccos s)) (deriv h (Real.arccos a) * (-(1 / √(1 - a ^ 2)))) a :=
  HasDerivAt.comp a hd.hasDerivAt (Real.hasDerivAt_arccos ha.1.ne' ha.2.ne)

theorem deriv_height_sq {t a : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1) :
    (t * (-(1 / √(1 - a ^ 2)))) ^ 2 * (1 - a ^ 2) = t ^ 2 := by
  have h1 : 0 < 1 - a ^ 2 := by nlinarith [ha.1, ha.2]
  have h2 : √(1 - a ^ 2) ^ 2 = 1 - a ^ 2 := Real.sq_sqrt h1.le
  have h3 : √(1 - a ^ 2) ≠ 0 := (Real.sqrt_pos.2 h1).ne'
  field_simp
  rw [h2]

theorem ofReal_le_liminf_inner (hD : 2 ≤ D) [NeZero D] (k : C(Sph D, ℝ)) {h : ℝ → ℝ}
    (hk : ∀ x : Sph D, k x = h (Real.arccos (inner ℝ (x : HilbertVec D) (pole D)))) (x : Sph D)
    (hx1 : inner ℝ (x : HilbertVec D) (pole D) ∈ Set.Ioo (-1 : ℝ) 1)
    (hxd : DifferentiableAt ℝ h (Real.arccos (inner ℝ (x : HilbertVec D) (pole D)))) :
    ENNReal.ofReal (deriv h (Real.arccos (inner ℝ (x : HilbertVec D) (pole D))) ^ 2) ≤
      liminf (fun ε => ENNReal.ofReal (innerEnergy ε k x / capMom D ε)) (𝓝[>] (0 : ℝ)) := by
  set ψ : ℝ := deriv h (Real.arccos (inner ℝ (x : HilbertVec D) (pole D))) ^ 2 with hψ
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  have hη' : (0 : ℝ) < η := NNReal.coe_pos.2 hη
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (ψ - η) ≤ ENNReal.ofReal (innerEnergy ε k x / capMom D ε) := by
    filter_upwards [inner_energy_ge hD k x (hasDerivAt_height hx1 hxd) hk hη',
      Ioo_mem_nhdsGT Real.pi_pos] with ε h1 hε
    refine ENNReal.ofReal_le_ofReal ?_
    have hm := capMom_pos hD hε.1 hε.2
    rw [le_div_iff₀ hm]
    rw [deriv_height_sq hx1] at h1
    exact h1
  have h1 := le_liminf_of_le (by isBoundedDefault) hev
  calc ENNReal.ofReal ψ = ENNReal.ofReal ((ψ - η) + η) := by rw [sub_add_cancel]
    _ ≤ ENNReal.ofReal (ψ - η) + ENNReal.ofReal η := ENNReal.ofReal_add_le
    _ ≤ _ := by
        rw [ENNReal.ofReal_coe_nnreal]
        gcongr

end Local

open Local

/-- F4d2: lower local limit for Lipschitz zonal functions. -/
theorem nlEnergy_ge_zonal {D : ℕ} (hD : 2 ≤ D) [NeZero D] (k : C(Sph D, ℝ)) {h : ℝ → ℝ} {K : NNReal}
    (hh : LipschitzWith K h) (hk : ∀ x : Sph D, k x = h (Real.arccos (inner ℝ (x : HilbertVec D) (pole D))))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      (sphereArea (D - 1) * (∫ φ in (0 : ℝ)..Real.pi, deriv h φ ^ 2 * Real.sin φ ^ (D - 2)) - η) *
          capMom D ε ≤ nlEnergy ε k := by
  set G : ℝ → ℝ := fun t => deriv h (Real.arccos t) ^ 2 with hG
  have hGm : Measurable G := ((measurable_deriv h).comp Real.continuous_arccos.measurable).pow_const 2
  have hGb : ∃ C, ∀ t, |G t| ≤ C := ⟨(K : ℝ) ^ 2, fun t => by
    rw [hG, abs_of_nonneg (sq_nonneg _)]
    have := norm_deriv_le_of_lipschitz (𝕜 := ℝ) (x₀ := Real.arccos t) hh
    rw [Real.norm_eq_abs] at this
    calc deriv h (Real.arccos t) ^ 2 = |deriv h (Real.arccos t)| ^ 2 := (sq_abs _).symm
      _ ≤ (K : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2⟩
  set ψ : Sph D → ℝ := fun x => G (inner ℝ (x : HilbertVec D) (pole D)) with hψ
  have hψm : Measurable ψ := hGm.comp (continuous_subtype_val.inner continuous_const).measurable
  have hψi : Integrable ψ (sphMeasure D) := by
    obtain ⟨C, hC⟩ := hGb
    exact Symm.integrable_of_bdd hψm fun x => hC _
  have hψnn : 0 ≤ᵐ[sphMeasure D] ψ := ae_of_all _ fun x => sq_nonneg _
  set A : ℝ := sphereArea (D - 1) * (∫ φ in (0 : ℝ)..Real.pi, deriv h φ ^ 2 * Real.sin φ ^ (D - 2))
    with hA
  have hAψ : ∫ x, ψ x ∂(sphMeasure D) = A := by
    refine (integral_zonal hD G hGm hGb).trans ?_
    congr 1
    refine intervalIntegral.integral_congr fun φ hφ => ?_
    rw [Set.uIcc_of_le Real.pi_pos.le] at hφ
    simp only [hG, Real.arccos_cos hφ.1 hφ.2]
  have hev0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Set.Ioo (0 : ℝ) Real.pi := Ioo_mem_nhdsGT Real.pi_pos
  -- Fatou
  have hF := lintegral_liminf_le (μ := sphMeasure D) (u := 𝓝[>] (0 : ℝ))
    (f := fun ε x => ENNReal.ofReal (innerEnergy ε k x / capMom D ε))
    (fun ε => ((measurable_innerEnergy ε k).div_const _).ennreal_ofReal)
  have hL : ENNReal.ofReal A ≤ liminf (fun ε => ∫⁻ x, ENNReal.ofReal (innerEnergy ε k x /
      capMom D ε) ∂(sphMeasure D)) (𝓝[>] (0 : ℝ)) := by
    calc ENNReal.ofReal A = ∫⁻ x, ENNReal.ofReal (ψ x) ∂(sphMeasure D) := by
          rw [← hAψ]; exact ofReal_integral_eq_lintegral_ofReal hψi hψnn
      _ ≤ ∫⁻ x, liminf (fun ε => ENNReal.ofReal (innerEnergy ε k x / capMom D ε))
            (𝓝[>] (0 : ℝ)) ∂(sphMeasure D) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_differentiableAt_angle hD hh] with x hx
          exact ofReal_le_liminf_inner hD k hk x hx.1 hx.2
      _ ≤ _ := hF
  have hL2 : liminf (fun ε => ∫⁻ x, ENNReal.ofReal (innerEnergy ε k x / capMom D ε)
      ∂(sphMeasure D)) (𝓝[>] (0 : ℝ)) =
      liminf (fun ε => ENNReal.ofReal (nlEnergy ε k / capMom D ε)) (𝓝[>] (0 : ℝ)) := by
    refine liminf_congr (hev0.mono fun ε hε => ?_)
    have hm := capMom_pos hD hε.1 hε.2
    rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_innerEnergy ε k).div_const _)
      (ae_of_all _ fun x => div_nonneg (innerEnergy_nonneg ε k x) hm.le), integral_div,
      ← nlEnergy_eq_integral]
  rw [hL2] at hL
  show ∀ᶠ ε in 𝓝[>] (0 : ℝ), (A - η) * capMom D ε ≤ nlEnergy ε k
  by_cases hAη : A - η ≤ 0
  · filter_upwards [hev0] with ε hε
    have hm := capMom_pos hD hε.1 hε.2
    have := nlEnergy_nonneg ε k
    nlinarith
  · have hAη' : 0 < A - η := not_le.1 hAη
    have hlt : ENNReal.ofReal (A - η) < ENNReal.ofReal A :=
      (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    filter_upwards [eventually_lt_of_lt_liminf (lt_of_lt_of_le hlt hL), hev0] with ε h1 hε
    have hm := capMom_pos hD hε.1 hε.2
    have h2 := (ENNReal.ofReal_lt_ofReal_iff'.1 h1).1
    rw [lt_div_iff₀ hm] at h2
    exact h2.le

end

end PDE.FHLane
