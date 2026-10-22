module

public import EllipticRegularity.Ch4.Planar.Sharp2dEnergy

/-!
# Energy growth in the plane from the Piccinini--Spagnolo monotonicity formula

The monotonicity formula (taken as the hypothesis `hSpag`, exactly the statement of the
statement `piccinini_spagnolo_monotonicity`) is applied to the blow-up
`v(y) = u(x₀ + y/2)` and pushed to the limit `s ↑ 1`.
-/

@[expose] public section

namespace PDE.Ch4Planar

open MeasureTheory Filter Topology

/-- The statement of the Piccinini--Spagnolo monotonicity formula (the statement
`piccinini_spagnolo_monotonicity`), used as an interface hypothesis. -/
abbrev PiccininiSpagnoloStatement : Prop :=
  ∀ (Λ : ℝ) (a : CoeffField 2),
    (∀ i j : Fin 2, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec 2) 1))) →
    (∀ x ∈ euclideanBall (0 : Vec 2) 1, ∀ i j : Fin 2, a x i j = a x j i) →
    (∀ x ∈ euclideanBall (0 : Vec 2) 1, IsEllipticMatrix 1 Λ (a x)) →
    ∀ (u : H1Function (euclideanBall (0 : Vec 2) 1)),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec 2) 1) u
        (0 : Vec 2 → ℝ) 0 →
    MonotoneOn
      (fun r : ℝ => r ^ (-(2 / Real.sqrt Λ)) *
        ∫ x in euclideanBall (0 : Vec 2) r, vecDot (u.grad x) (matVecMul (a x) (u.grad x)))
      (Set.Ioo 0 1)

local notation "U₁" => euclideanBall (0 : Vec 2) 1

/-- Energy growth of the weighted energy `∇u · a ∇u` on small balls. -/
theorem sharp2d_energy_growth (hSpag : PiccininiSpagnoloStatement)
    (Λ : ℝ) (a : CoeffField 2)
    (hmeas : ∀ i j : Fin 2, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec 2) 1)))
    (hsymm : ∀ x ∈ euclideanBall (0 : Vec 2) 1, ∀ i j : Fin 2, a x i j = a x j i)
    (hell : ∀ x ∈ euclideanBall (0 : Vec 2) 1, IsEllipticMatrix 1 Λ (a x))
    (u : H1Function (euclideanBall (0 : Vec 2) 1))
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec 2) 1) u
      (0 : Vec 2 → ℝ) 0)
    (x₀ : Vec 2) (hx₀ : x₀ ∈ euclideanBall (0 : Vec 2) (1 / 2))
    (r : ℝ) (hr : 0 < r) (hr2 : r ≤ 1 / 2) :
    ∫ y in euclideanBall x₀ r, vecDot (u.grad y) (matVecMul (a y) (u.grad y)) ≤
      (2 * r) ^ (2 * Λ ^ (-(1 / 2 : ℝ))) *
        ∫ y in euclideanBall (0 : Vec 2) 1, vecDot (u.grad y) (matVecMul (a y) (u.grad y)) := by
  have hUmeas : MeasurableSet U₁ := measurableSet_euclideanBall _ _
  have hΛ : 0 < Λ := (hell 0 (center_mem_euclideanBall 0 (by norm_num))).Lam_pos
  set q : Vec 2 → ℝ := fun x => vecDot (u.grad x) (matVecMul (a x) (u.grad x)) with hq
  have hqU : IntegrableOn q U₁ := integrableOn_energyDensity hUmeas hmeas hell u
  have hqnn : ∀ x ∈ U₁, 0 ≤ q x := fun x hx => DGNM.vecDot_matVecMul_self_nonneg (hell x hx) _
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hball : euclideanBall x₀ (1 / 2) ⊆ U₁ := euclideanBall_half_subset_unit_of_center_mem_half hx₀
  -- monotonicity of the energy in the radius
  have hQmono : ∀ ρ ρ' : ℝ, 0 ≤ ρ → ρ ≤ ρ' → ρ' ≤ 1 / 2 →
      ∫ x in euclideanBall x₀ ρ, q x ≤ ∫ x in euclideanBall x₀ ρ', q x := by
    intro ρ ρ' h0 h1 h2
    refine setIntegral_mono_set (hqU.mono_set ((euclideanBall_mono (h0.trans h1) h2).trans hball))
      ?_ (Filter.Eventually.of_forall (euclideanBall_mono h0 h1))
    filter_upwards [ae_restrict_mem (measurableSet_euclideanBall x₀ ρ')] with x hx
    exact hqnn x (hball (euclideanBall_mono (by linarith) h2 hx))
  have hQtot : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 / 2 → ∫ x in euclideanBall x₀ ρ, q x ≤ ∫ x in U₁, q x := by
    intro ρ h0 h1
    refine setIntegral_mono_set hqU ?_
      (Filter.Eventually.of_forall ((euclideanBall_mono h0 h1).trans hball))
    filter_upwards [ae_restrict_mem hUmeas] with x hx
    exact hqnn x hx
  -- the exponent
  set β : ℝ := 2 * Λ ^ (-(1 / 2 : ℝ)) with hβ
  have hβpos : 0 < β := by positivity
  have hβ' : -(2 / Real.sqrt Λ) = -β := by
    rw [hβ, Real.rpow_neg hΛ.le, Real.sqrt_eq_rpow, div_eq_mul_inv]
  -- blow-up data
  have hmeas' := DGNM.blowUpCoeff_aemeasurable hmeas x₀ hhalf hball
  have hin : ∀ y ∈ euclideanBall (0 : Vec 2) 1, (1 / 2 : ℝ) • y + x₀ ∈ U₁ := by
    intro y hy
    apply hball
    have := (DGNM.affineScale_mem_euclideanBall_iff x₀ hhalf 1 y).mpr hy
    rwa [mul_one] at this
  have hsymm' : ∀ y ∈ euclideanBall (0 : Vec 2) 1, ∀ i j : Fin 2,
      DGNM.blowUpCoeff a x₀ (1 / 2) y i j = DGNM.blowUpCoeff a x₀ (1 / 2) y j i := by
    intro y hy i j
    exact hsymm _ (hin y hy) i j
  have hell' := DGNM.blowUpCoeff_elliptic hell x₀ hhalf hball
  have hsol' := DGNM.solutionOn_blowUp (isOpen_euclideanBall 0 1) hsol x₀ hhalf hball
  have hmono := hSpag Λ _ hmeas' hsymm' hell' _ hsol'
  simp only [hβ'] at hmono
  simp only [blowUp_energy u a x₀ hball] at hmono
  -- the limit `s ↑ 1`
  have hkey : ∀ ρ : ℝ, 0 < ρ → 2 * ρ < 1 →
      (2 * ρ) ^ (-β) * ∫ x in euclideanBall x₀ ρ, q x ≤ ∫ x in U₁, q x := by
    intro ρ hρ h2ρ
    have hlim : Tendsto (fun s : ℝ => s ^ (-β) * ∫ x in U₁, q x) (𝓝[<] 1)
        (𝓝 (1 ^ (-β) * ∫ x in U₁, q x)) := by
      refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      exact ((Real.continuousAt_rpow_const 1 (-β) (Or.inl one_ne_zero)).mul
        continuousAt_const).tendsto
    have hev : ∀ᶠ s in 𝓝[<] (1 : ℝ), (2 * ρ) ^ (-β) * ∫ x in euclideanBall x₀ ρ, q x ≤
        s ^ (-β) * ∫ x in U₁, q x := by
      filter_upwards [Ioo_mem_nhdsLT h2ρ] with s hs
      have hs0 : 0 < s := by linarith [hs.1]
      have h1 := hmono ⟨by linarith, h2ρ⟩ ⟨hs0, hs.2⟩ hs.1.le
      simp only at h1
      have e : (1 / 2 : ℝ) * (2 * ρ) = ρ := by ring
      rw [e] at h1
      refine h1.trans (mul_le_mul_of_nonneg_left ((hQtot _ (by linarith [hs.2]) (by linarith [hs.2]))) (Real.rpow_nonneg hs0.le _))
    have := ge_of_tendsto hlim hev
    simpa using this
  have hmain : ∫ x in euclideanBall x₀ r, q x ≤ (2 * r) ^ β * ∫ x in U₁, q x := by
    rcases hr2.lt_or_eq with hlt | heq
    · have h2r : 0 < 2 * r := by linarith
      have := hkey r hr (by linarith)
      have hpow : (2 * r) ^ β * (2 * r) ^ (-β) = 1 := by
        rw [← Real.rpow_add h2r]; simp
      calc ∫ x in euclideanBall x₀ r, q x
          = (2 * r) ^ β * ((2 * r) ^ (-β) * ∫ x in euclideanBall x₀ r, q x) := by
            rw [← mul_assoc, hpow, one_mul]
        _ ≤ (2 * r) ^ β * ∫ x in U₁, q x :=
            mul_le_mul_of_nonneg_left this (Real.rpow_nonneg h2r.le _)
    · subst heq
      have : (2 * (1 / 2 : ℝ)) = 1 := by norm_num
      rw [this, Real.one_rpow, one_mul]
      exact hQtot _ hr.le le_rfl
  exact hmain

end PDE.Ch4Planar
