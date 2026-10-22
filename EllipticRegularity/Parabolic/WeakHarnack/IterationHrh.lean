module

public import EllipticRegularity.Parabolic.WeakHarnack.IterationChain

/-!
# From a power step to the reverse Hölder hypothesis of the Bombieri-Giusti lemma

For the Bombieri-Giusti lemma (`PDE.Bombieri.bombieri_giusti`) one needs, for every small
`α`, an estimate `‖f‖_{α₀, U σ'} ≤ (c (σ-σ')^{-m'})^{1/α - 1/α₀} ‖f‖_{α, U σ}`.  It follows by
iterating a single power step from `α` (rounded down to `q χ^{-N}`) up to `α₀ = q χ`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE.ParabIter

variable {X : Type*} [MeasurableSpace X]

/-- A good starting exponent `q χ^{-N}`: below `α` and at most `χ + 1/q` times `1/α`
away from it. -/
theorem exists_start_exponent {χ q α : ℝ} (hχ : 1 < χ) (hq : 0 < q) (hα : 0 < α)
    (hα1 : α ≤ 1) :
    ∃ N : ℕ, q / χ ^ N ≤ α ∧ (q / χ ^ N)⁻¹ ≤ (χ + q⁻¹) / α := by
  have hχ0 : 0 < χ := by linarith
  have hq1 : 0 < q⁻¹ := inv_pos.mpr hq
  by_cases hqα : q ≤ α
  · refine ⟨0, by simpa using hqα, ?_⟩
    simp only [pow_zero, div_one]
    rw [le_div_iff₀ hα]
    have : q⁻¹ * α ≤ q⁻¹ * 1 := by gcongr
    nlinarith
  · push Not at hqα
    have hx : 1 ≤ q / α := by rw [le_div_iff₀ hα]; linarith
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx hχ
    have hχn : 0 < χ ^ n := by positivity
    refine ⟨n + 1, ?_, ?_⟩
    · rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hα] at hn2
      linarith
    · rw [inv_div, div_le_div_iff₀ hq hα, pow_succ]
      rw [le_div_iff₀ hα] at hn1
      have h1 : χ ^ n * α ≤ q := by linarith
      have h2 : χ ^ n * χ * α ≤ q * χ := by nlinarith
      have h3 : 0 ≤ q⁻¹ * q := by positivity
      have h4 : q⁻¹ * q = 1 := inv_mul_cancel₀ hq.ne'
      nlinarith

/-- The constant `χ + 1/q` -/
noncomputable def posK (χ q : ℝ) : ℝ := χ + q⁻¹

/-- First exponent constant. -/
noncomputable def posC1 (χ q : ℝ) : ℝ := χ / (χ - 1) * posK χ q

/-- Second exponent constant. -/
noncomputable def posC2 (χ q : ℝ) : ℝ := χ / (χ - 1) ^ 2 * posK χ q

/-- The constant `c` of the reverse Hölder hypothesis obtained from a positive power step. -/
noncomputable def posC (χ A m q : ℝ) : ℝ :=
  (A * 2 ^ m) ^ (2 * posC1 χ q) * (2 ^ m) ^ (2 * posC2 χ q)

/-- The exponent `m'` of the reverse Hölder hypothesis obtained from a positive power step. -/
noncomputable def posM (χ m q : ℝ) : ℝ := 2 * posC1 χ q * m

/-- The pure-real bound combining the geometric products. -/
theorem real_bound {g A m χ p₀ E K0 : ℝ} (hg0 : 0 < g) (hg1 : g ≤ 1) (hA : 1 ≤ A)
    (hm : 0 < m) (hχ : 1 < χ) (hK : p₀⁻¹ ≤ 2 * K0 * E) :
    (A * 2 ^ m * g ^ (-m)) ^ (χ / (χ - 1) / p₀) * (1 * 2 ^ m) ^ (χ / (χ - 1) ^ 2 / p₀) ≤
      ((A * 2 ^ m) ^ (2 * (χ / (χ - 1) * K0)) * (2 ^ m) ^ (2 * (χ / (χ - 1) ^ 2 * K0)) *
        g ^ (-(2 * (χ / (χ - 1) * K0) * m))) ^ E := by
  have hχ1 : 0 < χ - 1 := by linarith
  have h2m : (1 : ℝ) ≤ 2 ^ m := Real.one_le_rpow (by norm_num) hm.le
  have hX1 : 1 ≤ A * 2 ^ m := by nlinarith
  have hgm : (1 : ℝ) ≤ g ^ (-m) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hg0 hg1 (by linarith)
  have ha : 1 ≤ A * 2 ^ m * g ^ (-m) := by nlinarith
  have hT : χ / (χ - 1) / p₀ ≤ 2 * (χ / (χ - 1) * K0) * E := by
    rw [div_eq_mul_inv]
    calc χ / (χ - 1) * p₀⁻¹ ≤ χ / (χ - 1) * (2 * K0 * E) := by gcongr
      _ = _ := by ring
  have hT2 : χ / (χ - 1) ^ 2 / p₀ ≤ 2 * (χ / (χ - 1) ^ 2 * K0) * E := by
    rw [div_eq_mul_inv]
    calc χ / (χ - 1) ^ 2 * p₀⁻¹ ≤ χ / (χ - 1) ^ 2 * (2 * K0 * E) := by gcongr
      _ = _ := by ring
  have hB1 : (1 : ℝ) ≤ 1 * 2 ^ m := by linarith
  calc (A * 2 ^ m * g ^ (-m)) ^ (χ / (χ - 1) / p₀) * (1 * 2 ^ m) ^ (χ / (χ - 1) ^ 2 / p₀)
      ≤ (A * 2 ^ m * g ^ (-m)) ^ (2 * (χ / (χ - 1) * K0) * E) *
        (2 ^ m) ^ (2 * (χ / (χ - 1) ^ 2 * K0) * E) := by
        rw [one_mul] at hB1 ⊢
        exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le ha hT)
          (Real.rpow_le_rpow_of_exponent_le hB1 hT2) (by positivity) (by positivity)
    _ = _ := by
        have hX0 : 0 ≤ A * 2 ^ m := by linarith
        have hY0 : (0 : ℝ) ≤ 2 ^ m := by linarith
        set a₁ : ℝ := 2 * (χ / (χ - 1) * K0) with ha₁
        set a₂ : ℝ := 2 * (χ / (χ - 1) ^ 2 * K0) with ha₂
        have eX : (A * 2 ^ m) ^ (a₁ * E) = ((A * 2 ^ m) ^ a₁) ^ E := Real.rpow_mul hX0 a₁ E
        have eY : (2 ^ m : ℝ) ^ (a₂ * E) = ((2 ^ m : ℝ) ^ a₂) ^ E := Real.rpow_mul hY0 a₂ E
        have eG : (g ^ (-m)) ^ (a₁ * E) = (g ^ (-(a₁ * m))) ^ E := by
          rw [← Real.rpow_mul hg0.le, ← Real.rpow_mul hg0.le]; congr 1; ring
        rw [Real.mul_rpow (x := (A * 2 ^ m) ^ a₁ * (2 ^ m) ^ a₂) (y := g ^ (-(a₁ * m)))
            (by positivity) (by positivity),
          Real.mul_rpow (x := (A * 2 ^ m) ^ a₁) (y := (2 ^ m) ^ a₂)
            (by positivity) (by positivity),
          ← eX, ← eY, ← eG, Real.mul_rpow hX0 (by positivity)]
        ring

/-- **Reverse Hölder hypothesis from a positive power step.**  A single reverse Hölder step
`‖f‖_{χp, U σ'} ≤ (A (σ-σ')^{-m})^{1/p} ‖f‖_{p, U σ}` for `0 < p ≤ q` yields the hypothesis
`hrh` of `PDE.Bombieri.bombieri_giusti` with `α₀ = q χ`, `c = posC χ A m q` and
`m' = posM χ m q` (which depend only on `χ, A, m, q`). -/
theorem hrh_of_posStep (ν : Measure X) [IsProbabilityMeasure ν] (U : ℝ → Set X) (f : X → ℝ)
    {δ χ A m q : ℝ} (hδ : 0 < δ) (hχ : 1 < χ) (hA : 1 ≤ A) (hm : 0 < m) (hq : 0 < q)
    (hUmono : ∀ σ' σ, δ ≤ σ' → σ' ≤ σ → σ ≤ 1 → U σ' ⊆ U σ)
    (hstep : ∀ σ' σ : ℝ, δ ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p → p ≤ q →
      eLpNorm f (ENNReal.ofReal (χ * p)) (ν.restrict (U σ')) ≤
        ENNReal.ofReal ((A * (σ - σ') ^ (-m)) ^ (1 / p)) *
          eLpNorm f (ENNReal.ofReal p) (ν.restrict (U σ))) :
    1 ≤ posC χ A m q ∧ 0 < posM χ m q ∧
    ∀ σ' σ : ℝ, δ ≤ σ' → σ' < σ → σ ≤ 1 → ∀ α : ℝ, 0 < α → α ≤ min 1 (q * χ / 2) →
      eLpNorm f (ENNReal.ofReal (q * χ)) (ν.restrict (U σ')) ≤
        ENNReal.ofReal ((posC χ A m q * (σ - σ') ^ (-posM χ m q)) ^ (1 / α - 1 / (q * χ))) *
          eLpNorm f (ENNReal.ofReal α) (ν.restrict (U σ)) := by
  have hχ1 : 0 < χ - 1 := by linarith
  have hχ0 : 0 < χ := by linarith
  have hK : 0 < posK χ q := by unfold posK; have := inv_pos.mpr hq; linarith
  have hc1 : 0 < posC1 χ q := mul_pos (div_pos hχ0 hχ1) hK
  have hc2 : 0 < posC2 χ q := mul_pos (div_pos hχ0 (by positivity)) hK
  have h2m : (1 : ℝ) ≤ 2 ^ m := Real.one_le_rpow (by norm_num) hm.le
  refine ⟨?_, ?_, ?_⟩
  · unfold posC
    have h1 : 1 ≤ A * 2 ^ m := by nlinarith
    exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow h1 (by linarith))
      (Real.one_le_rpow h2m (by linarith))
  · unfold posM; positivity
  intro σ' σ h1 h2 h3 α hα hαle
  have hα1 : α ≤ 1 := hαle.trans (min_le_left _ _)
  have hα2 : α ≤ q * χ / 2 := hαle.trans (min_le_right _ _)
  have hg0 : 0 < σ - σ' := by linarith
  have hg1 : σ - σ' ≤ 1 := by linarith
  obtain ⟨N, hN1, hN2⟩ := exists_start_exponent hχ hq hα hα1
  set p₀ : ℝ := q / χ ^ N with hp₀
  have hχN : 0 < χ ^ N := by positivity
  have hp₀0 : 0 < p₀ := by positivity
  -- Hölder from `p₀` up to `α`
  have hholder : eLpNorm f (ENNReal.ofReal p₀) (ν.restrict (U σ)) ≤
      eLpNorm f (ENNReal.ofReal α) (ν.restrict (U σ)) := by
    have hle : ENNReal.ofReal p₀ ≤ ENNReal.ofReal α := ENNReal.ofReal_le_ofReal hN1
    have hpos : 0 < ENNReal.ofReal p₀ := ENNReal.ofReal_pos.mpr hp₀0
    refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ_of_pos hle hpos).trans ?_
    have hμ : (ν.restrict (U σ)) Set.univ ≤ 1 := by
      rw [Measure.restrict_apply_univ]; exact prob_le_one
    have hexp : 0 ≤ 1 / (ENNReal.ofReal p₀).toReal - 1 / (ENNReal.ofReal α).toReal := by
      rw [ENNReal.toReal_ofReal hp₀0.le, ENNReal.toReal_ofReal hα.le, sub_nonneg]
      exact one_div_le_one_div_of_le hp₀0 hN1
    have := ENNReal.rpow_le_one hμ hexp
    calc _ ≤ eLpNorm f (ENNReal.ofReal α) (ν.restrict (U σ)) * 1 := by gcongr
      _ = _ := mul_one _
  -- the chain from `p₀` to `q χ`
  have hchain := chain_geometric ν U f δ χ m hδ hχ (fun p => p ≤ q) (fun _ => A) hstep hUmono
    (p₀ := p₀) (A₁ := A) (B₁ := 1) hm hp₀0 hA le_rfl (N + 1)
    (fun k hk => by
      show p₀ * χ ^ k ≤ q
      have hk' : χ ^ k ≤ χ ^ N := pow_le_pow_right₀ hχ.le (Nat.lt_succ_iff.mp hk)
      calc p₀ * χ ^ k ≤ p₀ * χ ^ N := by gcongr
        _ = q := by rw [hp₀]; field_simp)
    (fun _ _ => by linarith) (fun k _ => by simp) h1 h2 h3
  have hend : p₀ * χ ^ (N + 1) = q * χ := by rw [hp₀, pow_succ]; field_simp
  rw [hend] at hchain
  -- the real bound
  have hE : 1 / α - 1 / (q * χ) ≥ 1 / (2 * α) := by
    have : 1 / (q * χ) ≤ 1 / (2 * α) := one_div_le_one_div_of_le (by positivity) (by linarith)
    have h12 : 1 / α = 1 / (2 * α) + 1 / (2 * α) := by field_simp; ring
    linarith
  set E : ℝ := 1 / α - 1 / (q * χ) with hEdef
  have hpK : p₀⁻¹ ≤ 2 * posK χ q * E := by
    have h0 : p₀⁻¹ ≤ posK χ q / α := hN2
    have : posK χ q / α = 2 * posK χ q * (1 / (2 * α)) := by field_simp
    rw [this] at h0
    exact h0.trans (by gcongr)
  have hb := real_bound hg0 hg1 hA hm hχ hpK
  have hEq : (posC χ A m q * (σ - σ') ^ (-posM χ m q)) =
      (A * 2 ^ m) ^ (2 * (χ / (χ - 1) * posK χ q)) *
        (2 ^ m) ^ (2 * (χ / (χ - 1) ^ 2 * posK χ q)) *
        (σ - σ') ^ (-(2 * (χ / (χ - 1) * posK χ q) * m)) := rfl
  rw [hEq]
  calc eLpNorm f (ENNReal.ofReal (q * χ)) (ν.restrict (U σ'))
      ≤ _ := hchain
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hb) hholder

/-- The constant `c` of the reverse Hölder hypothesis from a negative-type power step. -/
noncomputable def negC (χ A β m : ℝ) : ℝ := posC χ (A * 2 ^ β) m χ⁻¹

/-- The exponent `m'` of the reverse Hölder hypothesis from a negative-type power step. -/
noncomputable def negM (χ m : ℝ) : ℝ := posM χ m χ⁻¹

/-- **Reverse Hölder hypothesis from a negative-type power step** (polynomial growth
`(1+p)^β` in the exponent), with `α₀ = 1`: constants depend only on `χ, A, β, m`. -/
theorem hrh_of_negStep (ν : Measure X) [IsProbabilityMeasure ν] (U : ℝ → Set X) (g : X → ℝ)
    {δ χ A β m : ℝ} (hδ : 0 < δ) (hχ : 1 < χ) (hA : 1 ≤ A) (hβ : 0 ≤ β) (hm : 0 < m)
    (hUmono : ∀ σ' σ, δ ≤ σ' → σ' ≤ σ → σ ≤ 1 → U σ' ⊆ U σ)
    (hstep : ∀ σ' σ : ℝ, δ ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm g (ENNReal.ofReal (χ * p)) (ν.restrict (U σ')) ≤
        ENNReal.ofReal ((A * (1 + p) ^ β * (σ - σ') ^ (-m)) ^ (1 / p)) *
          eLpNorm g (ENNReal.ofReal p) (ν.restrict (U σ))) :
    1 ≤ negC χ A β m ∧ 0 < negM χ m ∧
    ∀ σ' σ : ℝ, δ ≤ σ' → σ' < σ → σ ≤ 1 → ∀ α : ℝ, 0 < α → α ≤ min 1 (1 / 2) →
      eLpNorm g (ENNReal.ofReal 1) (ν.restrict (U σ')) ≤
        ENNReal.ofReal ((negC χ A β m * (σ - σ') ^ (-negM χ m)) ^ (1 / α - 1 / 1)) *
          eLpNorm g (ENNReal.ofReal α) (ν.restrict (U σ)) := by
  have hχ0 : 0 < χ := by linarith
  have hq : 0 < χ⁻¹ := inv_pos.mpr hχ0
  have hqχ : χ⁻¹ * χ = 1 := inv_mul_cancel₀ hχ0.ne'
  have h2β : (1 : ℝ) ≤ 2 ^ β := Real.one_le_rpow (by norm_num) hβ
  have hA' : 1 ≤ A * 2 ^ β := by nlinarith
  obtain ⟨hc, hM, h⟩ := hrh_of_posStep ν U g hδ hχ hA' hm hq hUmono
    (fun σ' σ h1 h2 h3 p hp hpq => by
      refine (hstep σ' σ h1 h2 h3 p hp).trans (mul_le_mul' ?_ le_rfl)
      refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) ?_ (by positivity))
      have hp1 : p ≤ 1 := hpq.trans (inv_le_one_of_one_le₀ hχ.le)
      have h1p : (1 + p) ^ β ≤ 2 ^ β :=
        Real.rpow_le_rpow (by linarith) (by linarith) hβ
      have hG : 0 ≤ (σ - σ') ^ (-m) := Real.rpow_nonneg (by linarith) _
      calc A * (1 + p) ^ β * (σ - σ') ^ (-m) ≤ A * 2 ^ β * (σ - σ') ^ (-m) := by gcongr)
  refine ⟨hc, hM, fun σ' σ h1 h2 h3 α hα hαle => ?_⟩
  have := h σ' σ h1 h2 h3 α hα (by rw [hqχ]; exact hαle)
  rw [hqχ] at this
  exact this

end PDE.ParabIter
