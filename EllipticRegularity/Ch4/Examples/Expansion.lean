module

public import EllipticRegularity.Ch4.Examples.ExpansionBound
public import DGNMStatements.WeakHarnack0

/-!
# Expansion of positivity for small `θ` (Proposition 4.15)

Follows the manuscript proof: apply the weak Harnack estimate to `u + ε` with
`p = Λ^{-1/2}` and `ε = (8 C_*)^{-Λ^{1/2}}`.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE.Ch4Examples

open MeasureTheory Filter

/-- **Expansion of positivity for small `θ`** (Proposition 4.15). -/
theorem expansion_small_full (d : ℕ) (hd : 3 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1 / 4 ∧ 0 < C ∧
      ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j)
        (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ θ : ℝ, 0 < θ → θ ≤ c →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) u →
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 ≤ u.toFun x) →
      ENNReal.ofReal (1 - θ) * volume (euclideanBall (0 : Vec d) 1) ≤
        volume {x ∈ euclideanBall (0 : Vec d) 1 | 1 ≤ u.toFun x} →
        ENNReal.ofReal (Real.exp (-(C * Real.sqrt Λ))) ≤
          essInf (fun x => ENNReal.ofReal (u.toFun x))
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) := by
  obtain ⟨C0, hC0, hW⟩ := exists_weakHarnack0_constant d hd
  have hBtop : volume (euclideanBall (0 : Vec d) 1) ≠ ⊤ :=
    volume_euclideanBall_ne_top _ zero_le_one
  have hBpos' : 0 < volume (euclideanBall (0 : Vec d) 1) := volume_euclideanBall_pos _ one_pos
  set Bt : ℝ := (volume (euclideanBall (0 : Vec d) 1)).toReal with hBt
  have hBpos : 0 < Bt := ENNReal.toReal_pos hBpos'.ne' hBtop
  have hBeq : volume (euclideanBall (0 : Vec d) 1) = ENNReal.ofReal Bt :=
    (ENNReal.ofReal_toReal hBtop).symm
  set κ : ℝ := (2 : ℝ) ^ ((d : ℝ) / 2) with hκ
  have hκpos : 0 < κ := by positivity
  set Cs : ℝ := max 1 (κ * C0 * Bt) with hCs
  have hCs1 : 1 ≤ Cs := le_max_left _ _
  have hCs2 : κ * C0 * Bt ≤ Cs := le_max_right _ _
  have hCspos : 0 < Cs := by linarith
  refine ⟨1 / (4 * Cs), Real.log (8 * Cs), by positivity, ?_, Real.log_pos (by linarith), ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  intro Λ a hmeas hell θ hθ hθc u hsuper hnn hdens
  have : IsFiniteMeasure (volumeOn (euclideanBall (0 : Vec d) 1)) :=
    (isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) one_pos).isFiniteMeasure_volumeOn
  have h0mem : (0 : Vec d) ∈ euclideanBall (0 : Vec d) 1 := by
    rw [mem_euclideanBall_zero_iff]; simp [vecNormSq_eq_sum_sq]
  have hΛ1 : 1 ≤ Λ := (hell 0 h0mem).lam_le_Lam
  set s : ℝ := Real.sqrt Λ with hs
  have hs1 : 1 ≤ s := by
    rw [hs, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hΛ1
  have hs2 : s ^ 2 = Λ := Real.sq_sqrt (by linarith)
  set p : ℝ := s⁻¹ with hp
  have hp0 : 0 < p := by positivity
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ hs1
  have hΛp : Λ * p ^ 2 + 1 = 2 := by
    rw [hp, inv_pow, ← hs2]; field_simp; norm_num
  set ε : ℝ := Real.exp (-(Real.log (8 * Cs) * s)) with hε
  have hεpos : 0 < ε := Real.exp_pos _
  have hεp : ε ^ p = (8 * Cs)⁻¹ := by
    rw [hε, ← Real.exp_mul]
    have : -(Real.log (8 * Cs) * s) * p = -Real.log (8 * Cs) := by
      rw [hp]; field_simp
    rw [this, Real.exp_neg, Real.exp_log (by positivity)]
  by_contra hcon
  push Not at hcon
  -- the function `v = u + ε`
  let v : H1Function (euclideanBall (0 : Vec d) 1) := u.addConst ε
  have hv : ∀ x, v.toFun x = u.toFun x + ε := fun x => rfl
  have hvpos : ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < v.toFun x := by
    filter_upwards [hnn] with x hx
    rw [hv]; linarith
  have hvsuper : IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) v := by
    intro φ hφ
    have hg : v.grad = u.grad := funext fun x => H1Function.grad_addConst u ε x
    obtain ⟨ht, hle⟩ := hsuper φ hφ
    refine ⟨⟨?_, ht.source_integrable, ht.forcing_integrable⟩, ?_⟩
    · rw [hg]; exact ht.flux_integrable
    · rw [hg]; exact hle
  have hH := (hW Λ a hmeas hell v hvpos hvsuper).1 p hp0
  rw [hΛp] at hH
  -- upper bound of the integral
  have hI := inv_power_lintegral_bound (isOpen_euclideanBall (0 : Vec d) 1).measurableSet hBtop u hnn θ hθ
    (by have : θ ≤ 1 / (4 * Cs) := hθc
        have : 1 / (4 * Cs) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
        linarith) hdens ε p hεpos hp0
  set R : ℝ := Bt * (1 + θ * (ε⁻¹) ^ p) with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  have hIR : ∫⁻ x in euclideanBall (0 : Vec d) 1, ENNReal.ofReal ((u.toFun x + ε)⁻¹ ^ p) ≤
      ENNReal.ofReal R := by
    refine hI.trans (le_of_eq ?_)
    have hE : 0 ≤ (ε⁻¹) ^ p := by positivity
    rw [hBeq, hR, show Bt * (1 + θ * (ε⁻¹) ^ p) = Bt + (ε⁻¹) ^ p * (θ * Bt) by ring,
      ENNReal.ofReal_add hBpos.le (by positivity), ENNReal.ofReal_mul hE,
      ENNReal.ofReal_mul hθ.le]
  -- upper bound of the essential infimum
  have hfreq : ∃ᶠ x in ae (volumeOn (euclideanBall (0 : Vec d) (1 / 2))),
      ENNReal.ofReal (v.toFun x) ≤ ENNReal.ofReal (2 * ε) := by
    have := frequently_lt_of_liminf_lt (by isBoundedDefault) hcon
    refine this.mono fun x hx => ENNReal.ofReal_le_ofReal ?_
    rw [hv]
    have := (ENNReal.ofReal_lt_ofReal_iff hεpos).1 hx
    linarith
  have hE : essInf (fun x => ENNReal.ofReal (v.toFun x))
      (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤ ENNReal.ofReal (2 * ε) :=
    liminf_le_of_frequently_le' hfreq
  -- combine
  have hH2 : ENNReal.ofReal ((2 : ℝ) ^ (-((d : ℝ) / 2))) * (ENNReal.ofReal R)⁻¹ ≤
      ENNReal.ofReal C0 * ENNReal.ofReal ((2 * ε) ^ p) := by
    refine le_trans (mul_le_mul' le_rfl (ENNReal.inv_le_inv.2 hIR)) (hH.trans ?_)
    rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le]
    exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hE hp0.le)
  rw [← ENNReal.ofReal_inv_of_pos hRpos, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul hC0.le, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hH2
  -- the real inequality
  have hpow2 : (2 * ε) ^ p ≤ 2 * ε ^ p := by
    rw [Real.mul_rpow (by norm_num) hεpos.le]
    have : (2 : ℝ) ^ p ≤ 2 ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hp1
    rw [Real.rpow_one] at this
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hεinv : (ε⁻¹) ^ p = 8 * Cs := by
    rw [Real.inv_rpow hεpos.le, hεp, inv_inv]
  have hRle : R ≤ 3 * Bt := by
    rw [hR, hεinv]
    have : θ * (8 * Cs) ≤ 2 := by
      have h1 : θ ≤ 1 / (4 * Cs) := hθc
      calc θ * (8 * Cs) ≤ 1 / (4 * Cs) * (8 * Cs) := by gcongr
        _ = 2 := by field_simp; norm_num
    nlinarith
  have hneg : (2 : ℝ) ^ (-((d : ℝ) / 2)) = κ⁻¹ := by
    rw [Real.rpow_neg (by norm_num)]
  rw [hneg] at hH2
  have hH3 : κ⁻¹ * R⁻¹ ≤ C0 * (2 * (8 * Cs)⁻¹) := by
    refine hH2.trans ?_
    rw [← hεp]
    exact mul_le_mul_of_nonneg_left hpow2 hC0.le
  have h4 : 1 ≤ κ * R * (C0 * (2 * (8 * Cs)⁻¹)) := by
    calc (1 : ℝ) = κ * R * (κ⁻¹ * R⁻¹) := by field_simp
      _ ≤ κ * R * (C0 * (2 * (8 * Cs)⁻¹)) := by gcongr
  have h5 : κ * R * (C0 * (2 * (8 * Cs)⁻¹)) ≤ κ * (3 * Bt) * (C0 * (2 * (8 * Cs)⁻¹)) := by
    gcongr
  have h6 : κ * (3 * Bt) * (C0 * (2 * (8 * Cs)⁻¹)) = 3 / 4 * (κ * C0 * Bt / Cs) := by
    field_simp; ring
  have h7 : κ * C0 * Bt / Cs ≤ 1 := by rw [div_le_one hCspos]; exact hCs2
  linarith

end PDE.Ch4Examples
