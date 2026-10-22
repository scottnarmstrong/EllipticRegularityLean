module

public import EllipticRegularity.Ch4.GreenDecay.DecayFull
public import DGNMStatements.DeGiorgiHolder
public import PDEFoundation.PDE.DGNM.Scaling

/-!
# Oscillation decay from De Giorgi's theorem (proof of Corollary 4.36, hypothesis (osc.decay))

If `w ∈ H¹(B_ρ)`, `ρ ≥ 4`, solves `-div (b ∇ w) = 0` in `B_ρ` for an elliptic field `b`, the
De Giorgi's Hölder estimate (Theorem 4.8) applied to `y ↦ w(ρ y) - (w)_{B_ρ}` on `B_1` gives
`ess osc_{B_2} w ≤ 4 |B_1|^{1/2} C_D Λ^{d/4} ρ^{-α} ‖w - (w)_{B_ρ}‖_{L̲²(B_ρ)}`, in the form
required by the hypothesis of `greenDecay_full`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4GreenDecay

open MeasureTheory PDE

noncomputable section

variable {d : ℕ}

/-- The smooth-test solution property only depends on the gradient representative. -/
theorem solution_of_grad_eq {U : Set (Vec d)} {a : CoeffField d} {u u' : H1Function U}
    {f : Vec d → ℝ} {F : Vec d → Vec d} (hg : ∀ x, u'.grad x = u.grad x)
    (h : IsWeakDivergenceFormSolutionOn a U u f F) :
    IsWeakDivergenceFormSolutionOn a U u' f F := by
  intro φ
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h φ
  refine ⟨⟨?_, h2, h3⟩, ?_⟩
  · simp only [hg]; exact h1
  · simp only [hg]; exact h4

/-- **Oscillation bound on `B_2` from De Giorgi's theorem.** -/
theorem osc_of_deGiorgi {CD Λ α : ℝ} (hCD : 0 < CD) (hΛ : 1 ≤ Λ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hDG : ∀ (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) 0 →
        ∃ (v : Vec d → ℝ) (M₀ M₁ : ℝ), v =ᵐ[volumeOn (euclideanBall (0 : Vec d) (1 / 2))] u.toFun ∧
          0 ≤ M₀ ∧ 0 ≤ M₁ ∧ (∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), |v x| ≤ M₀) ∧
          EuclideanHolderSeminormLE (euclideanBall (0 : Vec d) (1 / 2)) v α M₁ ∧
          ENNReal.ofReal (M₀ + M₁) ≤ ENNReal.ofReal (CD * Λ ^ ((d : ℝ) / 4)) *
            eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1)))
    {ρ : ℝ} (hρ : 4 ≤ ρ) {b : CoeffField d}
    (hbm : ∀ i j : Fin d, AEMeasurable (fun x => b x i j) (volumeOn (euclideanBall (0 : Vec d) ρ)))
    (hbell : ∀ x ∈ euclideanBall (0 : Vec d) ρ, IsEllipticMatrix 1 Λ (b x))
    (w : H1Function (euclideanBall (0 : Vec d) ρ))
    (hsol : IsWeakDivergenceFormSolutionOn b (euclideanBall (0 : Vec d) ρ) w (0 : Vec d → ℝ) 0) :
    ∃ m : ℝ, ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 2)),
      m ≤ w.toFun x ∧
      ENNReal.ofReal (w.toFun x - m) ≤
        ENNReal.ofReal ((4 * Real.sqrt (volume (euclideanBall (0 : Vec d) 1)).toReal * CD *
            Λ ^ ((d : ℝ) / 4)) * ρ ^ (-α)) *
          eLpMeanNormOn (euclideanBall (0 : Vec d) ρ) 2
            (fun y => w.toFun y - integralAverage (euclideanBall (0 : Vec d) ρ) w.toFun) := by
  have hρ0 : 0 < ρ := by linarith
  have hsub : euclideanBall (0 : Vec d) ρ ⊆ euclideanBall (0 : Vec d) ρ := subset_rfl
  have hfin1 : IsFiniteMeasure (volumeOn (euclideanBall (0 : Vec d) 1)) :=
    isFiniteMeasure_volumeOn_euclideanBall 0 one_pos.le
  have hfinρ : IsFiniteMeasure (volumeOn (euclideanBall (0 : Vec d) ρ)) :=
    isFiniteMeasure_volumeOn_euclideanBall 0 hρ0.le
  obtain ⟨c, hc⟩ : ∃ c, c = integralAverage (euclideanBall (0 : Vec d) ρ) w.toFun := ⟨_, rfl⟩
  rw [← hc]
  have hsol1 := DGNM.solutionOn_blowUp (isOpen_euclideanBall 0 ρ) hsol 0 hρ0 hsub
  let u1 : H1Function (euclideanBall (0 : Vec d) 1) := (DGNM.blowUp w 0 hρ0 hsub).addConst (-c)
  have hsol1' : IsWeakDivergenceFormSolutionOn (DGNM.blowUpCoeff b 0 ρ)
      (euclideanBall (0 : Vec d) 1) u1 (0 : Vec d → ℝ) 0 :=
    solution_of_grad_eq (fun y => H1Function.grad_addConst _ (-c) y) hsol1
  obtain ⟨v, M₀, M₁, hvae, hM₀, hM₁, hvbd, hHold, hsum⟩ :=
    hDG _ (DGNM.blowUpCoeff_aemeasurable hbm 0 hρ0 hsub)
      (DGNM.blowUpCoeff_elliptic hbell 0 hρ0 hsub) u1 hsol1'
  -- transfer of the a.e. identity back to `B_2`
  have hr2 : ρ * (1 / 2) = ρ / 2 := by ring
  have hae : ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) (ρ / 2))),
      v (ρ⁻¹ • x) = w.toFun x - c := by
    have key := (DGNM.ae_comp_affineScale_ball_iff (0 : Vec d) hρ0 (1 / 2)
      (P := fun x => v (ρ⁻¹ • x) = w.toFun x - c)).1
    rw [hr2] at key
    apply key
    filter_upwards [hvae] with y hy
    have h1 : ρ⁻¹ • (ρ • y + 0) = y := by
      rw [add_zero, smul_smul, inv_mul_cancel₀ hρ0.ne', one_smul]
    have h2 : u1.toFun y = w.toFun (ρ • y + 0) - c := by
      change w.toFun (ρ • y + 0) + -c = _
      ring
    show v (ρ⁻¹ • (ρ • y + 0)) = w.toFun (ρ • y + 0) - c
    rw [h1, hy, h2]
  have hB2 : euclideanBall (0 : Vec d) 2 ⊆ euclideanBall (0 : Vec d) (ρ / 2) :=
    euclideanBall_mono (by norm_num) (by linarith)
  have hae2 : ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 2)),
      v (ρ⁻¹ • x) = w.toFun x - c := ae_restrict_of_ae_restrict_of_subset hB2 hae
  have hae3 : ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 2)), x ∈ euclideanBall (0 : Vec d) 2 :=
    (ae_restrict_iff' (measurableSet_euclideanBall _ _)).2
      (Filter.Eventually.of_forall fun x hx => hx)
  -- the Hölder bound
  have hδ : ∀ x ∈ euclideanBall (0 : Vec d) 2,
      |v (ρ⁻¹ • x) - v 0| ≤ M₁ * (2 / ρ) ^ α := by
    intro x hx
    have hx2 : vecEuclideanNorm (x - 0) < 2 :=
      (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hx
    have hnorm : vecEuclideanNorm (ρ⁻¹ • x - 0) = ρ⁻¹ * vecEuclideanNorm (x - 0) := by
      rw [sub_zero, sub_zero, vecEuclideanNorm_smul, abs_of_pos (inv_pos.2 hρ0)]
    have hlt : vecEuclideanNorm (ρ⁻¹ • x - 0) < 2 / ρ := by
      rw [hnorm, div_eq_inv_mul]
      exact mul_lt_mul_of_pos_left hx2 (inv_pos.2 hρ0)
    have hle : vecEuclideanNorm (ρ⁻¹ • x - 0) ≤ 2 / ρ := hlt.le
    have hmem : ρ⁻¹ • x ∈ euclideanBall (0 : Vec d) (1 / 2) := by
      rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)]
      refine lt_of_lt_of_le hlt ?_
      rw [div_le_iff₀ hρ0]; linarith
    have h0 : (0 : Vec d) ∈ euclideanBall (0 : Vec d) (1 / 2) :=
      center_mem_euclideanBall 0 (by norm_num)
    refine (hHold _ hmem 0 h0).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (vecEuclideanNorm_nonneg _) hle hα0.le) hM₁
  -- the `L²` bound for `M₁`
  have hu1L2 : MemL2On (euclideanBall (0 : Vec d) 1) u1.toFun := u1.memL2
  have hfinN := hu1L2.eLpNorm_ne_top
  have hKnn : 0 ≤ CD * Λ ^ ((d : ℝ) / 4) := by positivity
  have hM1 : M₀ + M₁ ≤ CD * Λ ^ ((d : ℝ) / 4) *
      (eLpNorm u1.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1))).toReal := by
    rw [← ENNReal.ofReal_toReal hfinN, ← ENNReal.ofReal_mul hKnn] at hsum
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hsum
  -- comparison of the two normalized norms
  have hwL2 : MemL2On (euclideanBall (0 : Vec d) ρ) (fun y => w.toFun y - c) :=
    w.memL2.sub (memLp_const c)
  have hEfin : eLpMeanNormOn (euclideanBall (0 : Vec d) ρ) 2 (fun y => w.toFun y - c) ≠ ⊤ :=
    (memLp_normalizedVolumeOn_of_memLpOn hwL2 (volume_euclideanBall_pos 0 hρ0)).eLpNorm_ne_top
  have hEreal := toReal_eLpMeanNormOn_two hwL2 (volume_euclideanBall_ne_top 0 hρ0.le).lt_top
  have hvolρ := volume_euclideanBall_toReal_eq_unit_mul_of_pos (0 : Vec d) hρ0
  have hω : 0 < (volume (euclideanBall (0 : Vec d) 1)).toReal :=
    volume_euclideanBall_toReal_pos 0 one_pos
  have hN2 : (eLpNorm u1.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1))).toReal ^ 2 =
      (ρ ^ d)⁻¹ * ∫ x in euclideanBall (0 : Vec d) ρ, (w.toFun x - c) ^ 2 := by
    rw [toReal_eLpNorm_sq hu1L2]
    have h1 : (∫ x in euclideanBall (0 : Vec d) 1, u1.toFun x ^ 2) =
        ∫ y in euclideanBall (0 : Vec d) 1,
          (fun x => (w.toFun x - c) ^ 2) (ρ • y + 0) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      change (w.toFun (ρ • y + 0) + -c) ^ 2 = _
      ring
    have h2 := DGNM.setIntegral_comp_affineScale_ball (0 : Vec d) hρ0 1
      (fun x => (w.toFun x - c) ^ 2)
    rw [h1, h2, mul_one]
  have hNE : (eLpNorm u1.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1))).toReal =
      Real.sqrt (volume (euclideanBall (0 : Vec d) 1)).toReal *
        (eLpMeanNormOn (euclideanBall (0 : Vec d) ρ) 2 (fun y => w.toFun y - c)).toReal := by
    rw [hEreal, hvolρ, ← Real.sqrt_mul hω.le]
    rw [← Real.sqrt_sq (ENNReal.toReal_nonneg :
      0 ≤ (eLpNorm u1.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1))).toReal), hN2]
    congr 1
    have hρd : 0 < ρ ^ d := pow_pos hρ0 d
    field_simp
  refine ⟨c + v 0 - M₁ * (2 / ρ) ^ α, ?_⟩
  have hρα : 0 ≤ ρ ^ (-α) := Real.rpow_nonneg hρ0.le _
  have hEtr : 0 ≤ (eLpMeanNormOn (euclideanBall (0 : Vec d) ρ) 2
      (fun y => w.toFun y - c)).toReal := ENNReal.toReal_nonneg
  have h2α : (2 : ℝ) ^ α ≤ 2 := by
    calc (2 : ℝ) ^ α ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
      _ = 2 := Real.rpow_one 2
  have hdiv : (2 / ρ) ^ α = 2 ^ α * ρ ^ (-α) := by
    rw [Real.div_rpow (by norm_num) hρ0.le, Real.rpow_neg hρ0.le, div_eq_mul_inv]
  have hQ : 2 * (M₁ * (2 / ρ) ^ α) ≤
      (4 * Real.sqrt (volume (euclideanBall (0 : Vec d) 1)).toReal * CD *
          Λ ^ ((d : ℝ) / 4)) * ρ ^ (-α) *
        (eLpMeanNormOn (euclideanBall (0 : Vec d) ρ) 2 (fun y => w.toFun y - c)).toReal := by
    have h1 : M₁ ≤ CD * Λ ^ ((d : ℝ) / 4) * (Real.sqrt (volume (euclideanBall (0 : Vec d) 1)).toReal *
        (eLpMeanNormOn (euclideanBall (0 : Vec d) ρ) 2 (fun y => w.toFun y - c)).toReal) := by
      rw [← hNE]; linarith
    calc 2 * (M₁ * (2 / ρ) ^ α) = 2 * M₁ * 2 ^ α * ρ ^ (-α) := by rw [hdiv]; ring
      _ ≤ 2 * M₁ * 2 * ρ ^ (-α) := by
          gcongr
      _ = 4 * M₁ * ρ ^ (-α) := by ring
      _ ≤ 4 * (CD * Λ ^ ((d : ℝ) / 4) * (Real.sqrt (volume (euclideanBall (0 : Vec d) 1)).toReal *
          (eLpMeanNormOn (euclideanBall (0 : Vec d) ρ) 2
            (fun y => w.toFun y - c)).toReal)) * ρ ^ (-α) := by gcongr
      _ = _ := by ring
  filter_upwards [hae2, hae3] with x hx hxm
  have hd := abs_le.1 (hδ x hxm)
  refine ⟨by linarith, ?_⟩
  have hnn : 0 ≤ (4 * Real.sqrt (volume (euclideanBall (0 : Vec d) 1)).toReal * CD *
          Λ ^ ((d : ℝ) / 4)) * ρ ^ (-α) := by positivity
  rw [← ENNReal.ofReal_toReal hEfin, ← ENNReal.ofReal_mul hnn]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith [hd.1, hd.2, hQ, hx]

end

end PDE.Ch4GreenDecay
