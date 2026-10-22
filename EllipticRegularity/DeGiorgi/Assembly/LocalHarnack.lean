module

public import EllipticRegularity.DeGiorgi.Assembly.WeakHarnackChain
public import EllipticRegularity.DeGiorgi.Assembly.HarnackReal

/-!
# The local Harnack inequality

Step 1 of the proof of Theorem 4.18: a Harnack inequality on `B_{1/16}(x₀)` for every
`x₀ ∈ B_{1/2}`, from the weak Harnack inequality and Moser's `L^∞` estimate.
-/

@[expose] public section

open scoped ENNReal Pointwise

namespace PDE.DGNMAssembly

open MeasureTheory Filter

variable {d : ℕ}

theorem rpow_root_le {S N K : ℝ≥0∞} {p : ℝ} (hp : 0 < p) (h : S ^ p ≤ K * N ^ p) :
    S ≤ K ^ (1 / p) * N := by
  have h1 := ENNReal.rpow_le_rpow h (one_div_pos.2 hp).le
  rwa [← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.2 hp).le, ← ENNReal.rpow_mul,
    mul_one_div_cancel hp.ne', ENNReal.rpow_one] at h1

/-- A weak solution is a weak supersolution. -/
theorem IsSolution.toSuper {a : CoeffField d} {U : Set (Vec d)} {u : H1Function U}
    (h : IsWeakDivergenceFormSolutionOn a U u (0 : Vec d → ℝ) 0) :
    IsWeakDivergenceFormSuperharmonicOn a U u := by
  intro φ _
  obtain ⟨h1, h2⟩ := h φ
  exact ⟨h1, le_of_eq h2.symm⟩

/-- A weak solution is a weak subsolution. -/
theorem IsSolution.toSub {a : CoeffField d} {U : Set (Vec d)} {u : H1Function U}
    (h : IsWeakDivergenceFormSolutionOn a U u (0 : Vec d → ℝ) 0) :
    IsWeakDivergenceFormSubharmonicOn a U u := by
  intro φ _
  obtain ⟨h1, h2⟩ := h φ
  exact ⟨h1, le_of_eq h2⟩

/-- Local Harnack inequality on `B_{1/16}(x₀)`, `x₀ ∈ B_{1/2}` (Step 1 of Theorem 4.18). -/
theorem local_harnack (d : ℕ) (hd : 3 ≤ d) (hWH : WeakHarnackConcl d)
    (hMax : MoserLocalMaxConcl d) (hSol : SolAffineTransfer d) :
    ∃ C : ℝ, ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < u.toFun x) →
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) 0 →
      ∀ x₀ ∈ euclideanBall (0 : Vec d) (1 / 2),
        essSup (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall x₀ (1 / 16))) ≤
          ENNReal.ofReal (Real.exp (C * Real.sqrt Λ)) *
            essInf (fun x => ENNReal.ofReal (u.toFun x))
              (volumeOn (euclideanBall x₀ (1 / 16))) := by
  obtain ⟨Cw, hCw, hQw⟩ := hWH
  obtain ⟨CM, hCM, hQM⟩ := hMax
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hd2 : (0 : ℝ) < (d : ℝ) - 2 := by linarith
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  obtain ⟨q0, hq0def⟩ : ∃ q0 : ℝ, q0 = ((d : ℝ) - 1) / d := ⟨_, rfl⟩
  obtain ⟨p0, hp0def⟩ : ∃ p0 : ℝ, p0 = q0 * d / ((d : ℝ) - 2) := ⟨_, rfl⟩
  have hq0pos : 0 < q0 := by rw [hq0def]; apply div_pos <;> linarith
  have hq0lt : q0 < 1 := by rw [hq0def, div_lt_one hd0]; linarith
  have hp0eq : p0 = ((d : ℝ) - 1) / ((d : ℝ) - 2) := by
    rw [hp0def, hq0def]; field_simp
  have hp01 : 1 < p0 := by rw [hp0eq, lt_div_iff₀ hd2]; linarith
  have hp0ratio : p0 / (p0 - 1) = (d : ℝ) - 1 := by
    have : p0 - 1 = 1 / ((d : ℝ) - 2) := by rw [hp0eq]; field_simp; ring
    rw [this, hp0eq]; field_simp
  have h1q0 : 0 < 1 - q0 := by linarith
  obtain ⟨a1, ha1def⟩ : ∃ a1 : ℝ, a1 = CM * ((d : ℝ) - 1) ^ (d : ℝ) * 8 ^ (d : ℝ) := ⟨_, rfl⟩
  have ha1 : 0 < a1 := by
    rw [ha1def]
    have : 0 < (d : ℝ) - 1 := by linarith
    positivity
  have hBpos : 0 < Cw / (1 - q0) ^ Cw := by positivity
  refine ⟨|Real.log a1| + d + |Real.log (Cw / (1 - q0) ^ Cw)|, ?_⟩
  intro Λ a hmeas hell u hpos hsol x₀ hx₀
  have hΛ1 : 1 ≤ Λ := one_le_of_elliptic hell
  have hΛ0 : 0 < Λ := by linarith
  have hsub2 : euclideanBall x₀ (1 / 2) ⊆ euclideanBall (0 : Vec d) 1 :=
    euclideanBall_half_subset_unit_of_center_mem_half hx₀
  have hsub8 : euclideanBall x₀ (1 / 8) ⊆ euclideanBall (0 : Vec d) 1 :=
    (euclideanBall_mono (by norm_num) (by norm_num)).trans hsub2
  have hr2 : (0 : ℝ) < 1 / 2 := by norm_num
  have hr8 : (0 : ℝ) < 1 / 8 := by norm_num
  -- the dilated functions
  obtain ⟨ut, hut, hsolt⟩ := hSol Λ a hmeas hell x₀ (1 / 2) hr2 hsub2 u hsol 1 0
  obtain ⟨ut', hut', hsolt'⟩ := hSol Λ a hmeas hell x₀ (1 / 8) hr8 hsub8 u hsol 1 0
  have hutfun : ut.toFun = fun y => u.toFun (x₀ + (1 / 2 : ℝ) • y) := by
    funext y; rw [hut y]; ring
  have hutfun' : ut'.toFun = fun y => u.toFun (x₀ + (1 / 8 : ℝ) • y) := by
    funext y; rw [hut' y]; ring
  obtain ⟨hmeast, hellt⟩ := coeff_comp_aff hmeas hell x₀ hr2 hsub2
  obtain ⟨hmeast', hellt'⟩ := coeff_comp_aff hmeas hell x₀ hr8 hsub8
  have hpost : ∀ᵐ y ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < ut.toFun y := by
    rw [hutfun]; exact ae_pos_comp_aff hpos x₀ hr2 hsub2
  -- weak Harnack for `ut`
  have hW := hQw Λ _ hmeast hellt ut hpost (IsSolution.toSuper hsolt) q0 hq0pos hq0lt
  rw [← hp0def] at hW
  -- Moser's estimate for `ut'`
  have hM := hQM Λ _ hmeast' hellt' ut' (IsSolution.toSub hsolt') p0 hp01
  rw [hp0ratio] at hM
  -- transport to `u`
  set c' : ℝ≥0∞ := ENNReal.ofReal (((1 / 2 : ℝ) ^ d)⁻¹) with hc'
  set c'' : ℝ≥0∞ := ENNReal.ofReal (((1 / 8 : ℝ) ^ d)⁻¹) with hc''
  have hc'1 : 1 ≤ c' := by
    rw [hc', half_dilation_const]
    have : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
    simpa using ENNReal.ofReal_le_ofReal this
  have hc''eq : c'' = ENNReal.ofReal ((8 : ℝ) ^ (d : ℝ)) := by
    rw [hc'', Real.rpow_natCast, one_div, inv_pow, inv_inv]
  have e14 : (1 / 2 : ℝ) * (1 / 4) = 1 / 8 := by norm_num
  have e12 : (1 / 8 : ℝ) * (1 / 2) = 1 / 16 := by norm_num
  have e11 : (1 / 8 : ℝ) * 1 = 1 / 8 := by norm_num
  have e44 : (1 / 2 : ℝ) * (1 / 4) = 1 / 8 := e14
  set N := eLpNorm u.toFun (ENNReal.ofReal p0) (volumeOn (euclideanBall x₀ (1 / 8))) with hN
  have hW1 : N ≤ ENNReal.ofReal ((Cw / (1 - q0) ^ Cw) ^ Real.sqrt Λ) *
      essInf (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall x₀ (1 / 8))) := by
    rw [hutfun, eLpNorm_comp_aff_ball x₀ hr2 (by norm_num : (0 : ℝ) < 1 / 4), e14] at hW
    have hess := essInf_comp_aff_ball x₀ hr2 (by norm_num : (0 : ℝ) < 1 / 4)
      (fun x => ENNReal.ofReal (u.toFun x))
    rw [e14] at hess
    have hess' : essInf (fun x => ENNReal.ofReal (ut.toFun x))
        (volumeOn (euclideanBall (0 : Vec d) (1 / 4))) =
        essInf (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall x₀ (1 / 8))) := by
      rw [hutfun]; exact hess
    rw [hutfun] at hess'
    rw [hess'] at hW
    exact (le_mul_of_one_le_left zero_le
      (one_le_rpow_of_nonneg hc'1 ENNReal.toReal_nonneg)).trans hW
  -- Moser's estimate transported to `u`
  have hpe : (1 / ENNReal.ofReal p0).toReal * p0 = 1 := by
    rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith), inv_mul_cancel₀
      (by linarith)]
  have hM1 : essSup (fun x => ENNReal.ofReal (u.toFun x))
        (volumeOn (euclideanBall x₀ (1 / 16))) ^ p0 ≤
      ENNReal.ofReal (a1 * Λ ^ ((d : ℝ) / 2)) * N ^ p0 := by
    rw [hutfun', essSup_comp_aff_ball x₀ hr8 (by norm_num : (0 : ℝ) < 1 / 2)
      (fun x => ENNReal.ofReal (u.toFun x)), e12,
      eLpNorm_comp_aff_ball x₀ hr8 (one_pos : (0 : ℝ) < 1), e11,
      ENNReal.mul_rpow_of_nonneg _ _ (by linarith), ← ENNReal.rpow_mul, hpe,
      ENNReal.rpow_one, ← hc'', hc''eq] at hM
    refine hM.trans (le_of_eq ?_)
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ha1def]
    congr 2
    ring
  have hM2 := rpow_root_le (by linarith) hM1
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (one_div_pos.2 (by linarith)).le] at hM2
  have hI : essInf (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall x₀ (1 / 8))) ≤
      essInf (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall x₀ (1 / 16))) := by
    exact essInf_antitone_measure (Measure.absolutelyContinuous_of_le
      (Measure.restrict_mono (euclideanBall_mono (by norm_num) (by norm_num)) le_rfl))
  have hreal := harnack_real_bound (dR := (d : ℝ)) (p := p0) (Λ := Λ) ha1 hBpos hp01.le hΛ1
    hd0.le
  calc _ ≤ _ := hM2
    _ ≤ ENNReal.ofReal ((a1 * Λ ^ ((d : ℝ) / 2)) ^ (1 / p0)) *
        (ENNReal.ofReal ((Cw / (1 - q0) ^ Cw) ^ Real.sqrt Λ) *
          essInf (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall x₀ (1 / 16)))) := by
        gcongr
        exact hW1.trans (by gcongr)
    _ = ENNReal.ofReal ((a1 * Λ ^ ((d : ℝ) / 2)) ^ (1 / p0) *
          (Cw / (1 - q0) ^ Cw) ^ Real.sqrt Λ) *
          essInf (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall x₀ (1 / 16))) := by
        rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
    _ ≤ _ := by
        gcongr

end PDE.DGNMAssembly
