module

public import EllipticRegularity.Ch4.GreenDecay.HarmonicOsc
public import PDEFoundation.PDE.EllipticChange
public import PDEFoundation.Geometry.EuclideanBall.EllipticImage
public import PDEFoundation.Measure.LinearAverage
public import PDEFoundation.Sobolev.H1.Linear

/-!
# Oscillation decay for constant coefficients (proof of Corollary 4.37)

For a constant elliptic matrix `A`, a solution of `-div (A ∇w) = 0` in `B_ρ` (`ρ ≥ 4`) becomes harmonic
after the canonical elliptic normalization `y = e x` (removal of the skew part, then the inverse square
root of the symmetric part).  The Lipschitz estimate of `HarmonicOsc.lean` on the convex set `e(B_2)`,
with balls of radius `σ = ρ / (2 √Λ)`, gives
`ess osc_{B_2} w ≤ C Λ^{(d+2)/4} ρ⁻¹ ‖w - (w)_{B_ρ}‖_{L̲²(B_ρ)}`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4GreenDecay

open MeasureTheory PDE

noncomputable section

variable {d : ℕ}

/-- The normalization sends a constant-coefficient solution to a harmonic function. -/
theorem harmonic_of_constCoeff {Λ : ℝ} {A : Mat d} (hA : IsEllipticMatrix 1 Λ A)
    {U : Set (Vec d)} {w : H1Function U}
    (hsol : IsWeakDivergenceFormSolutionOn (fun _ : Vec d => A) U w (0 : Vec d → ℝ) 0) :
    IsWeakDivergenceFormSolutionOn (fun _ : Vec d => (1 : Mat d))
      (ellipticNormalizerContinuousLinearEquiv hA '' U)
      (w.compLinearEquiv (ellipticNormalizerContinuousLinearEquiv hA)) (0 : Vec d → ℝ) 0 := by
  have h := hsol.ellipticNormalize hA
  have hone : ∀ x : Vec d, vecNormSq x ≤ vecDot x (matVecMul A x) := by
    intro x
    simpa only [one_mul] using hA.coercive x
  have hS : (symmPart A).PosDef := symmPart_posDef_of_one_le hone
  have hcoef : (fun _ : Vec d => ellipticNormalizer A * (A - skewPart A) *
      matTranspose (ellipticNormalizer A)) = fun _ => (1 : Mat d) := by
    funext _
    have : A - skewPart A = symmPart A := by
      ext i j
      simp [skewPart, symmPart]
      ring
    rw [this]
    exact ellipticNormalizer_mul_symmPart_mul_transpose hS
  have hF : (fun y : Vec d => matVecMul (ellipticNormalizer A)
      ((0 : Vec d → Vec d) ((ellipticNormalizerContinuousLinearEquiv hA).symm y))) =
      (0 : Vec d → Vec d) := by
    funext y
    ext i
    simp [matVecMul]
  dsimp only at h
  rw [hcoef, hF] at h
  exact h

/-- Arithmetic of the powers of `Λ` in the constant-coefficient constant. -/
theorem sqrt_mul_sqrt_sqrt_pow {Λ : ℝ} (hΛ : 0 < Λ) (d : ℕ) :
    Real.sqrt Λ * Real.sqrt (Real.sqrt Λ ^ d) = Λ ^ (((d : ℝ) + 2) / 4) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul hΛ.le, ← Real.rpow_mul hΛ.le, ← Real.rpow_add hΛ]
  congr 1
  ring

/-- **Oscillation bound on `B_2` for constant coefficients.** -/
theorem osc_of_const (hd : 0 < d) :
    ∃ Cs : ℝ, 0 < Cs ∧ ∀ {Λ ρ : ℝ} {A : Mat d}, IsEllipticMatrix 1 Λ A → 4 ≤ ρ →
      ∀ w : H1Function (euclideanBall (0 : Vec d) ρ),
      IsWeakDivergenceFormSolutionOn (fun _ : Vec d => A) (euclideanBall (0 : Vec d) ρ) w
        (0 : Vec d → ℝ) 0 →
      ∃ m : ℝ, ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 2)),
        m ≤ w.toFun x ∧
        ENNReal.ofReal (w.toFun x - m) ≤
          ENNReal.ofReal (Cs * Λ ^ (((d : ℝ) + 2) / 4) * ρ ^ (-(1 : ℝ))) *
            eLpMeanNormOn (euclideanBall (0 : Vec d) ρ) 2
              (fun y => w.toFun y - integralAverage (euclideanBall (0 : Vec d) ρ) w.toFun) := by
  obtain ⟨K₀, hK₀, hlip⟩ := harmonic_lipschitz hd
  refine ⟨8 * K₀ * Real.sqrt ((2 : ℝ) ^ d), by positivity, ?_⟩
  intro Λ ρ A hA hρ w hw
  have hρ0 : 0 < ρ := by linarith
  have hΛ1 : 1 ≤ Λ := hA.lam_le_Lam
  have hΛ0 : 0 < Λ := by linarith
  have hsΛ : 0 < Real.sqrt Λ := Real.sqrt_pos.2 hΛ0
  obtain ⟨e, he⟩ : ∃ e : Vec d ≃L[ℝ] Vec d, e = ellipticNormalizerContinuousLinearEquiv hA :=
    ⟨_, rfl⟩
  have hĥ := harmonic_of_constCoeff hA hw
  rw [← he] at hĥ
  obtain ⟨c, hc⟩ : ∃ c, c = integralAverage (euclideanBall (0 : Vec d) ρ) w.toFun := ⟨_, rfl⟩
  rw [← hc]
  set σ : ℝ := (ρ / 2) / Real.sqrt Λ with hσdef
  have hσ : 0 < σ := by positivity
  have hEopen : IsOpen (e '' euclideanBall (0 : Vec d) ρ) :=
    e.toHomeomorph.isOpenMap _ (isOpen_euclideanBall 0 ρ)
  have hDopen : IsOpen (e '' euclideanBall (0 : Vec d) 2) :=
    e.toHomeomorph.isOpenMap _ (isOpen_euclideanBall 0 2)
  have hDconv : Convex ℝ (e '' euclideanBall (0 : Vec d) 2) :=
    (convex_euclideanBall (0 : Vec d) 2).linear_image (e : Vec d →ₗ[ℝ] Vec d)
  have hDE : ∀ y ∈ e '' euclideanBall (0 : Vec d) 2,
      euclideanBall y σ ⊆ e '' euclideanBall (0 : Vec d) ρ := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := euclideanBall_half_subset_ellipticNormalizer_image hA hρ0 x
    rw [← he] at h1
    refine h1.trans (Set.image_mono ?_)
    apply euclideanBall_subset_of_center_norm_add_le (by positivity) hρ0
    have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hx
    rw [sub_zero] at hx' ⊢
    linarith
  have hEsub : e '' euclideanBall (0 : Vec d) ρ ⊆ euclideanBall (0 : Vec d) ρ := by
    have h1 := ellipticNormalizer_image_euclideanBall_subset hA hρ0 (0 : Vec d)
    rw [← he, map_zero] at h1
    exact h1
  have hDsub : e '' euclideanBall (0 : Vec d) 2 ⊆ euclideanBall (0 : Vec d) 2 := by
    have h1 := ellipticNormalizer_image_euclideanBall_subset hA (by norm_num : (0 : ℝ) < 2)
      (0 : Vec d)
    rw [← he, map_zero] at h1
    exact h1
  have hBρfin : volume (euclideanBall (0 : Vec d) ρ) < ∞ :=
    (volume_euclideanBall_ne_top 0 hρ0.le).lt_top
  have hBρpos : 0 < volume (euclideanBall (0 : Vec d) ρ) := volume_euclideanBall_pos 0 hρ0
  have hEpos : 0 < volume (e '' euclideanBall (0 : Vec d) ρ) :=
    volume_image_linearEquiv_pos e hBρpos
  have hEfin : volume (e '' euclideanBall (0 : Vec d) ρ) < ∞ :=
    volume_image_linearEquiv_lt_top e hBρfin
  set ĥ := w.compLinearEquiv e with hĥdef
  have hĥsq : ∀ x, (ĥ.toFun (e x) - c) ^ 2 = (w.toFun x - c) ^ 2 := fun x => by
    change (w.toFun (e.symm (e x)) - c) ^ 2 = _
    rw [e.symm_apply_apply]
  have hĥL2 : MemL2On (e '' euclideanBall (0 : Vec d) ρ) (fun y => ĥ.toFun y - c) := by
    have : IsFiniteMeasure (volumeOn (e '' euclideanBall (0 : Vec d) ρ)) :=
      ⟨by simpa [volumeOn] using hEfin⟩
    exact ĥ.memL2.sub (memLp_const c)
  have hĥint : IntegrableOn (fun y => (ĥ.toFun y - c) ^ 2) (e '' euclideanBall (0 : Vec d) ρ) :=
    hĥL2.integrable_sq
  have havgE : integralAverage (e '' euclideanBall (0 : Vec d) ρ) (fun y => (ĥ.toFun y - c) ^ 2) =
      integralAverage (euclideanBall (0 : Vec d) ρ) (fun x => (w.toFun x - c) ^ 2) := by
    have := integralAverage_comp_linearEquiv e hBρpos hBρfin (fun y => (ĥ.toFun y - c) ^ 2)
    simp only [hĥsq] at this
    exact this.symm
  have hVE : (volume (e '' euclideanBall (0 : Vec d) ρ)).toReal ≤
      (volume (euclideanBall (0 : Vec d) ρ)).toReal :=
    ENNReal.toReal_mono hBρfin.ne (measure_mono hEsub)
  have hVEpos : 0 < (volume (e '' euclideanBall (0 : Vec d) ρ)).toReal :=
    ENNReal.toReal_pos hEpos.ne' hEfin.ne
  have hwc0 : 0 ≤ integralAverage (euclideanBall (0 : Vec d) ρ) (fun x => (w.toFun x - c) ^ 2) :=
    mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) (integral_nonneg fun x => sq_nonneg _)
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = Real.sqrt ((2 * Real.sqrt Λ) ^ d *
      integralAverage (euclideanBall (0 : Vec d) ρ) (fun x => (w.toFun x - c) ^ 2)) := ⟨_, rfl⟩
  have hM : ∀ y ∈ e '' euclideanBall (0 : Vec d) 2, Real.sqrt (integralAverage (euclideanBall y σ)
      (fun x => (ĥ.toFun x - c) ^ 2)) ≤ M := by
    intro y hy
    rw [hMdef]
    refine Real.sqrt_le_sqrt ?_
    have hsub := hDE y hy
    have hIle : (∫ x in euclideanBall y σ, (ĥ.toFun x - c) ^ 2) ≤
        ∫ x in e '' euclideanBall (0 : Vec d) ρ, (ĥ.toFun x - c) ^ 2 :=
      setIntegral_mono_set hĥint (Filter.Eventually.of_forall fun x => sq_nonneg _)
        (Filter.Eventually.of_forall hsub)
    have hIE : (∫ x in e '' euclideanBall (0 : Vec d) ρ, (ĥ.toFun x - c) ^ 2) =
        (volume (e '' euclideanBall (0 : Vec d) ρ)).toReal *
          integralAverage (e '' euclideanBall (0 : Vec d) ρ) (fun y => (ĥ.toFun y - c) ^ 2) := by
      unfold integralAverage
      rw [← mul_assoc, mul_inv_cancel₀ hVEpos.ne', one_mul]
    have hvolσ := volume_euclideanBall_toReal_pos y hσ
    have hratio := volume_euclideanBall_toReal_div_eq_div_pow (0 : Vec d) y hσ hρ0
    have hρσ : ρ / σ = 2 * Real.sqrt Λ := by
      rw [hσdef]; field_simp
    rw [hρσ] at hratio
    unfold integralAverage
    calc (volume (euclideanBall y σ)).toReal⁻¹ * ∫ x in euclideanBall y σ, (ĥ.toFun x - c) ^ 2
        ≤ (volume (euclideanBall y σ)).toReal⁻¹ *
          ((volume (e '' euclideanBall (0 : Vec d) ρ)).toReal *
            integralAverage (euclideanBall (0 : Vec d) ρ) (fun x => (w.toFun x - c) ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 ENNReal.toReal_nonneg)
          rw [← havgE, ← hIE]; exact hIle
      _ ≤ (volume (euclideanBall y σ)).toReal⁻¹ *
          ((volume (euclideanBall (0 : Vec d) ρ)).toReal *
            integralAverage (euclideanBall (0 : Vec d) ρ) (fun x => (w.toFun x - c) ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 ENNReal.toReal_nonneg)
          exact mul_le_mul_of_nonneg_right hVE hwc0
      _ = (2 * Real.sqrt Λ) ^ d *
          ((volume (euclideanBall (0 : Vec d) ρ)).toReal⁻¹ *
            ∫ x in euclideanBall (0 : Vec d) ρ, (w.toFun x - c) ^ 2) := by
          rw [← hratio]
          unfold integralAverage
          field_simp
  obtain ⟨g, hgae, hglip⟩ := hlip hEopen ĥ hĥ hσ hDopen hDconv hDE (c := c) (M := M) hM
  have hM0 : 0 ≤ M := by rw [hMdef]; exact Real.sqrt_nonneg _
  have h0D : (0 : Vec d) ∈ e '' euclideanBall (0 : Vec d) 2 :=
    ⟨0, center_mem_euclideanBall 0 (by norm_num), map_zero e⟩
  -- a.e. transfer of `g = ĥ` to `g ∘ e = w`
  have hx_ae : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 2), g (e x) = w.toFun x := by
    have h1 : ∀ᵐ y ∂(Measure.map e (volumeOn (euclideanBall (0 : Vec d) 2))), g y = ĥ.toFun y := by
      rw [map_linearEquiv_volumeOn]
      exact Measure.ae_smul_measure hgae _
    have h2 := (e.toHomeomorph.measurableEmbedding.ae_map_iff).1 h1
    filter_upwards [h2] with x hx
    have hx' : g (e x) = ĥ.toFun (e x) := hx
    rw [hx']
    change w.toFun (e.symm (e x)) = _
    rw [e.symm_apply_apply]
  have hmem : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 2), x ∈ euclideanBall (0 : Vec d) 2 :=
    (ae_restrict_iff' (measurableSet_euclideanBall _ _)).2
      (Filter.Eventually.of_forall fun x hx => hx)
  -- the final real bound
  have hEfinite : eLpMeanNormOn (euclideanBall (0 : Vec d) ρ) 2 (fun y => w.toFun y - c) ≠ ⊤ := by
    have : IsFiniteMeasure (volumeOn (euclideanBall (0 : Vec d) ρ)) :=
      isFiniteMeasure_volumeOn_euclideanBall 0 hρ0.le
    have hwL2 : MemL2On (euclideanBall (0 : Vec d) ρ) (fun y => w.toFun y - c) :=
      w.memL2.sub (memLp_const c)
    exact (memLp_normalizedVolumeOn_of_memLpOn hwL2 hBρpos).eLpNorm_ne_top
  have hwL2 : MemL2On (euclideanBall (0 : Vec d) ρ) (fun y => w.toFun y - c) := by
    have : IsFiniteMeasure (volumeOn (euclideanBall (0 : Vec d) ρ)) :=
      isFiniteMeasure_volumeOn_euclideanBall 0 hρ0.le
    exact w.memL2.sub (memLp_const c)
  have hEreal := toReal_eLpMeanNormOn_two hwL2 hBρfin
  have hEnn : 0 ≤ (eLpMeanNormOn (euclideanBall (0 : Vec d) ρ) 2 (fun y => w.toFun y - c)).toReal :=
    ENNReal.toReal_nonneg
  have hMeq : M = Real.sqrt ((2 * Real.sqrt Λ) ^ d) *
      (eLpMeanNormOn (euclideanBall (0 : Vec d) ρ) 2 (fun y => w.toFun y - c)).toReal := by
    rw [hMdef, hEreal, ← Real.sqrt_mul (by positivity)]
    congr 1
    unfold integralAverage
    rw [div_eq_inv_mul]
  have hQeq : 2 * (K₀ * σ⁻¹ * M) * 2 =
      (8 * K₀ * Real.sqrt ((2 : ℝ) ^ d)) * Λ ^ (((d : ℝ) + 2) / 4) * ρ ^ (-(1 : ℝ)) *
        (eLpMeanNormOn (euclideanBall (0 : Vec d) ρ) 2 (fun y => w.toFun y - c)).toReal := by
    have h1 : σ⁻¹ = 2 * Real.sqrt Λ / ρ := by
      rw [hσdef]; field_simp
    have h2 : Real.sqrt ((2 * Real.sqrt Λ) ^ d) =
        Real.sqrt ((2 : ℝ) ^ d) * Real.sqrt (Real.sqrt Λ ^ d) := by
      rw [mul_pow, Real.sqrt_mul (by positivity)]
    rw [hMeq, h1, h2, Real.rpow_neg hρ0.le, Real.rpow_one, ← sqrt_mul_sqrt_sqrt_pow hΛ0 d]
    field_simp
    ring
  refine ⟨g 0 - K₀ * σ⁻¹ * M * 2, ?_⟩
  filter_upwards [hx_ae, hmem] with x hx hxm
  have hyD : e x ∈ e '' euclideanBall (0 : Vec d) 2 := ⟨x, hxm, rfl⟩
  have hLip := hglip _ hyD 0 h0D
  have hnorm : vecEuclideanNorm (e x - 0) ≤ 2 := by
    have h1 := hDsub hyD
    exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 h1).le.trans_eq (by simp)
    |>.trans_eq' (by simp)
  have hKM : 0 ≤ K₀ * σ⁻¹ * M := by positivity
  have hd2 : |g (e x) - g 0| ≤ K₀ * σ⁻¹ * M * 2 :=
    hLip.trans (mul_le_mul_of_nonneg_left hnorm hKM)
  have hab := abs_le.1 hd2
  rw [hx] at hab
  refine ⟨by linarith [hab.1], ?_⟩
  have hnn : 0 ≤ (8 * K₀ * Real.sqrt ((2 : ℝ) ^ d)) * Λ ^ (((d : ℝ) + 2) / 4) *
      ρ ^ (-(1 : ℝ)) := by positivity
  rw [← ENNReal.ofReal_toReal hEfinite, ← ENNReal.ofReal_mul hnn]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← hQeq]
  linarith [hab.2]

end

end PDE.Ch4GreenDecay
