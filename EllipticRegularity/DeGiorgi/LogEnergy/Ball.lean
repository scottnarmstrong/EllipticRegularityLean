module

public import EllipticRegularity.DeGiorgi.LogEnergy.Main

/-!
# The ball form of the logarithmic energy estimate
-/

@[expose] public section

namespace PDE.DGNMLogEnergy

open MeasureTheory Filter Topology Set PDE.DGNM

variable {d : ℕ}

/-- The ball estimate `∫_{B_r(y)} |∇V|² ≤ 4Λ |B_s(y)| / (s-r)²` for `V = log u`,
where `u ≥ δ > 0` is a supersolution on the unit ball. -/
theorem logEnergy_ball_bound {Λ : ℝ} {a : CoeffField d}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hEll : ∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function (euclideanBall (0 : Vec d) 1)}
    (hsuper : IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) u)
    {δ : ℝ} (hδ : 0 < δ) (hu : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1), δ ≤ u.toFun x)
    {V : H1Function (euclideanBall (0 : Vec d) 1)}
    (hV : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1), V.grad x = (u.toFun x)⁻¹ • u.grad x)
    (y : Vec d) {r s : ℝ} (hr : 0 < r) (hrs : r < s) (hys : vecEuclideanNorm y + s < 1) :
    ∫ x in euclideanBall y r, vecNormSq (V.grad x) ≤
      4 * Λ * (volume (euclideanBall y s)).toReal / (s - r) ^ 2 := by
  have hU : IsOpenBoundedConvexDomain (euclideanBall (0 : Vec d) 1) := isOpenBoundedConvexDomain_euclideanBall 0 one_pos
  have hs0 : 0 < s := hr.trans hrs
  have hsU : euclideanBall y s ⊆ (euclideanBall (0 : Vec d) 1) := euclideanBall_subset_unit hs0 hys
  have hΛ : 0 ≤ Λ := by
    have hne : (0 : Vec d) ∈ (euclideanBall (0 : Vec d) 1) := center_mem_euclideanBall (0 : Vec d) one_pos
    exact (hEll 0 hne).Lam_pos.le
  have hVol : 0 ≤ (volume (euclideanBall y s)).toReal := ENNReal.toReal_nonneg
  -- the estimate for a fixed cutoff parameter
  have key : ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 →
      ∫ x in euclideanBall y r, vecNormSq (V.grad x) ≤
        4 * Λ * ((1 - 2 * θ)⁻¹ / ((r + (1 - θ) * (s - r)) - r)) ^ 2 *
          (volume (euclideanBall y s)).toReal := by
    intro θ hθ hθ4
    have hs1r : r < r + (1 - θ) * (s - r) := by
      have : 0 < (1 - θ) * (s - r) := mul_pos (by linarith) (by linarith)
      linarith
    have hs1s : r + (1 - θ) * (s - r) < s := by nlinarith
    let η := sharpBallCutoff y hr hs1r hs1s hθ hθ4
    obtain ⟨hint, hle⟩ := log_energy_cutoff hU ha hEll hsuper hδ hu hV η.smooth
      η.hasCompactSupport (η.tsupport_subset.trans hsU)
    have hG := integrableOn_vecNormSq_classicalGradient (U := euclideanBall (0 : Vec d) 1) η.smooth η.hasCompactSupport
    have hgrad := integral_gradSq_cutoff_le η hU.measurableSet hsU hs0.le hG
    have hmem : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1), x ∈ (euclideanBall (0 : Vec d) 1) :=
      (ae_restrict_iff' hU.measurableSet).2 (Filter.Eventually.of_forall fun _ hx => hx)
    have hBr : euclideanBall y r ⊆ (euclideanBall (0 : Vec d) 1) :=
      (euclideanBall_mono hr.le hrs.le).trans hsU
    have hVint : IntegrableOn (fun x => vecNormSq (V.grad x)) (euclideanBall (0 : Vec d) 1) :=
      integrableOn_vecNormSq_of_memVectorL2On V.gradMemL2
    have hnonneg : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
        0 ≤ η.toFun x ^ 2 * vecDot (V.grad x) (matVecMul (a x) (V.grad x)) := by
      filter_upwards [hmem] with x hx
      exact mul_nonneg (sq_nonneg _) (vecDot_matVecMul_self_nonneg (hEll x hx) _)
    have h1 : ∫ x in euclideanBall y r, vecNormSq (V.grad x) ≤
        ∫ x in euclideanBall y r,
          η.toFun x ^ 2 * vecDot (V.grad x) (matVecMul (a x) (V.grad x)) := by
      refine setIntegral_mono_on (hVint.mono_set hBr) (hint.mono_set hBr)
        (isOpen_euclideanBall y r).measurableSet ?_
      intro x hx
      rw [η.eq_one_on_inner x hx, one_pow, one_mul]
      exact vecNormSq_le_vecDot_matVecMul (hEll x (hBr hx)) _
    have h2 : ∫ x in euclideanBall y r,
          η.toFun x ^ 2 * vecDot (V.grad x) (matVecMul (a x) (V.grad x)) ≤
        ∫ x in (euclideanBall (0 : Vec d) 1), η.toFun x ^ 2 * vecDot (V.grad x) (matVecMul (a x) (V.grad x)) :=
      setIntegral_mono_set hint hnonneg (LE.le.eventuallySubset hBr)
    have hK : 0 ≤ 4 * Λ := by linarith
    calc _ ≤ _ := h1.trans h2
      _ ≤ 4 * Λ * ∫ x in (euclideanBall (0 : Vec d) 1), vecNormSq (classicalGradient η.toFun x) := hle
      _ ≤ 4 * Λ * (((1 - 2 * θ)⁻¹ / ((r + (1 - θ) * (s - r)) - r)) ^ 2 *
            (volume (euclideanBall y s)).toReal) := mul_le_mul_of_nonneg_left hgrad hK
      _ = _ := by ring
  -- pass to the limit `θ → 0`
  have hcont : ContinuousAt (fun θ : ℝ => 4 * Λ * ((1 - 2 * θ)⁻¹ /
      ((r + (1 - θ) * (s - r)) - r)) ^ 2 * (volume (euclideanBall y s)).toReal) 0 := by
    have hden : ((r + (1 - (0 : ℝ)) * (s - r)) - r) ≠ 0 := by
      simp only [sub_zero, one_mul, add_sub_cancel_left]; linarith
    have h1 : ContinuousAt (fun θ : ℝ => (1 - 2 * θ)⁻¹) 0 :=
      ContinuousAt.inv₀ (by fun_prop) (by norm_num)
    have h2 : ContinuousAt (fun θ : ℝ => (1 - 2 * θ)⁻¹ / ((r + (1 - θ) * (s - r)) - r)) 0 :=
      h1.div (by fun_prop) hden
    exact (continuousAt_const.mul (h2.pow 2)).mul continuousAt_const
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hval : 4 * Λ * ((1 - 2 * (0 : ℝ))⁻¹ / ((r + (1 - (0 : ℝ)) * (s - r)) - r)) ^ 2 *
      (volume (euclideanBall y s)).toReal =
      4 * Λ * (volume (euclideanBall y s)).toReal / (s - r) ^ 2 := by
    have : (s - r) ≠ 0 := by linarith
    simp only [mul_zero, sub_zero, inv_one, one_mul, add_sub_cancel_left]
    field_simp
  rw [hval] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with θ hθ
  exact key θ hθ.1 hθ.2

end PDE.DGNMLogEnergy
