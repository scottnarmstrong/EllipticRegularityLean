module

public import EllipticRegularity.DeGiorgi.Holder.OscDecay

/-!
# The `L^∞` estimate on rescaled balls

From the `L^∞` estimate on `B_1`, stability of solutions under `u ↦ -u` and under
rescaling of balls, we obtain an essential range bound `[-M, M]` for a solution on
`B_{ρ/2}(z)` whenever `B_ρ(z) ⊆ B_1`.
-/

@[expose] public section

namespace PDE.DGNMHolder

open PDE MeasureTheory

variable {d : ℕ}

/-- **`L^∞` bound on a rescaled half ball.** -/
theorem essentialRange_of_linfty {CL : ℝ} (hL : LinftyStatement d CL)
    (hAff : AffineStability d) (hScale : ScaleStability d)
    {Λ : ℝ} {a : CoeffField d}
    (hm : ∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1)))
    (he : ∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function (euclideanBall (0 : Vec d) 1)}
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) 0)
    {z : Vec d} {ρ : ℝ} (hρ : 0 < ρ) (hsub : euclideanBall z ρ ⊆ euclideanBall (0 : Vec d) 1)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ENNReal.ofReal (CL * Λ ^ ((d : ℝ) / 4)) *
        (ENNReal.ofReal ((ρ ^ d)⁻¹) ^ ((1 : ℝ) / 2) *
          eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1))) ≤ ENNReal.ofReal M) :
    EssentialRangeBoundsOn u.toFun (euclideanBall z (ρ / 2)) (-M) M := by
  obtain ⟨a', u', hm', he', hsol', hu'⟩ := hScale Λ a hm he u hsol z ρ hρ hsub
  have hmeas : AEStronglyMeasurable u.toFun (volumeOn (euclideanBall z (ρ * 1))) := by
    rw [mul_one]
    exact u.memL2.aestronglyMeasurable.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hnorm : eLpNorm u'.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1)) ≤
      ENNReal.ofReal ((ρ ^ d)⁻¹) ^ ((1 : ℝ) / 2) *
        eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1)) := by
    calc eLpNorm u'.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1))
        = eLpNorm (fun y => u.toFun (ρ • y + z)) 2 (volumeOn (euclideanBall (0 : Vec d) 1)) :=
          eLpNorm_congr_ae hu'
      _ = ENNReal.ofReal ((ρ ^ d)⁻¹) ^ ((1 : ℝ) / 2) *
            eLpNorm u.toFun 2 (volumeOn (euclideanBall z (ρ * 1))) :=
          eLpNorm_comp_affine_ball hρ z 1 u.toFun hmeas
      _ ≤ _ := by
          rw [mul_one]
          exact mul_le_mul' le_rfl (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl))
  have hsubhalf : euclideanBall (0 : Vec d) (1 / 2) ⊆ euclideanBall (0 : Vec d) 1 :=
    euclideanBall_mono (by norm_num) (by norm_num)
  -- upper bound for u'
  have hup : ∀ᵐ y ∂volumeOn (euclideanBall (0 : Vec d) (1 / 2)), u'.toFun y ≤ M := by
    have h1 := hL Λ a' hm' he' u' hsol'.toSubsolutionOn
    have h2 : essSup (fun x => ENNReal.ofReal (u'.toFun x))
        (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤ ENNReal.ofReal M :=
      h1.trans ((by gcongr : _ ≤ ENNReal.ofReal (CL * Λ ^ ((d : ℝ) / 4)) *
          (ENNReal.ofReal ((ρ ^ d)⁻¹) ^ ((1 : ℝ) / 2) *
          eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1)))).trans hM)
    filter_upwards [ENNReal.ae_le_essSup (μ := volumeOn (euclideanBall (0 : Vec d) (1 / 2)))
      (fun x => ENNReal.ofReal (u'.toFun x))] with y hy
    exact (ENNReal.ofReal_le_ofReal_iff hM0).1 (hy.trans h2)
  -- lower bound via -u'
  obtain ⟨w, hwsol, hw⟩ := hAff Λ a' hm' he' u' hsol' (-1) 0
  have hwnorm : eLpNorm w.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1)) =
      eLpNorm u'.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1)) := by
    rw [eLpNorm_congr_ae hw]
    have : (fun x => -1 * u'.toFun x + 0) = -u'.toFun := by ext x; simp
    rw [this, eLpNorm_neg]
  have hlow : ∀ᵐ y ∂volumeOn (euclideanBall (0 : Vec d) (1 / 2)), -M ≤ u'.toFun y := by
    have h1 := hL Λ a' hm' he' w hwsol.toSubsolutionOn
    have h2 : essSup (fun x => ENNReal.ofReal (w.toFun x))
        (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤ ENNReal.ofReal M := by
      refine h1.trans ?_
      rw [hwnorm]
      exact (by gcongr : _ ≤ ENNReal.ofReal (CL * Λ ^ ((d : ℝ) / 4)) *
          (ENNReal.ofReal ((ρ ^ d)⁻¹) ^ ((1 : ℝ) / 2) *
          eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1)))).trans hM
    have hw' := ae_restrict_of_ae_restrict_of_subset hsubhalf hw
    filter_upwards [ENNReal.ae_le_essSup (μ := volumeOn (euclideanBall (0 : Vec d) (1 / 2)))
      (fun x => ENNReal.ofReal (w.toFun x)), hw'] with y hy hwy
    have := (ENNReal.ofReal_le_ofReal_iff hM0).1 (hy.trans h2)
    rw [hwy] at this
    linarith
  exact range_scale_back hρ hu' (by filter_upwards [hup, hlow] with y h1 h2 using ⟨h2, h1⟩)

end PDE.DGNMHolder
