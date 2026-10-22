module

public import EllipticRegularity.Parabolic.Cauchy.Duality.PairLocalDuality
public import EllipticRegularity.Parabolic.Cauchy.Duality.PairIntegrable
public import EllipticRegularity.Parabolic.Cauchy.Energy.Cutoff
public import EllipticRegularity.Parabolic.Caccioppoli.Assembly

@[expose] public section

namespace PDE.Parabolic.Duality

open MeasureTheory Set
open PDE.Parabolic.Energy

/-- The integrable mixed-flux majorant for forward/adjoint duality. -/
noncomputable def cauchyDualityMixedFluxMajorant {d : ℕ} (a : ParCoeffField d)
    {s t : ℝ} (u w : ParH1Function (univ : Set (Vec d)) (Icc s t))
    (z : Vec d × ℝ) : ℝ :=
  ∑ i : Fin d,
    (|flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z| +
      |flux a u z i * w.toFun (z.1, s + t - z.2)|)

/-- The mixed-flux majorant is integrable on a finite slab. -/
theorem cauchyDualityMixedFluxMajorant_integrable {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s t : ℝ}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s t))
    (u w : ParH1Function (univ : Set (Vec d)) (Icc s t)) :
    IntegrableOn (cauchyDualityMixedFluxMajorant a u w)
      ((univ : Set (Vec d)) ×ˢ Ioc s t) := by
  let Ω : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s t
  have hp := cauchy_duality_mixed_flux_products_integrable ha u w
  have hterm : ∀ i : Fin d, IntegrableOn
      (fun z : Vec d × ℝ =>
      |flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z| +
          |flux a u z i * w.toFun (z.1, s + t - z.2)|) Ω := by
    intro i
    have hi := (hp i).1.abs.add (hp i).2.abs
    change Integrable (fun z : Vec d × ℝ =>
      |flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z| +
        |flux a u z i * w.toFun (z.1, s + t - z.2)|) (volume.restrict Ω)
    have heq : (fun z : Vec d × ℝ =>
        |flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z| +
          |flux a u z i * w.toFun (z.1, s + t - z.2)|) =
      (fun z => |u.toFun z * flux (parAdjCoeff a (s + t)) w
          (z.1, s + t - z.2) i| +
        |w.toFun (z.1, s + t - z.2) * flux a u z i|) := by
      funext z
      congr 1 <;> rw [mul_comm]
    rw [heq]
    exact hi
  have hsum : IntegrableOn (fun z : Vec d × ℝ =>
      ∑ i : Fin d,
        (|flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z| +
          |flux a u z i * w.toFun (z.1, s + t - z.2)|)) Ω :=
    integrable_finsetSum _ fun i _ => hterm i
  change IntegrableOn (fun z : Vec d × ℝ =>
      ∑ i : Fin d,
        (|flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z| +
          |flux a u z i * w.toFun (z.1, s + t - z.2)|)) Ω
  exact hsum

/-- The cutoff error in the bilinear identity is bounded by the mixed-flux majorant. -/
theorem cauchy_duality_cutoff_flux_integral_bound {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s t R : ℝ} (hR : 0 < R)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s t))
    (u w : ParH1Function (univ : Set (Vec d)) (Icc s t))
    (χ : ParCutoff (univ : Set (Vec d)) (Icc s t))
    (hχbound : ∀ z, |χ.toFun z| ≤ 1)
    (hgradbound : ∀ z i, |parSpaceGrad χ.toFun z i| ≤ 32 / R)
    {K : Set (Vec d)} :
    |∫ z in K ×ˢ Ioc s t,
        2 * χ.toFun z * ∑ i : Fin d,
          (flux a u z i * w.toFun (z.1, s + t - z.2) -
            flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z) *
              parSpaceGrad χ.toFun z i| ≤
      (64 / R) * ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        cauchyDualityMixedFluxMajorant a u w z := by
  let Ω : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s t
  let ΩK : Set (Vec d × ℝ) := K ×ˢ Ioc s t
  let M : Vec d × ℝ → ℝ := cauchyDualityMixedFluxMajorant a u w
  let F : Vec d × ℝ → ℝ := fun z =>
    2 * χ.toFun z * ∑ i : Fin d,
      (flux a u z i * w.toFun (z.1, s + t - z.2) -
        flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z) *
          parSpaceGrad χ.toFun z i
  have hM : IntegrableOn M Ω := by
    simpa [M, Ω] using cauchyDualityMixedFluxMajorant_integrable ha u w
  have hsubset : ΩK ⊆ Ω := by
    intro z hz
    exact ⟨mem_univ z.1, hz.2⟩
  have hle : volume.restrict ΩK ≤ volume.restrict Ω := Measure.restrict_mono hsubset le_rfl
  change Integrable M (volume.restrict Ω) at hM
  have hMk : Integrable M (volume.restrict ΩK) := hM.mono_measure hle
  have hC : 0 ≤ (64 : ℝ) / R := by positivity
  have hMnonneg : ∀ᵐ z ∂(volume.restrict Ω), 0 ≤ M z := by
    filter_upwards [] with z
    exact Finset.sum_nonneg fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hp := cauchy_duality_mixed_flux_products_integrable ha u w
  have hpMeas : ∀ i : Fin d, AEStronglyMeasurable
      (fun z : Vec d × ℝ =>
        flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z)
      (volume.restrict Ω) := fun i => by
        simpa only [Ω] using ((hp i).1.aestronglyMeasurable.congr
          (Filter.Eventually.of_forall fun z => by rw [mul_comm]))
  have hqMeas : ∀ i : Fin d, AEStronglyMeasurable
      (fun z : Vec d × ℝ =>
        flux a u z i * w.toFun (z.1, s + t - z.2))
      (volume.restrict Ω) := fun i => by
        simpa only [Ω] using ((hp i).2.aestronglyMeasurable.congr
          (Filter.Eventually.of_forall fun z => by rw [mul_comm]))
  have hgradCont : Continuous (parSpaceGrad χ.toFun) :=
    PDE.ParabCaccioppoli.continuous_parSpaceGrad χ
  have hφCont : Continuous χ.toFun := χ.contDiff.continuous
  have hFmeas : AEStronglyMeasurable F (volume.restrict Ω) := by
    have hsum : AEStronglyMeasurable (fun z : Vec d × ℝ =>
        ∑ i : Fin d,
          ((flux a u z i * w.toFun (z.1, s + t - z.2) -
              flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z) *
            parSpaceGrad χ.toFun z i)) (volume.restrict Ω) := by
      refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
      have hpq : AEStronglyMeasurable
          (fun z : Vec d × ℝ =>
            flux a u z i * w.toFun (z.1, s + t - z.2) -
              flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z)
          (volume.restrict Ω) := (hqMeas i).sub (hpMeas i)
      exact hpq.mul (((continuous_apply i).comp hgradCont).aestronglyMeasurable)
    exact hφCont.aestronglyMeasurable.const_mul _ |>.mul hsum
  have hpoint : ∀ z : Vec d × ℝ, ‖F z‖ ≤ (64 / R) * M z := by
    intro z
    rw [Real.norm_eq_abs]
    dsimp [F, M, cauchyDualityMixedFluxMajorant]
    have hχ : |2 * χ.toFun z| ≤ 2 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [hχbound z]
    have hgrad : ∀ i : Fin d, |parSpaceGrad χ.toFun z i| ≤ 32 / R :=
      fun i => hgradbound z i
    have hterm : ∀ i : Fin d,
        |(flux a u z i * w.toFun (z.1, s + t - z.2) -
            flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z) *
              parSpaceGrad χ.toFun z i| ≤
          (|flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z| +
            |flux a u z i * w.toFun (z.1, s + t - z.2)|) * (32 / R) := by
      intro i
      rw [abs_mul]
      have hdiff :
          |flux a u z i * w.toFun (z.1, s + t - z.2) -
              flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z| ≤
            |flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z| +
              |flux a u z i * w.toFun (z.1, s + t - z.2)| := by
        simpa [abs_mul, mul_comm, add_comm] using abs_sub_le
          (flux a u z i * w.toFun (z.1, s + t - z.2)) (0 : ℝ)
          (flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z)
      have hRnonneg : 0 ≤ (32 : ℝ) / R := by positivity
      calc
        |flux a u z i * w.toFun (z.1, s + t - z.2) -
            flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z| *
              |parSpaceGrad χ.toFun z i| ≤
            (|flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z| +
              |flux a u z i * w.toFun (z.1, s + t - z.2)|) *
                |parSpaceGrad χ.toFun z i| :=
          mul_le_mul_of_nonneg_right hdiff (abs_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left (hgrad i) (by positivity)
    have hsum :
        ∑ i : Fin d,
          |(flux a u z i * w.toFun (z.1, s + t - z.2) -
              flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z) *
                parSpaceGrad χ.toFun z i| ≤
          ∑ i : Fin d,
            ((|flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z| +
                |flux a u z i * w.toFun (z.1, s + t - z.2)|) * (32 / R)) := by
      exact Finset.sum_le_sum fun i _ => hterm i
    have hsum' :
        ∑ i : Fin d,
          |(flux a u z i * w.toFun (z.1, s + t - z.2) -
              flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z) *
                parSpaceGrad χ.toFun z i| ≤
          (32 / R) * ∑ i : Fin d,
            (|flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z| +
              |flux a u z i * w.toFun (z.1, s + t - z.2)|) := by
      calc
        _ ≤ ∑ i : Fin d,
            ((|flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z| +
                |flux a u z i * w.toFun (z.1, s + t - z.2)|) * (32 / R)) := hsum
        _ = _ := by
          calc
            _ = ∑ i : Fin d,
                ((32 / R) *
                  (|flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z| +
                    |flux a u z i * w.toFun (z.1, s + t - z.2)|)) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = _ := by rw [Finset.mul_sum]
    have hsumabs :
        |∑ i : Fin d,
          (flux a u z i * w.toFun (z.1, s + t - z.2) -
            flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z) *
                  parSpaceGrad χ.toFun z i| ≤
          ∑ i : Fin d,
            |(flux a u z i * w.toFun (z.1, s + t - z.2) -
                flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z) *
                  parSpaceGrad χ.toFun z i| := by
      simpa using Finset.abs_sum_le_sum_abs
        (fun i : Fin d =>
          (flux a u z i * w.toFun (z.1, s + t - z.2) -
            flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z) *
              parSpaceGrad χ.toFun z i) Finset.univ
    have hsumM : 0 ≤ ∑ i : Fin d,
        (|flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z| +
          |flux a u z i * w.toFun (z.1, s + t - z.2)|) :=
      Finset.sum_nonneg fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
    calc
      |2 * χ.toFun z * ∑ i : Fin d,
          (flux a u z i * w.toFun (z.1, s + t - z.2) -
            flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z) *
              parSpaceGrad χ.toFun z i| =
          |2 * χ.toFun z| * |∑ i : Fin d,
            (flux a u z i * w.toFun (z.1, s + t - z.2) -
              flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z) *
                parSpaceGrad χ.toFun z i| := abs_mul _ _
      _ ≤ 2 * ((32 / R) * ∑ i : Fin d,
          (|flux (parAdjCoeff a (s + t)) w (z.1, s + t - z.2) i * u.toFun z| +
            |flux a u z i * w.toFun (z.1, s + t - z.2)|)) := by
        exact mul_le_mul hχ (le_trans hsumabs hsum') (abs_nonneg _) (by positivity)
      _ = (64 / R) * M z := by
        dsimp [M, cauchyDualityMixedFluxMajorant]
        ring
  have hFint : IntegrableOn F Ω := by
    refine Integrable.mono' (hM.const_mul (64 / R)) hFmeas ?_
    filter_upwards [] with z
    exact hpoint z
  change Integrable F (volume.restrict Ω) at hFint
  have hFK : Integrable F (volume.restrict ΩK) := hFint.mono_measure hle
  have hpointAE : ∀ᵐ z ∂(volume.restrict ΩK), ‖F z‖ ≤ (64 / R) * M z :=
    Filter.Eventually.of_forall hpoint
  have hmono : ∫ z in ΩK, ‖F z‖ ≤ ∫ z in ΩK, (64 / R) * M z :=
    integral_mono_ae hFK.norm (hMk.const_mul (64 / R)) hpointAE
  have hnorm : |∫ z in ΩK, F z| ≤ ∫ z in ΩK, ‖F z‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (μ := volume.restrict ΩK) F)
  have hMrestrict : ∫ z in ΩK, M z ≤ ∫ z in Ω, M z :=
    integral_mono_measure hle hMnonneg hM
  calc
    |∫ z in ΩK, F z| ≤ ∫ z in ΩK, ‖F z‖ := hnorm
    _ ≤ ∫ z in ΩK, (64 / R) * M z := hmono
    _ = (64 / R) * ∫ z in ΩK, M z := by rw [integral_const_mul]
    _ ≤ (64 / R) * ∫ z in Ω, M z := mul_le_mul_of_nonneg_left hMrestrict hC

end PDE.Parabolic.Duality
