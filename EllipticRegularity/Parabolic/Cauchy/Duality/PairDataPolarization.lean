module

public import EllipticRegularity.Parabolic.Cauchy.Duality.PairDataSub
public import EllipticRegularity.Parabolic.Energy.Integrable

@[expose] public section

namespace PDE.Parabolic.Duality

open MeasureTheory Set
open PDE.Parabolic.Energy

private theorem energyData_weightedSlice_sq_integrable {d : ℕ} (D : Energy.Data d)
    {τ : ℝ} (hτ : τ ∈ Icc D.s D.t) :
    IntegrableOn (fun x => D.φ (x, τ) ^ 2 * D.u (x, τ) ^ 2) D.K := by
  have hu : MemLp (fun x => D.u (x, τ)) 2 (volume.restrict D.K) :=
    (D.hus τ hτ).mono_measure (Measure.restrict_mono D.K_subset_K1 le_rfl)
  have hφ : Continuous fun x : Vec d => D.φ (x, τ) ^ 2 :=
    (D.hφ.continuous.comp (continuous_id.prodMk continuous_const)).pow 2
  obtain ⟨M, hM⟩ := D.hK.exists_bound_of_continuousOn hφ.continuousOn
  have hbound : ∀ᵐ x ∂(volume.restrict D.K),
      ‖D.φ (x, τ) ^ 2‖ ≤ M := by
    exact (ae_restrict_iff' D.K_measurable).2
      (Filter.Eventually.of_forall fun x hx => by simpa using hM x hx)
  have hmul := hu.integrable_sq.bdd_mul hφ.aestronglyMeasurable (c := M) hbound
  exact hmul.congr (Filter.Eventually.of_forall fun x => by ring)

/-- Polarize the abstract energy identity to get a bilinear identity on a common compact collar. -/
theorem energyData_cross_identity {d : ℕ} (D E : Energy.Data d)
    (hK : D.K = E.K) (hδ : D.δ0 = E.δ0)
    (hs : D.s = E.s) (ht : D.t = E.t) :
    (∫ x in D.K, D.φ (x, D.t) ^ 2 * D.u (x, D.t) * E.u (x, D.t)) -
        ∫ x in D.K, D.φ (x, D.s) ^ 2 * D.u (x, D.s) * E.u (x, D.s) =
      ∫ z in D.K ×ˢ Ioc D.s D.t,
        2 * D.u z * E.u z * D.φ z * parTimeDeriv D.φ z -
          ∑ i,
            (D.G z i * (D.φ z ^ 2 * E.Du z i +
                2 * D.φ z * E.u z * parSpaceGrad D.φ z i) +
              E.G z i * (D.φ z ^ 2 * D.Du z i +
                2 * D.φ z * D.u z * parSpaceGrad D.φ z i)) := by
  classical
  let P := energyDataAdd D E hK hδ hs ht
  let N := energyDataSub D E hK hδ hs ht
  let Ω : Set (Vec d × ℝ) := D.K ×ˢ Ioc D.s D.t
  let Aplus : Vec d × ℝ → ℝ := fun z =>
    (D.u z + E.u z) ^ 2 * D.φ z * parTimeDeriv D.φ z
  let Aminus : Vec d × ℝ → ℝ := fun z =>
    (D.u z - E.u z) ^ 2 * D.φ z * parTimeDeriv D.φ z
  let Bplus : Vec d × ℝ → ℝ := fun z =>
    ∑ i, (D.G z i + E.G z i) *
      (D.φ z ^ 2 * (D.Du z + E.Du z) i +
        2 * D.φ z * (D.u z + E.u z) * parSpaceGrad D.φ z i)
  let Bminus : Vec d × ℝ → ℝ := fun z =>
    ∑ i, (D.G z i - E.G z i) *
      (D.φ z ^ 2 * (D.Du z - E.Du z) i +
        2 * D.φ z * (D.u z - E.u z) * parSpaceGrad D.φ z i)
  let Across : Vec d × ℝ → ℝ := fun z =>
    4 * D.u z * E.u z * D.φ z * parTimeDeriv D.φ z
  let Bcross : Vec d × ℝ → ℝ := fun z =>
    2 * ∑ i,
      (D.G z i * (D.φ z ^ 2 * E.Du z i +
          2 * D.φ z * E.u z * parSpaceGrad D.φ z i) +
        E.G z i * (D.φ z ^ 2 * D.Du z i +
          2 * D.φ z * D.u z * parSpaceGrad D.φ z i))
  have hPK : P.K = D.K := rfl
  have hPs : P.s = D.s := rfl
  have hPt : P.t = D.t := rfl
  have hPφ : P.φ = D.φ := rfl
  have hPfields := energyDataAdd_fields D E hK hδ hs ht
  have hPu : P.u = fun z => D.u z + E.u z := by
    funext z
    exact hPfields z |>.1
  have hPDu : P.Du = fun z => D.Du z + E.Du z := by
    funext z
    exact hPfields z |>.2.1
  have hPG : P.G = fun z => D.G z + E.G z := by
    funext z
    exact hPfields z |>.2.2
  have hNK : N.K = D.K := rfl
  have hNs : N.s = D.s := rfl
  have hNt : N.t = D.t := rfl
  have hNφ : N.φ = D.φ := rfl
  have hNfields := energyDataSub_fields D E hK hδ hs ht
  have hNu : N.u = fun z => D.u z - E.u z := by
    funext z
    exact hNfields z |>.1
  have hNDu : N.Du = fun z => D.Du z - E.Du z := by
    funext z
    exact hNfields z |>.2.1
  have hNG : N.G = fun z => D.G z - E.G z := by
    funext z
    exact hNfields z |>.2.2
  have hPenergy := P.energy_identity
  have hNenergy := N.energy_identity
  have hP :
      (1 / 2 : ℝ) * (∫ x in D.K,
          D.φ (x, D.t) ^ 2 * (D.u (x, D.t) + E.u (x, D.t)) ^ 2) -
        (1 / 2 : ℝ) * (∫ x in D.K,
          D.φ (x, D.s) ^ 2 * (D.u (x, D.s) + E.u (x, D.s)) ^ 2) =
      (∫ z in Ω, Aplus z) - ∫ z in Ω, Bplus z := by
    simpa only [Energy.Data.μP, hPK, hPs, hPt, hPφ, hPu, hPDu, hPG,
      Ω, Aplus, Bplus, Pi.add_apply] using hPenergy
  have hN :
      (1 / 2 : ℝ) * (∫ x in D.K,
          D.φ (x, D.t) ^ 2 * (D.u (x, D.t) - E.u (x, D.t)) ^ 2) -
        (1 / 2 : ℝ) * (∫ x in D.K,
          D.φ (x, D.s) ^ 2 * (D.u (x, D.s) - E.u (x, D.s)) ^ 2) =
      (∫ z in Ω, Aminus z) - ∫ z in Ω, Bminus z := by
    simpa only [Energy.Data.μP, hNK, hNs, hNt, hNφ, hNu, hNDu, hNG,
      Ω, Aminus, Bminus, Pi.sub_apply] using hNenergy
  have hAplus : IntegrableOn Aplus Ω := by
    have h := P.integrable_A
    change IntegrableOn (fun z => P.u z ^ 2 * P.φ z * parTimeDeriv P.φ z) Ω at h
    simpa only [Energy.Data.μP, hPK, hPs, hPt, hPφ, hPu, Ω, Aplus] using h
  have hAminus : IntegrableOn Aminus Ω := by
    have h := N.integrable_A
    change IntegrableOn (fun z => N.u z ^ 2 * N.φ z * parTimeDeriv N.φ z) Ω at h
    simpa only [Energy.Data.μP, hNK, hNs, hNt, hNφ, hNu, Ω, Aminus] using h
  have hBplus : IntegrableOn Bplus Ω := by
    have h := P.integrable_B
    change IntegrableOn (fun z => ∑ i, P.G z i *
      (P.φ z ^ 2 * P.Du z i + 2 * P.φ z * P.u z * parSpaceGrad P.φ z i)) Ω at h
    simpa only [Energy.Data.μP, hPK, hPs, hPt, hPφ, hPu, hPDu, hPG,
      Ω, Bplus, Pi.add_apply] using h
  have hBminus : IntegrableOn Bminus Ω := by
    have h := N.integrable_B
    change IntegrableOn (fun z => ∑ i, N.G z i *
      (N.φ z ^ 2 * N.Du z i + 2 * N.φ z * N.u z * parSpaceGrad N.φ z i)) Ω at h
    simpa only [Energy.Data.μP, hNK, hNs, hNt, hNφ, hNu, hNDu, hNG,
      Ω, Bminus, Pi.sub_apply] using h
  have hApoint (z : Vec d × ℝ) : Aplus z - Aminus z = Across z := by
    simp only [Aplus, Aminus, Across]
    ring
  have hBpoint (z : Vec d × ℝ) : Bplus z - Bminus z = Bcross z := by
    simp only [Bplus, Bminus, Bcross, Pi.add_apply, Pi.sub_apply]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply congrArg (fun q : Fin d → ℝ => ∑ i, q i)
    funext i
    ring
  have hAcross : IntegrableOn Across Ω :=
    (hAplus.sub hAminus).congr (Filter.Eventually.of_forall fun z => hApoint z)
  have hBcross : IntegrableOn Bcross Ω :=
    (hBplus.sub hBminus).congr (Filter.Eventually.of_forall fun z => hBpoint z)
  have hAint : (∫ z in Ω, Aplus z) - ∫ z in Ω, Aminus z = ∫ z in Ω, Across z := by
    rw [← integral_sub hAplus hAminus]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => hApoint z)
  have hBint : (∫ z in Ω, Bplus z) - ∫ z in Ω, Bminus z = ∫ z in Ω, Bcross z := by
    rw [← integral_sub hBplus hBminus]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => hBpoint z)
  have hcomb :
      ((∫ z in Ω, Aplus z) - ∫ z in Ω, Bplus z) -
        ((∫ z in Ω, Aminus z) - ∫ z in Ω, Bminus z) =
      ∫ z in Ω, (Across z - Bcross z) := by
    calc
      _ = ((∫ z in Ω, Aplus z) - ∫ z in Ω, Aminus z) -
          ((∫ z in Ω, Bplus z) - ∫ z in Ω, Bminus z) := by ring
      _ = (∫ z in Ω, Across z) - ∫ z in Ω, Bcross z := by rw [hAint, hBint]
      _ = _ := by rw [← integral_sub hAcross hBcross]
  have hcross_slice {τ : ℝ} (hτ : τ ∈ Icc D.s D.t) :
      (1 / 2 : ℝ) * (∫ x in D.K,
          D.φ (x, τ) ^ 2 * (D.u (x, τ) + E.u (x, τ)) ^ 2) -
        (1 / 2 : ℝ) * (∫ x in D.K,
          D.φ (x, τ) ^ 2 * (D.u (x, τ) - E.u (x, τ)) ^ 2) =
      2 * ∫ x in D.K, D.φ (x, τ) ^ 2 * D.u (x, τ) * E.u (x, τ) := by
    have hplus : IntegrableOn
        (fun x => D.φ (x, τ) ^ 2 * (D.u (x, τ) + E.u (x, τ)) ^ 2) D.K := by
      have hτP : τ ∈ Icc P.s P.t := by simpa only [hPs, hPt] using hτ
      have h := energyData_weightedSlice_sq_integrable P hτP
      simpa only [hPK, hPφ, hPu] using h
    have hminus : IntegrableOn
        (fun x => D.φ (x, τ) ^ 2 * (D.u (x, τ) - E.u (x, τ)) ^ 2) D.K := by
      have hτN : τ ∈ Icc N.s N.t := by simpa only [hNs, hNt] using hτ
      have h := energyData_weightedSlice_sq_integrable N hτN
      simpa only [hNK, hNφ, hNu] using h
    have hscaledPlus := hplus.const_mul (1 / 2 : ℝ)
    have hscaledMinus := hminus.const_mul (1 / 2 : ℝ)
    calc
      _ = ∫ x in D.K,
          ((1 / 2 : ℝ) * (D.φ (x, τ) ^ 2 * (D.u (x, τ) + E.u (x, τ)) ^ 2) -
            (1 / 2 : ℝ) * (D.φ (x, τ) ^ 2 * (D.u (x, τ) - E.u (x, τ)) ^ 2)) := by
        rw [← integral_const_mul, ← integral_const_mul,
          ← integral_sub hscaledPlus hscaledMinus]
      _ = 2 * ∫ x in D.K, D.φ (x, τ) ^ 2 * D.u (x, τ) * E.u (x, τ) := by
        rw [show (fun x =>
          (1 / 2 : ℝ) * (D.φ (x, τ) ^ 2 * (D.u (x, τ) + E.u (x, τ)) ^ 2) -
            (1 / 2 : ℝ) * (D.φ (x, τ) ^ 2 * (D.u (x, τ) - E.u (x, τ)) ^ 2)) =
          fun x => 2 * (D.φ (x, τ) ^ 2 * D.u (x, τ) * E.u (x, τ)) by
            funext x
            ring, integral_const_mul]
  have hEnd :
      ((1 / 2 : ℝ) * (∫ x in D.K,
          D.φ (x, D.t) ^ 2 * (D.u (x, D.t) + E.u (x, D.t)) ^ 2) -
        (1 / 2 : ℝ) * (∫ x in D.K,
          D.φ (x, D.s) ^ 2 * (D.u (x, D.s) + E.u (x, D.s)) ^ 2)) -
      ((1 / 2 : ℝ) * (∫ x in D.K,
          D.φ (x, D.t) ^ 2 * (D.u (x, D.t) - E.u (x, D.t)) ^ 2) -
        (1 / 2 : ℝ) * (∫ x in D.K,
          D.φ (x, D.s) ^ 2 * (D.u (x, D.s) - E.u (x, D.s)) ^ 2)) =
      2 * ((∫ x in D.K, D.φ (x, D.t) ^ 2 * D.u (x, D.t) * E.u (x, D.t)) -
        ∫ x in D.K, D.φ (x, D.s) ^ 2 * D.u (x, D.s) * E.u (x, D.s)) := by
    have ht := hcross_slice ⟨D.hst.le, le_rfl⟩
    have hs := hcross_slice ⟨le_rfl, D.hst.le⟩
    rw [show
      ((1 / 2 : ℝ) * (∫ x in D.K, D.φ (x, D.t) ^ 2 * (D.u (x, D.t) + E.u (x, D.t)) ^ 2) -
          (1 / 2 : ℝ) * (∫ x in D.K, D.φ (x, D.s) ^ 2 * (D.u (x, D.s) + E.u (x, D.s)) ^ 2)) -
        ((1 / 2 : ℝ) * (∫ x in D.K, D.φ (x, D.t) ^ 2 * (D.u (x, D.t) - E.u (x, D.t)) ^ 2) -
          (1 / 2 : ℝ) * (∫ x in D.K, D.φ (x, D.s) ^ 2 * (D.u (x, D.s) - E.u (x, D.s)) ^ 2)) =
        ((1 / 2 : ℝ) * (∫ x in D.K, D.φ (x, D.t) ^ 2 * (D.u (x, D.t) + E.u (x, D.t)) ^ 2) -
          (1 / 2 : ℝ) * (∫ x in D.K, D.φ (x, D.t) ^ 2 * (D.u (x, D.t) - E.u (x, D.t)) ^ 2)) -
        ((1 / 2 : ℝ) * (∫ x in D.K, D.φ (x, D.s) ^ 2 * (D.u (x, D.s) + E.u (x, D.s)) ^ 2) -
          (1 / 2 : ℝ) * (∫ x in D.K, D.φ (x, D.s) ^ 2 * (D.u (x, D.s) - E.u (x, D.s)) ^ 2)) by ring,
      ht, hs]
    ring
  have hsum :
      ((1 / 2 : ℝ) * (∫ x in D.K,
          D.φ (x, D.t) ^ 2 * (D.u (x, D.t) + E.u (x, D.t)) ^ 2) -
        (1 / 2 : ℝ) * (∫ x in D.K,
          D.φ (x, D.s) ^ 2 * (D.u (x, D.s) + E.u (x, D.s)) ^ 2)) -
      ((1 / 2 : ℝ) * (∫ x in D.K,
          D.φ (x, D.t) ^ 2 * (D.u (x, D.t) - E.u (x, D.t)) ^ 2) -
        (1 / 2 : ℝ) * (∫ x in D.K,
          D.φ (x, D.s) ^ 2 * (D.u (x, D.s) - E.u (x, D.s)) ^ 2)) =
      ((∫ z in Ω, Aplus z) - ∫ z in Ω, Bplus z) -
        ((∫ z in Ω, Aminus z) - ∫ z in Ω, Bminus z) := by rw [hP, hN]
  rw [hEnd, hcomb] at hsum
  have hpoint (z : Vec d × ℝ) :
      Across z - Bcross z = 2 * (2 * D.u z * E.u z * D.φ z * parTimeDeriv D.φ z -
        ∑ i,
          (D.G z i * (D.φ z ^ 2 * E.Du z i +
              2 * D.φ z * E.u z * parSpaceGrad D.φ z i) +
            E.G z i * (D.φ z ^ 2 * D.Du z i +
              2 * D.φ z * D.u z * parSpaceGrad D.φ z i))) := by
    simp only [Across, Bcross]
    ring
  have hfinal : ∫ z in Ω, (Across z - Bcross z) =
      2 * ∫ z in Ω,
        (2 * D.u z * E.u z * D.φ z * parTimeDeriv D.φ z -
          ∑ i,
            (D.G z i * (D.φ z ^ 2 * E.Du z i +
                2 * D.φ z * E.u z * parSpaceGrad D.φ z i) +
              E.G z i * (D.φ z ^ 2 * D.Du z i +
                2 * D.φ z * D.u z * parSpaceGrad D.φ z i))) := by
    rw [show (fun z => Across z - Bcross z) = fun z => 2 *
      (2 * D.u z * E.u z * D.φ z * parTimeDeriv D.φ z -
        ∑ i,
          (D.G z i * (D.φ z ^ 2 * E.Du z i +
              2 * D.φ z * E.u z * parSpaceGrad D.φ z i) +
            E.G z i * (D.φ z ^ 2 * D.Du z i +
              2 * D.φ z * D.u z * parSpaceGrad D.φ z i))) by
        funext z
        exact hpoint z]
    rw [integral_const_mul]
  rw [hfinal] at hsum
  have htwo := hsum
  linarith

end PDE.Parabolic.Duality
