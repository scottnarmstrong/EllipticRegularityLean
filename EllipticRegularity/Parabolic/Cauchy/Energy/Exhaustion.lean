/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.Cauchy.Energy.Density
public import EllipticRegularity.Parabolic.Cauchy.Energy.Local
public import EllipticRegularity.Parabolic.Caccioppoli.Matrix

/-! # Integrable terms in the whole-space cutoff identity -/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Energy

open MeasureTheory Set Filter Topology

/-- The round cutoff at the `n`th stage of the spatial exhaustion. -/
noncomputable def cauchyExhaustionCutoff {d : ℕ} (s T : ℝ) (n : ℕ) :
    ParCutoff (univ : Set (Vec d)) (Icc s T) :=
  cauchyParabolicCutoff s T ((n : ℝ) + 2) (by positivity)

/-- Every fixed spatial point eventually lies in the inner ball of the exhaustion cutoff. -/
theorem cauchyExhaustionCutoff_eventually_one {d : ℕ} (s T : ℝ) (x : Vec d) (t : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      (cauchyExhaustionCutoff s T n).toFun (x, t) = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (vecEuclideanNorm x)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) + 2 := by positivity
  have hxnorm : vecEuclideanNorm x < (n : ℝ) + 2 := by linarith
  have hxball : x ∈ euclideanBall 0 ((n : ℝ) + 2) := by
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hnpos).2
    simpa using hxnorm
  exact cauchyParabolicCutoff_eq_one s T ((n : ℝ) + 2) (by positivity) hxball (t := t)

/-- The energy density is integrable on every shorter time slab. -/
theorem cauchyEnergyDensity_integrable_Ioc {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T)) {t : ℝ}
    (ht : t ∈ Icc s T) :
    IntegrableOn (cauchyEnergyDensity a u) ((univ : Set (Vec d)) ×ˢ Ioc s t) := by
  apply (cauchyEnergyDensity_integrable ha u).mono_set
  exact prod_mono subset_rfl (fun τ hτ => ⟨hτ.1.le, hτ.2.trans ht.2⟩)

/-- The local identity's flux integrand splits into the bulk energy density and a cross-flux term. -/
theorem cauchy_cutoff_flux_split {d : ℕ} {a : ParCoeffField d} {s T : ℝ}
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (η : Vec d × ℝ → ℝ) (p : Vec d) (z : Vec d × ℝ) :
    vecDot (matVecMul (a z) (u.grad z))
        (η z ^ 2 • u.grad z + (2 * η z * u.toFun z) • p) =
      η z ^ 2 * cauchyEnergyDensity a u z +
        (2 * η z * u.toFun z) * vecDot (matVecMul (a z) (u.grad z)) p := by
  rw [PDE.ParabCaccioppoli.vecDot_add_right', PDE.ParabCaccioppoli.vecDot_smul_right',
    PDE.ParabCaccioppoli.vecDot_smul_right', vecDot_comm (matVecMul (a z) (u.grad z))]
  rfl

/-- The cross-flux left after separating the bulk energy density. -/
noncomputable def cauchyCutoffCrossFlux {d : ℕ} (a : ParCoeffField d)
    {s T : ℝ} (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (R : ℝ) (hR : 0 < R) (z : Vec d × ℝ) : ℝ :=
  (2 * (cauchyParabolicCutoff s T R hR).toFun z * u.toFun z) *
    vecDot (matVecMul (a z) (u.grad z))
      (parSpaceGrad (cauchyParabolicCutoff s T R hR).toFun z)

/-- An integrable coordinatewise majorant for the cross-flux term. -/
noncomputable def cauchyFluxMajorant {d : ℕ} (a : ParCoeffField d)
    {s T : ℝ} (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (z : Vec d × ℝ) : ℝ :=
  |u.toFun z| * ∑ i : Fin d, |PDE.Parabolic.Energy.flux a u z i|

/-- The flux integrand supplied by the local energy identity is integrable. -/
theorem cauchy_cutoff_flux_integrable {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsParabolicWeakSolution a univ (Icc s T) u)
    (R : ℝ) (hR : 0 < R) {t : ℝ} (ht : t ∈ Icc s T) (hst : s < t) :
    IntegrableOn (fun z => vecDot (matVecMul (a z) (u.grad z))
      ((cauchyParabolicCutoff s T R hR).toFun z ^ 2 • u.grad z +
        (2 * (cauchyParabolicCutoff s T R hR).toFun z * u.toFun z) •
          parSpaceGrad (cauchyParabolicCutoff s T R hR).toFun z))
      ((univ : Set (Vec d)) ×ˢ Ioc s t) := by
  have hlocal := PDE.Parabolic.energy_identity d lam Lam univ isOpen_univ
    (Icc s T) Set.ordConnected_Icc a ha u hu (cauchyParabolicCutoff s T R hR)
  obtain ⟨_, _, hslab⟩ := hlocal
  obtain ⟨_, hflux, _⟩ := hslab s t ⟨le_rfl, hsT.le⟩ ht hst
  exact hflux

/-- The cutoff-weighted bulk energy is integrable on the time slab of the identity. -/
theorem cauchy_cutoff_bulk_integrable {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (R : ℝ) (hR : 0 < R) {t : ℝ} (ht : t ∈ Icc s T) :
    IntegrableOn (fun z => (cauchyParabolicCutoff s T R hR).toFun z ^ 2 *
      cauchyEnergyDensity a u z) ((univ : Set (Vec d)) ×ˢ Ioc s t) := by
  let Q : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s t
  have hq := cauchyEnergyDensity_integrable_Ioc ha u ht
  have hηcont : Continuous (fun z : Vec d × ℝ =>
      (cauchyParabolicCutoff s T R hR).toFun z ^ 2) :=
    (cauchyParabolicCutoff s T R hR).contDiff.continuous.pow 2
  have hηmeas : AEStronglyMeasurable
      (fun z => (cauchyParabolicCutoff s T R hR).toFun z ^ 2)
      (volume.restrict Q) := hηcont.aestronglyMeasurable
  have hηbound : ∀ᵐ z ∂(volume.restrict Q),
      ‖(cauchyParabolicCutoff s T R hR).toFun z ^ 2‖ ≤ 1 := by
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rcases cauchyParabolicCutoff_nonneg_le_one s T R hR z with ⟨hη0, hη1⟩
    simpa only [pow_two, one_mul] using (mul_self_le_mul_self hη0 hη1)
  have hmul := hq.bdd_mul hηmeas (c := 1) hηbound
  change Integrable
    (fun z => (cauchyParabolicCutoff s T R hR).toFun z ^ 2 *
      cauchyEnergyDensity a u z) (volume.restrict Q)
  simpa only [mul_comm] using hmul

/-- The cross-flux term is integrable, by subtracting the integrable bulk term from the
integrand of the local identity. -/
theorem cauchy_cutoff_cross_integrable {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsParabolicWeakSolution a univ (Icc s T) u)
    (R : ℝ) (hR : 0 < R) {t : ℝ} (ht : t ∈ Icc s T) (hst : s < t) :
    IntegrableOn (cauchyCutoffCrossFlux a u R hR)
      ((univ : Set (Vec d)) ×ˢ Ioc s t) := by
  let Q : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s t
  have hflux := cauchy_cutoff_flux_integrable hsT ha u hu R hR ht hst
  have hbulk := cauchy_cutoff_bulk_integrable ha u R hR ht
  have hsub := hflux.sub hbulk
  refine hsub.congr ?_
  filter_upwards [] with z
  change vecDot (matVecMul (a z) (u.grad z))
      ((cauchyParabolicCutoff s T R hR).toFun z ^ 2 • u.grad z +
        (2 * (cauchyParabolicCutoff s T R hR).toFun z * u.toFun z) •
          parSpaceGrad (cauchyParabolicCutoff s T R hR).toFun z) -
      ((cauchyParabolicCutoff s T R hR).toFun z ^ 2 * cauchyEnergyDensity a u z) =
    cauchyCutoffCrossFlux a u R hR z
  rw [cauchy_cutoff_flux_split u (cauchyParabolicCutoff s T R hR).toFun
    (parSpaceGrad (cauchyParabolicCutoff s T R hR).toFun z) z]
  simp [cauchyCutoffCrossFlux]

/-- The product majorant is integrable by the global space-time `L²` bounds. -/
theorem cauchyFluxMajorant_integrable_Ioc {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T)) {t : ℝ}
    (ht : t ∈ Icc s T) :
    IntegrableOn (cauchyFluxMajorant a u) ((univ : Set (Vec d)) ×ˢ Ioc s t) := by
  let Q : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s t
  have hsub : Q ⊆ (univ : Set (Vec d)) ×ˢ Icc s T := by
    intro z hz
    exact ⟨hz.1, ⟨hz.2.1.le, hz.2.2.trans ht.2⟩⟩
  have hle : volume.restrict Q ≤
      volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s T) :=
    Measure.restrict_mono hsub le_rfl
  have hu2 : MemLp u.toFun 2 (volume.restrict Q) := u.memL2.mono_measure hle
  have hterm : ∀ i : Fin d,
      Integrable (fun z => |u.toFun z| * |PDE.Parabolic.Energy.flux a u z i|)
        (volume.restrict Q) := by
    intro i
    have hfi : MemLp (fun z => PDE.Parabolic.Energy.flux a u z i) 2
        (volume.restrict Q) :=
      (PDE.Parabolic.Energy.flux_memLp ha u i).mono_measure hle
    have hp := hu2.integrable_mul hfi
    convert hp.abs using 1; ext z; simp only [Pi.mul_apply, abs_mul]
  have hsum : Integrable
      (fun z => ∑ i : Fin d,
        |u.toFun z| * |PDE.Parabolic.Energy.flux a u z i|)
      (volume.restrict Q) :=
    integrable_finsetSum _ fun i _ => hterm i
  change Integrable (cauchyFluxMajorant a u) (volume.restrict Q)
  convert hsum using 1; ext z; simp [cauchyFluxMajorant, Finset.mul_sum]

/-- The absolute integral of the cross-flux term decays at rate `1/R`. -/
theorem cauchy_cutoff_cross_integral_bound {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsParabolicWeakSolution a univ (Icc s T) u)
    (R : ℝ) (hR : 0 < R) {t : ℝ} (ht : t ∈ Icc s T) (hst : s < t) :
    |∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t, cauchyCutoffCrossFlux a u R hR z| ≤
      (64 / R) * ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t, cauchyFluxMajorant a u z := by
  let Q : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s t
  have hcross := cauchy_cutoff_cross_integrable hsT ha u hu R hR ht hst
  have hmajor := cauchyFluxMajorant_integrable_Ioc ha u ht
  have hpoint : ∀ z : Vec d × ℝ,
      ‖cauchyCutoffCrossFlux a u R hR z‖ ≤ (64 / R) * cauchyFluxMajorant a u z := by
    intro z
    let η := (cauchyParabolicCutoff s T R hR).toFun z
    let p := parSpaceGrad (cauchyParabolicCutoff s T R hR).toFun z
    let F := PDE.Parabolic.Energy.flux a u z
    have hη := cauchyParabolicCutoff_nonneg_le_one s T R hR z
    have hηabs : |η| ≤ 1 := abs_le.mpr ⟨by dsimp [η]; linarith [hη.1], by
      dsimp [η]; linarith [hη.2]⟩
    have hp : vecEuclideanNorm p ≤ 32 / R :=
      cauchyParabolicCutoff_spatialGrad_bound s T R hR z.1 z.2
    have hF : vecEuclideanNorm F ≤ ∑ i : Fin d, |F i| := vecEuclideanNorm_le_sum_abs F
    have hpn : 0 ≤ vecEuclideanNorm p := vecEuclideanNorm_nonneg p
    have hFn : 0 ≤ vecEuclideanNorm F := vecEuclideanNorm_nonneg F
    have huabs : 0 ≤ |u.toFun z| := abs_nonneg _
    have hdot := abs_vecDot_le_vecEuclideanNorm_mul F p
    change ‖(2 * η * u.toFun z) * vecDot F p‖ ≤
      (64 / R) * (|u.toFun z| * ∑ i : Fin d, |F i|)
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2:ℝ))]
    calc
      2 * |η| * |u.toFun z| * |vecDot F p| ≤
          2 * 1 * |u.toFun z| * (vecEuclideanNorm F * vecEuclideanNorm p) := by
            gcongr
      _ ≤ 2 * 1 * |u.toFun z| * ((∑ i : Fin d, |F i|) * (32 / R)) := by
            have hsum : 0 ≤ ∑ i : Fin d, |F i| := Finset.sum_nonneg fun i _ => abs_nonneg _
            have hRnonneg : 0 ≤ (32 : ℝ) / R := by positivity
            gcongr
      _ = (64 / R) * (|u.toFun z| * ∑ i : Fin d, |F i|) := by ring
  have hmono : ∫ z in Q, ‖cauchyCutoffCrossFlux a u R hR z‖ ≤
      ∫ z in Q, (64 / R) * cauchyFluxMajorant a u z := by
    apply integral_mono hcross.norm (hmajor.const_mul (64 / R))
    intro z
    exact hpoint z
  have hnorm : |∫ z in Q, cauchyCutoffCrossFlux a u R hR z| ≤
      ∫ z in Q, ‖cauchyCutoffCrossFlux a u R hR z‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (μ := volume.restrict Q)
        (fun z : Vec d × ℝ => cauchyCutoffCrossFlux a u R hR z))
  calc
    |∫ z in Q, cauchyCutoffCrossFlux a u R hR z| ≤
        ∫ z in Q, ‖cauchyCutoffCrossFlux a u R hR z‖ := hnorm
    _ ≤ ∫ z in Q, (64 / R) * cauchyFluxMajorant a u z := hmono
    _ = (64 / R) * ∫ z in Q, cauchyFluxMajorant a u z := by
      rw [integral_const_mul]

/-- The integral form of the flux split. -/
theorem cauchy_cutoff_flux_integral_split {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsParabolicWeakSolution a univ (Icc s T) u)
    (R : ℝ) (hR : 0 < R) {t : ℝ} (ht : t ∈ Icc s T) (hst : s < t) :
    (∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
      vecDot (matVecMul (a z) (u.grad z))
        ((cauchyParabolicCutoff s T R hR).toFun z ^ 2 • u.grad z +
          (2 * (cauchyParabolicCutoff s T R hR).toFun z * u.toFun z) •
            parSpaceGrad (cauchyParabolicCutoff s T R hR).toFun z)) =
    (∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
      (cauchyParabolicCutoff s T R hR).toFun z ^ 2 * cauchyEnergyDensity a u z) +
    ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t, cauchyCutoffCrossFlux a u R hR z := by
  have hflux := cauchy_cutoff_flux_integrable hsT ha u hu R hR ht hst
  have hbulk := cauchy_cutoff_bulk_integrable ha u R hR ht
  have hcross := cauchy_cutoff_cross_integrable hsT ha u hu R hR ht hst
  rw [← integral_add hbulk hcross]
  apply integral_congr_ae
  filter_upwards [] with z
  exact cauchy_cutoff_flux_split u (cauchyParabolicCutoff s T R hR).toFun
    (parSpaceGrad (cauchyParabolicCutoff s T R hR).toFun z) z

/-- Every cutoff slice energy is bounded by the initial energy plus the controlled cross flux. -/
theorem cauchy_cutoff_slice_energy_bound {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u)
    (R : ℝ) (hR : 0 < R) {t : ℝ} (ht : t ∈ Icc s T) (hst : s < t) :
    (∫ x in (univ : Set (Vec d)),
      (cauchyParabolicCutoff s T R hR).toFun (x, t) ^ 2 * u.toFun (x, t) ^ 2) ≤
      (∫ x : Vec d, f x ^ 2) + (128 / R) *
        ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t, cauchyFluxMajorant a u z := by
  have hweak := hu.1
  have hid := cauchy_cutoff_energy_identity hsT ha u hweak R hR ht hst
  have hsplit := cauchy_cutoff_flux_integral_split hsT ha u hweak R hR ht hst
  have hcross := cauchy_cutoff_cross_integral_bound hsT ha u hweak R hR ht hst
  have hbulkNonneg : 0 ≤ ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
      (cauchyParabolicCutoff s T R hR).toFun z ^ 2 * cauchyEnergyDensity a u z := by
    apply integral_nonneg_of_ae
    have hsub : (univ : Set (Vec d)) ×ˢ Ioc s t ⊆
        (univ : Set (Vec d)) ×ˢ Icc s T :=
      prod_mono subset_rfl fun τ hτ => ⟨hτ.1.le, hτ.2.trans ht.2⟩
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub
      (cauchyEnergyDensity_nonneg_ae ha u)] with z hz
    exact mul_nonneg (sq_nonneg _) hz
  have hstart : (∫ x in (univ : Set (Vec d)),
      (cauchyParabolicCutoff s T R hR).toFun (x, s) ^ 2 * u.toFun (x, s) ^ 2) ≤
      ∫ x : Vec d, f x ^ 2 := by
    have hinit : ∀ᵐ x : Vec d, u.toFun (x, s) = f x := hu.2
    have hleft := (PDE.Parabolic.energy_identity d lam Lam univ isOpen_univ
      (Icc s T) Set.ordConnected_Icc a ha u hweak (cauchyParabolicCutoff s T R hR)).1 s
      ⟨le_rfl, hsT.le⟩
    have hsqInt : Integrable (fun x : Vec d => f x ^ 2) volume := hf.integrable_sq
    have hηInt : Integrable (fun x : Vec d =>
        (cauchyParabolicCutoff s T R hR).toFun (x, s) ^ 2 * u.toFun (x, s) ^ 2)
        (volume.restrict univ) := hleft
    have hηeq : (∫ x in (univ : Set (Vec d)),
        (cauchyParabolicCutoff s T R hR).toFun (x, s) ^ 2 * u.toFun (x, s) ^ 2) =
        ∫ x : Vec d, (cauchyParabolicCutoff s T R hR).toFun (x, s) ^ 2 * f x ^ 2 := by
      rw [setIntegral_univ]
      apply integral_congr_ae
      filter_upwards [hinit] with x hx
      rw [hx]
    have hηfInt : Integrable (fun x : Vec d =>
        (cauchyParabolicCutoff s T R hR).toFun (x, s) ^ 2 * f x ^ 2) volume := by
      have hηmeas : AEStronglyMeasurable
          (fun x : Vec d => (cauchyParabolicCutoff s T R hR).toFun (x, s) ^ 2) volume :=
        ((cauchyParabolicCutoff s T R hR).contDiff.continuous.comp
          (continuous_id.prodMk continuous_const)).pow 2 |>.aestronglyMeasurable
      have hηbound : ∀ᵐ x : Vec d ∂volume,
          ‖(cauchyParabolicCutoff s T R hR).toFun (x, s) ^ 2‖ ≤ 1 := by
        have hpoint : ∀ x : Vec d,
            ‖(cauchyParabolicCutoff s T R hR).toFun (x, s) ^ 2‖ ≤ 1 := by
          intro x
          have hη := cauchyParabolicCutoff_nonneg_le_one s T R hR (x, s)
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          have := mul_self_le_mul_self hη.1 hη.2
          simpa only [pow_two, one_mul] using this
        exact ae_of_all volume hpoint
      simpa only [mul_comm] using hsqInt.bdd_mul hηmeas (c := 1) hηbound
    have hηmono : ∫ x : Vec d,
        (cauchyParabolicCutoff s T R hR).toFun (x, s) ^ 2 * f x ^ 2 ≤
        ∫ x : Vec d, f x ^ 2 := by
      apply integral_mono hηfInt hsqInt
      intro x
      have hη := cauchyParabolicCutoff_nonneg_le_one s T R hR (x, s)
      have hsq : (cauchyParabolicCutoff s T R hR).toFun (x, s) ^ 2 ≤ 1 := by
        have := mul_self_le_mul_self hη.1 hη.2
        simpa only [pow_two, one_mul] using this
      exact mul_le_of_le_one_left (sq_nonneg _) hsq
    rw [hηeq]
    exact hηmono
  rw [hsplit] at hid
  have henergy :
      ((1 / 2 : ℝ) * ∫ x in (univ : Set (Vec d)),
        (cauchyParabolicCutoff s T R hR).toFun (x, t) ^ 2 * u.toFun (x, t) ^ 2) -
      (1 / 2 : ℝ) * ∫ x in (univ : Set (Vec d)),
        (cauchyParabolicCutoff s T R hR).toFun (x, s) ^ 2 * u.toFun (x, s) ^ 2 =
      -((∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
          (cauchyParabolicCutoff s T R hR).toFun z ^ 2 * cauchyEnergyDensity a u z) +
        ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t, cauchyCutoffCrossFlux a u R hR z) := by
    simpa only [hsplit] using hid
  have hfinal :
      (∫ x in (univ : Set (Vec d)),
        (cauchyParabolicCutoff s T R hR).toFun (x, t) ^ 2 * u.toFun (x, t) ^ 2) ≤
        (∫ x in (univ : Set (Vec d)),
          (cauchyParabolicCutoff s T R hR).toFun (x, s) ^ 2 * u.toFun (x, s) ^ 2) +
      2 * |∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
          cauchyCutoffCrossFlux a u R hR z| := by
    let C := ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
      cauchyCutoffCrossFlux a u R hR z
    have hC : -C ≤ |C| := by exact neg_le_abs C
    linarith [henergy, hbulkNonneg, hC]
  calc
    (∫ x in (univ : Set (Vec d)),
          (cauchyParabolicCutoff s T R hR).toFun (x, t) ^ 2 * u.toFun (x, t) ^ 2) ≤
        (∫ x in (univ : Set (Vec d)),
          (cauchyParabolicCutoff s T R hR).toFun (x, s) ^ 2 * u.toFun (x, s) ^ 2) +
        2 * |∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
          cauchyCutoffCrossFlux a u R hR z| := hfinal
    _ ≤ (∫ x : Vec d, f x ^ 2) + (128 / R) *
        ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t, cauchyFluxMajorant a u z := by
      have hbound :
          (∫ x in (univ : Set (Vec d)),
            (cauchyParabolicCutoff s T R hR).toFun (x, s) ^ 2 * u.toFun (x, s) ^ 2) +
          2 * |∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
            cauchyCutoffCrossFlux a u R hR z| ≤
          (∫ x : Vec d, f x ^ 2) + 2 * ((64 / R) *
            ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t, cauchyFluxMajorant a u z) :=
        add_le_add hstart (mul_le_mul_of_nonneg_left hcross (by norm_num))
      calc
        _ ≤ (∫ x : Vec d, f x ^ 2) + 2 * ((64 / R) *
            ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t, cauchyFluxMajorant a u z) := hbound
        _ = (∫ x : Vec d, f x ^ 2) + (128 / R) *
            ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t, cauchyFluxMajorant a u z := by ring

/-- Every time slice of a Cauchy energy solution is globally square integrable. -/
theorem cauchy_slice_square_integrable {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) {t : ℝ} (ht : t ∈ Icc s T) :
    Integrable (fun x : Vec d => u.toFun (x, t) ^ 2) volume := by
  rcases lt_or_eq_of_le ht.1 with hst | hst
  · let K : ℕ → Set (Vec d) := fun n => euclideanClosedBall 0 ((n : ℝ) + 1)
    have hcover : AECover volume atTop K := by
      constructor
      · filter_upwards [] with x
        obtain ⟨N, hN⟩ := exists_nat_gt (vecEuclideanNorm x)
        filter_upwards [eventually_ge_atTop N] with n hn
        have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
        have hnorm : vecEuclideanNorm (x - (0 : Vec d)) ≤ (n : ℝ) + 1 := by
          rw [sub_zero]
          exact le_trans (le_of_lt hN) (by linarith)
        exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2 hnorm
      · intro n
        exact measurableSet_euclideanClosedBall 0 ((n : ℝ) + 1)
    let Qmax : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s T
    have hMmax : IntegrableOn (cauchyFluxMajorant a u) Qmax := by
      exact cauchyFluxMajorant_integrable_Ioc ha u ⟨hsT.le, le_rfl⟩
    have hMmaxNonneg : 0 ≤ ∫ z in Qmax, cauchyFluxMajorant a u z := by
      apply integral_nonneg_of_ae
      refine ae_of_all _ fun z => ?_
      apply mul_nonneg (abs_nonneg _)
      exact Finset.sum_nonneg fun i _ => abs_nonneg _
    have hlocalSq : ∀ n, IntegrableOn (fun x : Vec d => u.toFun (x, t) ^ 2) (K n) := by
      intro n
      have hloc := u.sliceL2loc t ht (K n)
        (isCompact_euclideanClosedBall 0 (by positivity)) (Set.subset_univ _)
      exact hloc.integrable_sq
    have hbound : ∀ n, ∫ x in K n, u.toFun (x, t) ^ 2 ≤
        (∫ x : Vec d, f x ^ 2) + 128 * ∫ z in Qmax, cauchyFluxMajorant a u z := by
      intro n
      let R : ℝ := (n : ℝ) + 2
      have hR : 0 < R := by dsimp [R]; positivity
      have hRge : 1 ≤ R := by
        dsimp [R]
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
        linarith
      have hKinner : ∀ x ∈ K n, x ∈ euclideanBall 0 R := by
        intro x hx
        have hnorm := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).1 hx
        apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).2
        rw [sub_zero] at hnorm ⊢
        dsimp [R]
        exact lt_of_le_of_lt hnorm (by linarith)
      have hEq : (∫ x in K n, u.toFun (x, t) ^ 2) =
          ∫ x in K n, (cauchyParabolicCutoff s T R hR).toFun (x, t) ^ 2 *
            u.toFun (x, t) ^ 2 := by
        refine setIntegral_congr_fun (hcover.measurableSet n) ?_
        intro x hx
        change u.toFun (x, t) ^ 2 =
          (cauchyParabolicCutoff s T R hR).toFun (x, t) ^ 2 * u.toFun (x, t) ^ 2
        rw [cauchyParabolicCutoff_eq_one s T R hR (hKinner x hx)]
        ring
      have hηglobal : Integrable (fun x : Vec d =>
          (cauchyParabolicCutoff s T R hR).toFun (x, t) ^ 2 * u.toFun (x, t) ^ 2)
          (volume.restrict univ) :=
        (PDE.Parabolic.energy_identity d lam Lam univ isOpen_univ (Icc s T)
          Set.ordConnected_Icc a ha u hu.1 (cauchyParabolicCutoff s T R hR)).1 t ht
      have hηnonneg : 0 ≤ᵐ[volume.restrict univ] fun x : Vec d =>
          (cauchyParabolicCutoff s T R hR).toFun (x, t) ^ 2 * u.toFun (x, t) ^ 2 :=
        ae_of_all _ fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)
      have hKsub : K n ≤ᵐ[volume] univ := ae_of_all _ fun x hx => mem_univ x
      have hset := setIntegral_mono_set hηglobal hηnonneg hKsub
      have hcut := cauchy_cutoff_slice_energy_bound hsT ha f hf u hu R hR ht hst
      have hQsub : (univ : Set (Vec d)) ×ˢ Ioc s t ⊆ Qmax :=
        prod_mono subset_rfl fun τ hτ => ⟨hτ.1, hτ.2.trans ht.2⟩
      have hQle : volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s t) ≤
          volume.restrict Qmax := Measure.restrict_mono hQsub le_rfl
      have hQmajor : ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
          cauchyFluxMajorant a u z ≤ ∫ z in Qmax, cauchyFluxMajorant a u z := by
        apply integral_mono_measure hQle
        · exact ae_of_all _ fun z => mul_nonneg (abs_nonneg _) <|
            Finset.sum_nonneg fun i _ => abs_nonneg _
        · exact hMmax
      have hcoef : 128 / R ≤ 128 := by
        rw [div_le_iff₀ hR]
        nlinarith
      have htail : (128 / R) * ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
          cauchyFluxMajorant a u z ≤ 128 * ∫ z in Qmax, cauchyFluxMajorant a u z := by
        calc
          _ ≤ 128 * ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
              cauchyFluxMajorant a u z := mul_le_mul_of_nonneg_right hcoef (by
                apply integral_nonneg_of_ae
                exact ae_of_all _ fun z => mul_nonneg (abs_nonneg _) <|
                  Finset.sum_nonneg fun i _ => abs_nonneg _)
          _ ≤ _ := mul_le_mul_of_nonneg_left hQmajor (by norm_num)
      calc
        _ = ∫ x in K n, (cauchyParabolicCutoff s T R hR).toFun (x, t) ^ 2 *
              u.toFun (x, t) ^ 2 := hEq
        _ ≤ ∫ x in (univ : Set (Vec d)),
              (cauchyParabolicCutoff s T R hR).toFun (x, t) ^ 2 * u.toFun (x, t) ^ 2 := hset
        _ ≤ (∫ x : Vec d, f x ^ 2) +
              (128 / R) * ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
                cauchyFluxMajorant a u z := hcut
        _ ≤ _ := by
          simpa only [add_comm] using add_le_add_left htail (∫ x : Vec d, f x ^ 2)
    have hfK : ∀ n, IntegrableOn (fun x : Vec d => u.toFun (x, t) ^ 2) (K n) := hlocalSq
    have hbound' : ∀ᶠ n in atTop,
        (∫ x in K n, u.toFun (x, t) ^ 2) ≤
          (∫ x : Vec d, f x ^ 2) + 128 * ∫ z in Qmax, cauchyFluxMajorant a u z := by
      filter_upwards [] with n
      exact hbound n
    have hnn : 0 ≤ᵐ[volume] fun x : Vec d => u.toFun (x, t) ^ 2 :=
      ae_of_all _ fun x => sq_nonneg _
    exact hcover.integrable_of_integral_bounded_of_nonneg_ae
      ((∫ x : Vec d, f x ^ 2) + 128 * ∫ z in Qmax, cauchyFluxMajorant a u z)
      hfK hnn hbound'
  · subst t
    have hinit := hu.2
    have hfSq : Integrable (fun x : Vec d => f x ^ 2) volume := hf.integrable_sq
    exact hfSq.congr (hinit.mono fun x hx => by
      change f x ^ 2 = u.toFun (x, s) ^ 2
      rw [hx])

/-- Dominated convergence for the slice energies of the exhaustion cutoffs. -/
theorem cauchy_cutoff_slice_integral_tendsto {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) {t : ℝ} (ht : t ∈ Icc s T) :
    Tendsto (fun n : ℕ => ∫ x : Vec d,
      (cauchyExhaustionCutoff s T n).toFun (x, t) ^ 2 * u.toFun (x, t) ^ 2)
      atTop (𝓝 <| ∫ x : Vec d, u.toFun (x, t) ^ 2) := by
  have hslice := cauchy_slice_square_integrable hsT ha f hf u hu ht
  let F : ℕ → Vec d → ℝ := fun n x =>
    (cauchyExhaustionCutoff s T n).toFun (x, t) ^ 2 * u.toFun (x, t) ^ 2
  have hmeas : ∀ n, AEStronglyMeasurable (F n) volume := by
    intro n
    have hη : Continuous (fun x : Vec d =>
        (cauchyExhaustionCutoff s T n).toFun (x, t) ^ 2) :=
      (cauchyExhaustionCutoff s T n).contDiff.continuous.comp
        (continuous_id.prodMk continuous_const) |>.pow 2
    exact hη.aestronglyMeasurable.mul hslice.aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ x ∂volume, ‖F n x‖ ≤ u.toFun (x, t) ^ 2 := by
    intro n
    filter_upwards [] with x
    dsimp [F]
    have hη := cauchyParabolicCutoff_nonneg_le_one s T ((n : ℝ) + 2) (by positivity) (x, t)
    have hηsq : (cauchyExhaustionCutoff s T n).toFun (x, t) ^ 2 ≤ 1 := by
      dsimp [cauchyExhaustionCutoff]
      have := mul_self_le_mul_self hη.1 hη.2
      simpa only [pow_two, one_mul] using this
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact mul_le_of_le_one_left (sq_nonneg _) hηsq
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun n => F n x) atTop
      (𝓝 (u.toFun (x, t) ^ 2)) := by
    filter_upwards [] with x
    apply tendsto_const_nhds.congr'
    filter_upwards [cauchyExhaustionCutoff_eventually_one s T x t] with n hn
    simp [F, hn]
  exact tendsto_integral_of_dominated_convergence
    (fun x : Vec d => u.toFun (x, t) ^ 2) hmeas hslice hbound hlim

/-- Dominated convergence for the cutoff-weighted space-time energy density. -/
theorem cauchy_cutoff_bulk_integral_tendsto {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    {t : ℝ} (ht : t ∈ Icc s T) :
    Tendsto (fun n : ℕ => ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
      (cauchyExhaustionCutoff s T n).toFun z ^ 2 * cauchyEnergyDensity a u z)
      atTop (𝓝 <| ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t, cauchyEnergyDensity a u z) := by
  let Q : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s t
  let F : ℕ → Vec d × ℝ → ℝ := fun n z =>
    (cauchyExhaustionCutoff s T n).toFun z ^ 2 * cauchyEnergyDensity a u z
  have hq := cauchyEnergyDensity_integrable_Ioc ha u ht
  have hqnn := cauchyEnergyDensity_nonneg_ae ha u
  have hsub : Q ⊆ (univ : Set (Vec d)) ×ˢ Icc s T := by
    intro z hz
    exact ⟨hz.1, ⟨hz.2.1.le, hz.2.2.trans ht.2⟩⟩
  have hqnnQ : ∀ᵐ z ∂(volume.restrict Q), 0 ≤ cauchyEnergyDensity a u z :=
    ae_restrict_of_ae_restrict_of_subset hsub hqnn
  have hmeas : ∀ n, AEStronglyMeasurable (F n) (volume.restrict Q) := by
    intro n
    have hη : Continuous (fun z : Vec d × ℝ =>
        (cauchyExhaustionCutoff s T n).toFun z ^ 2) :=
      (cauchyExhaustionCutoff s T n).contDiff.continuous.pow 2
    exact hη.aestronglyMeasurable.mul hq.aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ z ∂(volume.restrict Q), ‖F n z‖ ≤ cauchyEnergyDensity a u z := by
    intro n
    filter_upwards [hqnnQ] with z hqz
    dsimp [F]
    have hη := cauchyParabolicCutoff_nonneg_le_one s T ((n : ℝ) + 2) (by positivity) z
    have hηsq : (cauchyExhaustionCutoff s T n).toFun z ^ 2 ≤ 1 := by
      dsimp [cauchyExhaustionCutoff]
      have := mul_self_le_mul_self hη.1 hη.2
      simpa only [pow_two, one_mul] using this
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hqz)]
    exact mul_le_of_le_one_left hqz hηsq
  have hlim : ∀ᵐ z ∂(volume.restrict Q), Tendsto (fun n => F n z) atTop
      (𝓝 (cauchyEnergyDensity a u z)) := by
    filter_upwards [] with z
    apply tendsto_const_nhds.congr'
    filter_upwards [cauchyExhaustionCutoff_eventually_one s T z.1 z.2] with n hn
    simp [F, hn]
  have hq' : Integrable (cauchyEnergyDensity a u) (volume.restrict Q) := hq
  simpa [F, Q] using
    (tendsto_integral_of_dominated_convergence
      (fun z : Vec d × ℝ => cauchyEnergyDensity a u z) hmeas hq' hbound hlim)

end PDE.Parabolic.Cauchy.Energy
