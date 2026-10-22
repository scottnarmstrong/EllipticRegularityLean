module

public import EllipticRegularity.Parabolic.Cauchy.Energy.Global
public import EllipticRegularity.Parabolic.Cauchy.Energy.Density
public import EllipticRegularity.Parabolic.Cauchy.Energy.Exhaustion
public import EllipticRegularity.Parabolic.Cauchy.OnDiag.NashDecay
public import EllipticRegularity.Parabolic.Cauchy.Weights.TimeMoment
public import EllipticRegularity.Parabolic.Cauchy.Weights.TimeShift
public import EllipticRegularity.Parabolic.Cauchy.L1.Contraction
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The polynomially weighted space-time square integral

The energy identity controls the early time slab, while Nash smoothing controls
the later slab.  Splitting at the positive shift gives a dimensional bound
for the time moment used by the Gaussian weighted-energy estimate.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.OnDiag

open MeasureTheory Set

/-- Uniform time-moment estimate from whole-space energy contraction and the
unit-mass Nash smoothing bound.  The shift assumptions make the initial-data
contribution at most one time-length. -/
theorem cauchy_unit_mass_time_moment {d : ℕ} (hd : 0 < d)
    {Lam s H σ : ℝ}
    (hσ : 0 < σ) (hσH : σ ≤ H / 2)
    (a : ParCoeffField d)
    (ha : IsParabolicCoeff 1 Lam a univ (Icc s (s + H)))
    (f : Vec d → ℝ) (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (hσData : σ ^ (((d : ℝ) + 2) / 2) * (∫ x : Vec d, f x ^ 2) ≤ H)
    (hfnonneg : 0 ≤ᵐ[volume] f) (hfmass : ∫ x, f x = 1)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s (s + H)))
    (hu : IsCauchySolution a s (s + H) f u) :
    IntegrableOn
        (fun z : Vec d × ℝ =>
          (PDE.Parabolic.Cauchy.Weights.nashPositiveTimeShift σ (z.2 - s)) ^
              ((d : ℝ) / 2) * u.toFun z ^ 2)
        ((univ : Set (Vec d)) ×ˢ Ioc s (s + H)) ∧
      ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s (s + H),
          (PDE.Parabolic.Cauchy.Weights.nashPositiveTimeShift σ (z.2 - s)) ^
              ((d : ℝ) / 2) * u.toFun z ^ 2 ≤
        2 ^ ((d : ℝ) / 2) *
          (1 + cauchyUnitMassNashConstant d hd) * H := by
  let p : ℝ := (d : ℝ) / 2
  let I : ℝ := ∫ x : Vec d, f x ^ 2
  let Q : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s (s + H)
  have hsH : s < s + H := by linarith [hσ, hσH]
  have hI : 0 ≤ I := by
    dsimp [I]
    exact integral_nonneg_of_ae (ae_of_all _ fun x => sq_nonneg (f x))
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hκ : ((d : ℝ) + 2) / 2 = p + 1 := by dsimp [p]; ring
  have hσlt : σ < H := by linarith
  have hU2 : Integrable (fun z : Vec d × ℝ => u.toFun z ^ 2)
      (volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s (s + H))) :=
    u.memL2.integrable_sq
  have hQsub : Q ⊆ (univ : Set (Vec d)) ×ˢ Icc s (s + H) := by
    intro z hz
    exact ⟨Set.mem_univ _, ⟨hz.2.1.le, hz.2.2⟩⟩
  have hU2Q : Integrable (fun z : Vec d × ℝ => u.toFun z ^ 2)
      (volume.restrict Q) :=
    hU2.mono_measure (Measure.restrict_mono hQsub le_rfl)
  let W : Vec d × ℝ → ℝ := fun z =>
    (PDE.Parabolic.Cauchy.Weights.nashPositiveTimeShift σ (z.2 - s)) ^ p
  have hshiftCont : Continuous (fun z : Vec d × ℝ =>
      PDE.Parabolic.Cauchy.Weights.nashPositiveTimeShift σ (z.2 - s)) :=
    (PDE.Parabolic.Cauchy.Weights.nashPositiveTimeShift_contDiff_one.continuous.comp
      (continuous_snd.sub continuous_const))
  have hWcont : Continuous W := by
    dsimp [W]
    exact Real.continuous_rpow_const hp |>.comp hshiftCont
  have hWbound : ∀ᵐ z ∂(volume.restrict Q), ‖W z‖ ≤ (H + σ) ^ p := by
    apply (ae_restrict_iff' (MeasurableSet.prod MeasurableSet.univ measurableSet_Ioc)).2
    filter_upwards [] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by
      have h := PDE.Parabolic.Cauchy.Weights.nashPositiveTimeShift_lower
        (σ := σ) (t := z.2 - s) hσ
      linarith) p)]
    have hrge : 0 ≤ z.2 - s := by linarith [hz.2.1]
    have hshift := PDE.Parabolic.Cauchy.Weights.nashPositiveTimeShift_eq_add
      hσ hrge
    have hshiftle :
        PDE.Parabolic.Cauchy.Weights.nashPositiveTimeShift σ (z.2 - s) ≤ H + σ := by
      rw [hshift]
      linarith [hz.2.2]
    exact Real.rpow_le_rpow (by
      have h := PDE.Parabolic.Cauchy.Weights.nashPositiveTimeShift_lower
        (σ := σ) (t := z.2 - s) hσ
      linarith) hshiftle hp
  have hMomentInt : IntegrableOn
      (fun z : Vec d × ℝ => W z * u.toFun z ^ 2) Q := by
    change Integrable (fun z : Vec d × ℝ => W z * u.toFun z ^ 2)
      (volume.restrict Q)
    have h := hU2Q.mul_bdd (c := (H + σ) ^ p)
      hWcont.aestronglyMeasurable hWbound
    exact h.congr (ae_of_all _ fun z => by simp [mul_comm])
  have hSliceInt : ∀ t ∈ Icc s (s + H),
      Integrable (fun x : Vec d => u.toFun (x, t) ^ 2) volume := by
    intro t ht
    exact PDE.Parabolic.Cauchy.Energy.cauchy_slice_square_integrable
      hsH ha f hf2 u hu ht
  have hDensityNonneg := PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity_nonneg_ae ha u
  have hEarly : ∀ᵐ t ∂(volume.restrict (Ioc s (s + σ))),
      ∫ x : Vec d, u.toFun (x, t) ^ 2 ≤ I := by
    apply (ae_restrict_iff' measurableSet_Ioc).2
    filter_upwards [] with t ht
    have htIcc : t ∈ Icc s (s + H) := by
      refine ⟨le_of_lt ht.1, ?_⟩
      linarith [ht.2, hσH]
    let Qt : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s t
    have hQtSub : Qt ⊆ (univ : Set (Vec d)) ×ˢ Icc s (s + H) := by
      intro z hz
      exact ⟨Set.mem_univ _, ⟨hz.2.1.le, le_trans hz.2.2 htIcc.2⟩⟩
    have hDensityNonnegQt : ∀ᵐ z ∂(volume.restrict Qt),
        0 ≤ PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z :=
      hDensityNonneg.filter_mono
        (ae_mono (Measure.restrict_mono hQtSub le_rfl))
    have hDissNonneg : 0 ≤ ∫ z in Qt,
        PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z := by
      apply integral_nonneg_of_ae
      exact hDensityNonnegQt
    have hEnergy := PDE.Parabolic.Cauchy.Energy.cauchy_energy_identity_real
      hsH ha f hf2 u hu htIcc
    dsimp [I]
    change (∫ x : Vec d, u.toFun (x, t) ^ 2) +
      2 * ∫ z in Qt, PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z =
        ∫ x : Vec d, f x ^ 2 at hEnergy
    linarith
  have hLate : ∀ᵐ t ∂(volume.restrict (Ioc (s + σ) (s + H))),
      ∫ x : Vec d, u.toFun (x, t) ^ 2 ≤
        cauchyUnitMassNashConstant d hd * (t - s) ^ (-(d : ℝ) / 2) := by
    apply (ae_restrict_iff' measurableSet_Ioc).2
    filter_upwards [] with t ht
    have htIcc : t ∈ Icc s (s + H) := by
      exact ⟨le_trans (by linarith : s ≤ s + σ) (le_of_lt ht.1), ht.2⟩
    exact cauchy_unit_mass_nash_decay hd hsH a ha f hf1 hf2 hfnonneg hfmass u hu
      htIcc (by linarith [ht.1])
  have hmoment := PDE.Parabolic.Cauchy.Weights.nashTimeWeightedMoment_bound
    (d := d) (H := H) (σ := σ) (B₁ := 1) (B₂ := I)
    (C := cauchyUnitMassNashConstant d hd) s hd hσ hσlt
    (by norm_num) hI (cauchyUnitMassNashConstant_pos d hd).le
    hMomentInt hSliceInt hEarly (by
      filter_upwards [hLate] with t ht
      simpa using ht)
  refine ⟨hMomentInt, ?_⟩
  have hEarlyTerm : (2 * σ) ^ p * I * σ ≤ 2 ^ p * H := by
    have hpower : (2 * σ) ^ p = 2 ^ p * σ ^ p := by
      rw [Real.mul_rpow (by norm_num) hσ.le]
    have hcombine : σ ^ p * σ = σ ^ (p + 1) := by
      calc
        σ ^ p * σ = σ ^ p * σ ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = σ ^ (p + 1) := by rw [← Real.rpow_add hσ]
    rw [hpower]
    calc
      2 ^ p * σ ^ p * I * σ = 2 ^ p * (σ ^ p * σ) * I := by ring
      _ = 2 ^ p * (σ ^ (p + 1) * I) := by rw [hcombine]; ring
      _ ≤ 2 ^ p * H := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) p)
        simpa [hκ, I] using hσData
  have hLateTerm : 2 ^ p * cauchyUnitMassNashConstant d hd * 1 * (H - σ) ≤
      2 ^ p * cauchyUnitMassNashConstant d hd * H := by
    have hcoeff : 0 ≤ 2 ^ p * cauchyUnitMassNashConstant d hd :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) p)
        (cauchyUnitMassNashConstant_pos d hd).le
    have hlen : H - σ ≤ H := by linarith
    calc
      2 ^ p * cauchyUnitMassNashConstant d hd * 1 * (H - σ) =
          (2 ^ p * cauchyUnitMassNashConstant d hd) * (H - σ) := by ring
      _ ≤ (2 ^ p * cauchyUnitMassNashConstant d hd) * H :=
        mul_le_mul_of_nonneg_left hlen hcoeff
  calc
    ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s (s + H), W z * u.toFun z ^ 2 ≤
        (2 * σ) ^ p * I * σ + 2 ^ p * cauchyUnitMassNashConstant d hd * 1 * (H - σ) := by
      simpa [W, p, I] using hmoment.2
    _ ≤ 2 ^ p * H + 2 ^ p * cauchyUnitMassNashConstant d hd * H :=
      add_le_add hEarlyTerm hLateTerm
    _ = 2 ^ p * (1 + cauchyUnitMassNashConstant d hd) * H := by ring

end PDE.Parabolic.Cauchy.OnDiag
