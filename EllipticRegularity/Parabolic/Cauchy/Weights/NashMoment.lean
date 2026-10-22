module

public import EllipticRegularity.Parabolic.Cauchy.Weights.DiagonalBound
public import EllipticRegularity.Parabolic.Cauchy.Weights.TimeMoment
public import EllipticRegularity.Parabolic.Cauchy.Weights.TruncatedEnergyLimit
public import EllipticRegularity.Parabolic.Cauchy.Energy.Global
public import EllipticRegularity.Parabolic.Cauchy.Energy.Exhaustion
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Time moment bound for the truncated Nash weight

The time weighted square norm is controlled by early `L²` contraction and
late Nash smoothing. This supplies the moment input to the truncated weighted
energy inequality.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Weights

open MeasureTheory Set

variable {d : ℕ}

/-- Whole-space `L²` contraction at every time slice. -/
theorem cauchy_l2_slice_contraction {Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (_hLam : 1 ≤ Lam)
    (ha : IsParabolicCoeff 1 Lam a univ (Icc s T))
    {f : Vec d → ℝ} (hf : MemLp f 2 volume)
    {u : ParH1Function (univ : Set (Vec d)) (Icc s T)}
    (hu : IsCauchySolution a s T f u) {t : ℝ} (ht : t ∈ Icc s T) :
    ∫ x : Vec d, u.toFun (x, t) ^ 2 ≤ ∫ x : Vec d, f x ^ 2 := by
  have hid := PDE.Parabolic.Cauchy.Energy.cauchy_energy_identity_real
    hsT ha f hf u hu ht
  have hQsub : (univ : Set (Vec d)) ×ˢ Ioc s t ⊆
      (univ : Set (Vec d)) ×ˢ Icc s T := by
    exact prod_mono subset_rfl fun τ hτ => ⟨hτ.1.le, hτ.2.trans ht.2⟩
  have hQmeasure : volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s t) ≤
      volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s T) :=
    Measure.restrict_mono hQsub le_rfl
  have hqnonneg : 0 ≤ᵐ[volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s t)]
      fun z => PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z :=
    (PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity_nonneg_ae ha u).filter_mono
      (ae_mono hQmeasure)
  have hqnonnegInt : 0 ≤ ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
      PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z :=
    integral_nonneg_of_ae hqnonneg
  linarith

/-- The polynomially weighted space-time square norm is controlled by the
two phase `L²` estimates: contraction before `σ`, and dimension-only Nash
smoothing afterwards. -/
theorem cauchy_nash_timeMoment_bound {H Lam σ B : ℝ} (s : ℝ)
    (hd : 0 < d) (_hH : 0 < H) (hσ : 0 < σ) (hσH : σ < H)
    (hLam : 1 ≤ Lam) (hB : 0 < B)
    {a : ParCoeffField d}
    (ha : IsParabolicCoeff 1 Lam a univ (Icc s (s + H)))
    {f : Vec d → ℝ} (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (hBf : ∫ x : Vec d, |f x| ≤ B)
    {u : ParH1Function (univ : Set (Vec d)) (Icc s (s + H))}
    (hu : IsCauchySolution a s (s + H) f u) :
    IntegrableOn
        (fun z : Vec d × ℝ =>
          (nashPositiveTimeShift σ (z.2 - s)) ^ ((d : ℝ) / 2) * u.toFun z ^ 2)
        ((univ : Set (Vec d)) ×ˢ Ioc s (s + H)) ∧
    ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s (s + H),
      (nashPositiveTimeShift σ (z.2 - s)) ^ ((d : ℝ) / 2) * u.toFun z ^ 2 ≤
      (2 * σ) ^ ((d : ℝ) / 2) * (∫ x : Vec d, f x ^ 2) * σ +
        2 ^ ((d : ℝ) / 2) * nashDiagonalSmoothingConstant d * B ^ 2 * (H - σ) := by
  have hB₂ : 0 ≤ ∫ x : Vec d, f x ^ 2 :=
    integral_nonneg_of_ae (ae_of_all _ fun x => sq_nonneg (f x))
  have hC := nashDiagonalSmoothingConstant_pos hd
  have hMomentInt : IntegrableOn
      (fun z : Vec d × ℝ =>
        (nashPositiveTimeShift σ (z.2 - s)) ^ ((d : ℝ) / 2) * u.toFun z ^ 2)
      ((univ : Set (Vec d)) ×ˢ Ioc s (s + H)) := by
    let Q : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s (s + H)
    let slab : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Icc s (s + H)
    let p : ℝ := (d : ℝ) / 2
    let w : Vec d × ℝ → ℝ := fun z =>
      (nashPositiveTimeShift σ (z.2 - s)) ^ p
    have hQsub : Q ⊆ slab := by
      intro z hz
      exact ⟨hz.1, ⟨hz.2.1.le, hz.2.2⟩⟩
    have hQmeasure : volume.restrict Q ≤ volume.restrict slab :=
      Measure.restrict_mono hQsub le_rfl
    have huSq : Integrable (fun z : Vec d × ℝ => u.toFun z ^ 2)
        (volume.restrict slab) := u.memL2.integrable_sq
    have huSqQ : Integrable (fun z : Vec d × ℝ => u.toFun z ^ 2)
        (volume.restrict Q) := huSq.mono_measure hQmeasure
    have hp : 0 ≤ p := by dsimp [p]; positivity
    have hτcont : Continuous (fun z : Vec d × ℝ => nashPositiveTimeShift σ (z.2 - s)) :=
      nashPositiveTimeShift_contDiff_one.continuous.comp
        (continuous_snd.sub continuous_const)
    have hwcont : Continuous w := by
      dsimp [w]
      exact hτcont.rpow_const (fun _ => Or.inr hp)
    have hwMeas : AEStronglyMeasurable w (volume.restrict Q) :=
      hwcont.aestronglyMeasurable
    have hwBound : ∀ᵐ z ∂(volume.restrict Q), ‖w z‖ ≤ (H + σ) ^ p := by
      filter_upwards [ae_restrict_mem
        (MeasurableSet.prod MeasurableSet.univ measurableSet_Ioc)] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg
        (le_of_lt (lt_of_lt_of_le (by positivity)
          (nashPositiveTimeShift_lower hσ))) _)]
      have hshift := nashPositiveTimeShift_eq_add hσ (sub_nonneg.mpr hz.2.1.le)
      rw [hshift]
      have hElapsed : z.2 - s ≤ H := by linarith [hz.2.2]
      have hbase0 : 0 ≤ z.2 - s + σ := by linarith [hz.2.1, hσ]
      have hbasele : z.2 - s + σ ≤ H + σ := by linarith [hElapsed]
      exact Real.rpow_le_rpow hbase0 hbasele hp
    have hmul := huSqQ.mul_bdd hwMeas (c := (H + σ) ^ p) hwBound
    change Integrable
      (fun z : Vec d × ℝ =>
        (nashPositiveTimeShift σ (z.2 - s)) ^ ((d : ℝ) / 2) * u.toFun z ^ 2)
      (volume.restrict Q)
    simpa only [w, p, mul_comm] using hmul
  have hSliceInt : ∀ t ∈ Icc s (s + H),
      Integrable (fun x : Vec d => u.toFun (x, t) ^ 2) volume := by
    intro t ht
    exact PDE.Parabolic.Cauchy.Energy.cauchy_slice_square_integrable
      (by linarith) ha f hf2 u hu ht
  have hEarly : ∀ᵐ t ∂(volume.restrict (Ioc s (s + σ))),
      ∫ x : Vec d, u.toFun (x, t) ^ 2 ≤ ∫ x : Vec d, f x ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htH : t ∈ Icc s (s + H) :=
      ⟨ht.1.le, le_trans ht.2 (by linarith [hσH])⟩
    exact cauchy_l2_slice_contraction (by linarith) hLam ha hf2 hu htH
  have hLate : ∀ᵐ t ∂(volume.restrict (Ioc (s + σ) (s + H))),
      ∫ x : Vec d, u.toFun (x, t) ^ 2 ≤
        nashDiagonalSmoothingConstant d * (t - s) ^ (-(d : ℝ) / 2) * B ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htH : t ∈ Icc s (s + H) := ⟨by linarith [ht.1], ht.2⟩
    have hst : s < t := by linarith [ht.1, hσ]
    exact cauchy_nash_diagonal_bound hd (by linarith) hLam a ha f hf1 hf2 u hu
      hB hBf htH hst
  have hBsq : 0 ≤ B ^ 2 := sq_nonneg B
  refine ⟨hMomentInt, ?_⟩
  exact (nashTimeWeightedMoment_bound s hd hσ hσH hBsq hB₂ hC.le
    hMomentInt hSliceInt hEarly hLate).2

end PDE.Parabolic.Cauchy.Weights
