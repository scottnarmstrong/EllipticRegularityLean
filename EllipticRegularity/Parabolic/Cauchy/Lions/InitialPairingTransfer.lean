/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.Lions.IsL2cScalarTrace
public import EllipticRegularity.Parabolic.Cauchy.Lions.EnergyFields
public import EllipticRegularity.Parabolic.Energy.Limits

/-! # Initial pairings of representatives of the raw Lions field -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.Lions

/-- If a parabolic representative agrees almost everywhere with the raw Lions energy field,
weak continuity identifies all its initial spatial pairings with the datum. This is the trace
transfer needed after the all-time representative has been assembled. -/
theorem cauchyInitialPairing_eq_of_ae_representation
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 (volume : Measure (Vec d)))
    (u : CauchyX d s T) {u₀ : CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (W : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hWae : W.toFun =ᵐ[slabMeasure d s T] cauchyEnergyValue u)
    (ψ : Vec d → ℝ) (hψ : IsL2c (univ : Set (Vec d)) ψ) :
    ∫ x in (univ : Set (Vec d)), W.toFun (x, s) * ψ x = ∫ x, f x * ψ x := by
  obtain ⟨v, hvcont, hvraw, hvinit⟩ :=
    exists_cauchy_scalar_pairing_representative_of_isL2c
      hsT ha f hf u hclose hrep ψ hψ
  have hWcont : ContinuousOn
      (fun t => ∫ x in (univ : Set (Vec d)), W.toFun (x, t) * ψ x) (Icc s T) :=
    W.weakCont ψ hψ
  have hmeasure : (volume : Measure (Vec d)).prod
      (volume.restrict (Icc s T)) = slabMeasure d s T := by
    change (volume : Measure (Vec d)).prod (volume.restrict (Icc s T)) =
      (volume : Measure (Vec d × ℝ)).restrict (univ ×ˢ Icc s T)
    calc
      _ = (volume.restrict (univ : Set (Vec d))).prod
          (volume.restrict (Icc s T) : Measure ℝ) := by simp
      _ = (volume : Measure (Vec d × ℝ)).restrict (univ ×ˢ Icc s T) :=
        (PDE.Parabolic.Energy.volume_restrict_prod univ (Icc s T)).symm
  have hWprod : W.toFun =ᵐ[(volume : Measure (Vec d)).prod
      (volume.restrict (Icc s T))] cauchyEnergyValue u := by
    simpa only [hmeasure] using hWae
  have hWtime := PDE.Parabolic.Energy.ae_ae_swap hWprod
  have hpairAE : (fun t => ∫ x in (univ : Set (Vec d)), W.toFun (x, t) * ψ x) =ᵐ[
      volume.restrict (Icc s T)] cauchyValuePairing u ψ := by
    filter_upwards [hWtime] with t hWt
    rw [setIntegral_univ, cauchyValuePairing]
    apply integral_congr_ae
    filter_upwards [hWt] with x hx
    rw [hx]
  have hae : (fun t => ∫ x in (univ : Set (Vec d)), W.toFun (x, t) * ψ x) =ᵐ[
      volume.restrict (Icc s T)] v := hpairAE.trans hvraw
  have hEq := Measure.eqOn_Icc_of_ae_eq (volume : Measure ℝ) hsT.ne hae hWcont hvcont
  have hsI : s ∈ Icc s T := ⟨le_rfl, hsT.le⟩
  have hs := hEq hsI
  simpa only [setIntegral_univ] using hs.trans hvinit

/-- The initial pairing identity implies equality of the initial slice with the datum almost
everywhere, provided the representative has the local `L²` slices required by `ParH1Function`. -/
theorem cauchyInitial_ae_of_ae_representation
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 (volume : Measure (Vec d)))
    (u : CauchyX d s T) {u₀ : CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (W : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hWae : W.toFun =ᵐ[slabMeasure d s T] cauchyEnergyValue u) :
    ∀ᵐ x : Vec d, W.toFun (x, s) = f x := by
  have hEqK (K : Set (Vec d)) (hK : IsCompact K) :
      ∀ᵐ x ∂(volume : Measure (Vec d)), x ∈ K → W.toFun (x, s) = f x := by
    let g : Vec d → ℝ := fun x => W.toFun (x, s) - f x
    let η : Vec d → ℝ := K.indicator g
    have hWk : MemLp (fun x => W.toFun (x, s)) 2
        (volume.restrict K) := W.sliceL2loc s ⟨le_rfl, hsT.le⟩ K hK
          (subset_univ K)
    have hfU : MemLp f 2 (volume.restrict (univ : Set (Vec d))) := by
      simpa using hf
    have hfk : MemLp f 2 (volume.restrict K) :=
      hfU.mono_measure (Measure.restrict_mono (subset_univ K) le_rfl)
    have hgk : MemLp g 2 (volume.restrict K) := by
      exact (hWk.sub hfk)
    have hηLp : MemLp η 2 (volume : Measure (Vec d)) :=
      (memLp_indicator_iff_restrict hK.measurableSet).2 hgk
    have hηL2c : IsL2c (univ : Set (Vec d)) η := by
      refine ⟨?_, K, hK, subset_univ K, ?_⟩
      · simpa [PDE.MemL2On, PDE.MemLpOn, PDE.volumeOn, Measure.restrict_univ] using hηLp
      · intro x hx
        simp [η, hx]
    have hpair := cauchyInitialPairing_eq_of_ae_representation hsT ha f hf u hclose
      hrep W hWae η hηL2c
    have hpair' : (∫ x, W.toFun (x, s) * η x) = ∫ x, f x * η x := by
      simpa only [setIntegral_univ] using hpair
    have hleft : (∫ x, W.toFun (x, s) * η x) =
        ∫ x in K, W.toFun (x, s) * g x := by
      calc
        _ = ∫ x, K.indicator (fun x => W.toFun (x, s) * g x) x := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            by_cases hx : x ∈ K <;> simp [η, g, hx]
        _ = ∫ x in K, W.toFun (x, s) * g x := integral_indicator hK.measurableSet
    have hright : (∫ x, f x * η x) = ∫ x in K, f x * g x := by
      calc
        _ = ∫ x, K.indicator (fun x => f x * g x) x := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            by_cases hx : x ∈ K <;> simp [η, g, hx]
        _ = ∫ x in K, f x * g x := integral_indicator hK.measurableSet
    have hpairK : (∫ x in K, W.toFun (x, s) * g x) =
        ∫ x in K, f x * g x := by
      rw [← hleft, ← hright]
      exact hpair'
    have hWint : Integrable (fun x => W.toFun (x, s) * g x)
        (volume.restrict K) := hWk.integrable_mul hgk
    have hfint : Integrable (fun x => f x * g x) (volume.restrict K) :=
      hfk.integrable_mul hgk
    have hgsqInt : Integrable (fun x => g x ^ 2) (volume.restrict K) := by
      have hfun : (fun x => g x ^ 2) = g * g := by
        funext x
        simp [pow_two]
      rw [hfun]
      exact hgk.integrable_mul hgk
    have hgsqZero : ∫ x in K, g x ^ 2 = 0 := by
      calc
        ∫ x in K, g x ^ 2 = ∫ x in K,
            (W.toFun (x, s) * g x - f x * g x) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            dsimp [g]
            ring
        _ = (∫ x in K, W.toFun (x, s) * g x) -
              ∫ x in K, f x * g x := integral_sub hWint hfint
        _ = 0 := by rw [hpairK]; ring
    have hgsqAE : (fun x => g x ^ 2) =ᵐ[volume.restrict K] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (g x)) hgsqInt).mp hgsqZero
    have hgAE : g =ᵐ[volume.restrict K] 0 := by
      filter_upwards [hgsqAE] with x hx
      exact (sq_eq_zero_iff).mp hx
    have hgAE' : ∀ᵐ x ∂(volume.restrict K), g x = 0 := hgAE
    rw [ae_restrict_iff' hK.measurableSet] at hgAE'
    filter_upwards [hgAE'] with x hx
    intro hxK
    exact sub_eq_zero.mp (hx hxK)
  have hballs : ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure (Vec d)),
      x ∈ euclideanClosedBall (0 : Vec d) ((n : ℝ) + 1) →
        W.toFun (x, s) = f x := by
    intro n
    exact hEqK (euclideanClosedBall (0 : Vec d) ((n : ℝ) + 1))
      (isCompact_euclideanClosedBall 0 (by positivity))
  have hcoverAE : ∀ᵐ x ∂(volume : Measure (Vec d)),
      ∀ n : ℕ, x ∈ euclideanClosedBall (0 : Vec d) ((n : ℝ) + 1) →
        W.toFun (x, s) = f x := ae_all_iff.2 hballs
  filter_upwards [hcoverAE] with x hx
  have hxball : ∃ n : ℕ,
      x ∈ euclideanClosedBall (0 : Vec d) ((n : ℝ) + 1) := by
    obtain ⟨n, hn⟩ := exists_nat_gt (vecEuclideanNorm x)
    refine ⟨n, (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2 ?_⟩
    simpa only [sub_zero] using (le_of_lt hn).trans (by norm_num)
  obtain ⟨n, hn⟩ := hxball
  exact hx n hn

end PDE.Parabolic.Lions
