module

public import EllipticRegularity.Parabolic.Cauchy.Weights.NashMidpointEstimate
public import EllipticRegularity.Parabolic.Cauchy.Weights.NashRestriction
public import EllipticRegularity.Parabolic.Cauchy.Duality.AdjCoeff
public import EllipticRegularity.Parabolic.Cauchy.Duality.CauchyDuality
public import EllipticRegularity.Parabolic.Cauchy.L1.Contraction
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Nash--Aronson upper bound assembly

The estimate is assembled from two weighted half-interval estimates. The
global endpoint pairing is proved independently; the remaining input is
existence of an energy solution for arbitrary whole-space Cauchy data.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Weights

open MeasureTheory Set

private theorem nash_support_nonempty_of_positive_l1
    {d : ℕ} {f : Vec d → ℝ} {K : Set (Vec d)}
    (hfsupp : ∀ᵐ x : Vec d ∂volume, x ∉ K → f x = 0)
    (hL1 : 0 < ∫ x : Vec d, |f x|) : K.Nonempty := by
  by_contra hK
  have hEmpty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hK
  have hfzero : f =ᵐ[volume] 0 := by
    filter_upwards [hfsupp] with x hx
    exact hx (by simp [hEmpty])
  have habsZero : (fun x : Vec d => |f x|) =ᵐ[volume] 0 := by
    filter_upwards [hfzero] with x hx
    simp [hx]
  have hIntZero : ∫ x : Vec d, |f x| = 0 := by
    rw [integral_congr_ae habsZero]
    simp
  linarith

private theorem nash_zero_l1_ae
    {d : ℕ} {f : Vec d → ℝ} (hf1 : Integrable f volume)
    (hL1 : ∫ x : Vec d, |f x| = 0) : f =ᵐ[volume] 0 := by
  have hnonneg : 0 ≤ᵐ[volume] fun x : Vec d => |f x| :=
    ae_of_all _ fun x => abs_nonneg (f x)
  have habs : (fun x : Vec d => |f x|) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hf1.abs).mp hL1
  filter_upwards [habs] with x hx
  exact abs_eq_zero.mp hx

/-- The manuscript's upper bound follows from whole-space Cauchy solution
existence. The endpoint pairing, support geometry, zero-data cases, interval
restriction, weighted endpoint estimates, and Gaussian optimization are
proved here. -/
theorem nashAronsonUpper_of_cauchySolutionExistence
    (d : ℕ) (hd : 0 < d)
    (hCauchyEnergySolutionExists : ∀ (lam Lam s t : ℝ), s < t →
      ∀ (a : ParCoeffField d), IsParabolicCoeff lam Lam a univ (Icc s t) →
        ∀ f : Vec d → ℝ, MemLp f 2 volume →
          ∃ u : ParH1Function (univ : Set (Vec d)) (Icc s t),
            IsCauchySolution a s t f u) :
    ∃ C : ℝ, 0 < C ∧ ∀ Lam : ℝ, 1 ≤ Lam → ∀ (a : ParCoeffField d) (s t : ℝ), s < t →
      IsParabolicCoeff 1 Lam a univ (Icc s t) →
      ∀ r : ℝ, 0 ≤ r → ∀ f g : Vec d → ℝ,
      Integrable f volume → MemLp f 2 volume → Integrable g volume → MemLp g 2 volume →
      ∀ Kf Kg : Set (Vec d),
        (∀ᵐ x : Vec d, x ∉ Kf → f x = 0) →
        (∀ᵐ x : Vec d, x ∉ Kg → g x = 0) →
        (∀ x ∈ Kf, ∀ y ∈ Kg, r ^ 2 ≤ euclideanSqDist x y) →
        ∀ u : ParH1Function (univ : Set (Vec d)) (Icc s t),
          IsCauchySolution a s t f u →
          Integrable (fun x => g x * u.toFun (x, t)) volume ∧
            |∫ x, g x * u.toFun (x, t)| ≤
              C * (t - s) ^ (-(d : ℝ) / 2) *
                Real.exp (-r ^ 2 / (4 * Lam * (t - s)) +
                  Real.sqrt (((d : ℝ) + 2) / 2) * r / Real.sqrt (Lam * (t - s))) *
                ((∫ x, |f x|) * ∫ x, |g x|) := by
  refine ⟨nashMidpointConstant d, nashMidpointConstant_pos hd, ?_⟩
  intro Lam hLam a s t hst ha r hr f g hf1 hf2 hg1 hg2 Kf Kg hfsupp hgsupp hsep u hu
  have hUslice : MemLp (fun x : Vec d => u.toFun (x, t)) 2 volume :=
    cauchy_slice_memLp_of_solution hst ⟨hst.le, le_rfl⟩ ha hf2 u hu
  have hTargetInt : Integrable (fun x : Vec d => g x * u.toFun (x, t)) volume :=
    hg2.integrable_mul hUslice
  have hL1fNonneg : 0 ≤ ∫ x : Vec d, |f x| :=
    integral_nonneg_of_ae (ae_of_all _ fun x => abs_nonneg (f x))
  have hL1gNonneg : 0 ≤ ∫ x : Vec d, |g x| :=
    integral_nonneg_of_ae (ae_of_all _ fun x => abs_nonneg (g x))
  by_cases hfzero : ∫ x : Vec d, |f x| = 0
  · have hfAE := nash_zero_l1_ae hf1 hfzero
    have hfnorm : eLpNorm f 1 volume = 0 := by
      rw [eLpNorm_one_eq_lintegral_enorm hf1.aestronglyMeasurable]
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [hfAE] with x hx
      simp [hx]
    have hcontract := PDE.Parabolic.Cauchy.L1.cauchyL1Contraction
      d 1 Lam a s t hst ha f hf1 hf2 u hu t ⟨hst.le, le_rfl⟩
    have hUnorm : eLpNorm (parSlice u.toFun t) 1 volume = 0 :=
      le_antisymm (hcontract.2.trans_eq hfnorm) bot_le
    have huAE : (fun x : Vec d => u.toFun (x, t)) =ᵐ[volume] 0 :=
      (eLpNorm_eq_zero_iff (by norm_num : (1 : ENNReal) ≠ 0)).mp hUnorm
    have hprodZero : (fun x : Vec d => g x * u.toFun (x, t)) =ᵐ[volume] 0 := by
      filter_upwards [huAE] with x hx
      simp [hx]
    refine ⟨hTargetInt, ?_⟩
    rw [integral_eq_zero_of_ae hprodZero]
    simp [hfzero]
  · by_cases hgzero : ∫ x : Vec d, |g x| = 0
    · have hgAE := nash_zero_l1_ae hg1 hgzero
      have hprodZero : (fun x : Vec d => g x * u.toFun (x, t)) =ᵐ[volume] 0 := by
        filter_upwards [hgAE] with x hx
        simp [hx]
      refine ⟨hTargetInt, ?_⟩
      rw [integral_eq_zero_of_ae hprodZero]
      simp [hgzero]
    · have hL1fPos : 0 < ∫ x : Vec d, |f x| := lt_of_le_of_ne hL1fNonneg (Ne.symm hfzero)
      have hL1gPos : 0 < ∫ x : Vec d, |g x| := lt_of_le_of_ne hL1gNonneg (Ne.symm hgzero)
      have hKf : Kf.Nonempty := nash_support_nonempty_of_positive_l1 hfsupp hL1fPos
      have hKg : Kg.Nonempty := nash_support_nonempty_of_positive_l1 hgsupp hL1gPos
      let H : ℝ := (t - s) / 2
      let m : ℝ := s + H
      have hH : 0 < H := by dsimp [H]; linarith
      have h2H : 2 * H = t - s := by dsimp [H]; ring
      have hmH : (s + H) + H = t := by dsimp [H]; linarith
      have hm_lt_t : m < t := by dsimp [m]; linarith
      have hleftI : Icc s (s + H) ⊆ Icc s t := by
        refine Icc_subset_Icc le_rfl ?_
        dsimp [H]
        linarith
      have hrightI : Icc m t ⊆ Icc s t := by
        refine Icc_subset_Icc ?_ le_rfl
        dsimp [m, H]
        linarith
      let uLeft := PDE.Parabolic.Moser.restrictParH1TimeSet u hleftI
      have huLeft0 := cauchy_solution_restrict_closedInterval hleftI u hu
      have huLeft : IsCauchySolution a s (s + H) f uLeft := by
        refine ⟨huLeft0.1, ?_⟩
        filter_upwards [huLeft0.2, hu.2] with x hx₀ hx
        rw [hx₀, hx]
      have haLeft := parabolicCoeff_restrict_closedInterval ha hleftI
      have haRight := parabolicCoeff_restrict_closedInterval ha hrightI
      let b : ParCoeffField d := parAdjCoeff a (m + t)
      have hb0 := parAdjCoeff_isParabolicCoeff_core d 1 Lam a m t haRight
      have hb : IsParabolicCoeff 1 Lam b univ
          (Icc (s + H) ((s + H) + H)) := by
        simpa [b, m, hmH] using hb0
      obtain ⟨w, hw⟩ := hCauchyEnergySolutionExists 1 Lam m t hm_lt_t b (by
        simpa [b, m, hmH] using hb0) g hg2
      let uRight := PDE.Parabolic.Moser.restrictParH1TimeSet u hrightI
      have huRight0 := cauchy_solution_restrict_closedInterval hrightI u hu
      have huRight : IsCauchySolution a m t (fun x => u.toFun (x, m)) uRight := by
        exact huRight0
      have hUsliceMid : MemLp (fun x : Vec d => u.toFun (x, m)) 2 volume :=
        cauchy_slice_memLp_of_solution (t := m) hst
          ⟨by change s ≤ s + H; linarith,
            by change s + H ≤ t; linarith [h2H]⟩
          ha hf2 u hu
      have hdual := PDE.Parabolic.Duality.cauchyDuality_core
        d 1 Lam a m t hm_lt_t haRight (fun x => u.toFun (x, m)) g
        hUsliceMid hg2 uRight huRight w hw
      have hdualEq :
          ∫ x, g x * u.toFun (x, t) =
            ∫ x, u.toFun (x, m) * w.toFun (x, t) := by
        have hdualPair := hdual.2.2
        change ∫ x, g x * u.toFun (x, t) =
          ∫ x, (fun x => u.toFun (x, m)) x * w.toFun (x, t) at hdualPair
        exact hdualPair
      have htimeSubset : Icc (s + H) ((s + H) + H) ⊆ Icc m t := by
        rw [show m = s + H by rfl, hmH]
      let wMid := PDE.Parabolic.Moser.restrictParH1TimeSet w htimeSubset
      have hwMid0 := cauchy_solution_restrict_closedInterval htimeSubset w hw
      have hwMid : IsCauchySolution b (s + H) ((s + H) + H) g wMid := by
        refine ⟨hwMid0.1, ?_⟩
        filter_upwards [hw.2] with x hx
        change w.toFun (x, s + H) = g x
        simpa only [show m = s + H by rfl] using hx
      have hq : Integrable
          (fun x : Vec d => u.toFun (x, t) * g x) volume := by
        simpa only [mul_comm] using hTargetInt
      have hpairMid :
          ∫ x, u.toFun (x, t) * g x =
            ∫ x, uLeft.toFun (x, s + H) * wMid.toFun (x, (s + H) + H) := by
        calc
          ∫ x, u.toFun (x, t) * g x = ∫ x, g x * u.toFun (x, t) := by
            apply integral_congr_ae
            filter_upwards [] with x
            ring
          _ = ∫ x, u.toFun (x, m) * w.toFun (x, t) := hdualEq
          _ = ∫ x, uLeft.toFun (x, s + H) * wMid.toFun (x, (s + H) + H) := by
            apply integral_congr_ae
            filter_upwards [] with x
            change u.toFun (x, m) * w.toFun (x, t) =
              u.toFun (x, s + H) * w.toFun (x, (s + H) + H)
            have huTime : u.toFun (x, m) = u.toFun (x, s + H) := rfl
            have hwTime : w.toFun (x, t) = w.toFun (x, (s + H) + H) :=
              congrArg (fun τ : ℝ => w.toFun (x, τ)) hmH.symm
            rw [huTime, hwTime]
      have hmid := cauchy_nash_midpoint_offDiagonal
        (d := d) (Lam := Lam) (s := s) (H := H) (r := r)
        (Bf := ∫ x : Vec d, |f x|) (Bg := ∫ x : Vec d, |g x|)
        hd hLam hH hr hL1fPos hL1gPos hKf hKg hsep
        haLeft hb f g hf1 hf2 hg1 hg2 le_rfl le_rfl hfsupp hgsupp huLeft hwMid
        (q := fun x => u.toFun (x, t)) (qEnd := g) hq hpairMid
      have hden : 8 * Lam * H = 4 * Lam * (t - s) := by
        calc
          8 * Lam * H = 4 * Lam * (2 * H) := by ring
          _ = 4 * Lam * (t - s) := by rw [h2H]
      have hrootden : Lam * (2 * H) = Lam * (t - s) := by rw [h2H]
      have hbound :
          |∫ x, g x * u.toFun (x, t)| ≤
            nashMidpointConstant d * (t - s) ^ (-(d : ℝ) / 2) *
            Real.exp (-r ^ 2 / (4 * Lam * (t - s)) +
              Real.sqrt (((d : ℝ) + 2) / 2) * r / Real.sqrt (Lam * (t - s))) *
              ((∫ x, |f x|) * ∫ x, |g x|) := by
        have h : |∫ x, u.toFun (x, t) * g x| ≤
            nashMidpointConstant d * (2 * H) ^ (-(d : ℝ) / 2) *
              Real.exp (-r ^ 2 / (8 * Lam * H) +
                Real.sqrt (((d : ℝ) + 2) / 2) * r / Real.sqrt (Lam * (2 * H))) *
              ((∫ x, |f x|) * ∫ x, |g x|) := by
          simpa only [mul_assoc] using hmid.2
        have hcomm :
            ∫ x, u.toFun (x, t) * g x = ∫ x, g x * u.toFun (x, t) := by
          apply integral_congr_ae
          filter_upwards [] with x
          ring
        calc
          |∫ x, g x * u.toFun (x, t)| =
              |∫ x, u.toFun (x, t) * g x| := by rw [hcomm]
          _ ≤ nashMidpointConstant d * (2 * H) ^ (-(d : ℝ) / 2) *
              Real.exp (-r ^ 2 / (8 * Lam * H) +
                Real.sqrt (((d : ℝ) + 2) / 2) * r / Real.sqrt (Lam * (2 * H))) *
              ((∫ x, |f x|) * ∫ x, |g x|) := h
          _ = nashMidpointConstant d * (t - s) ^ (-(d : ℝ) / 2) *
              Real.exp (-r ^ 2 / (4 * Lam * (t - s)) +
                Real.sqrt (((d : ℝ) + 2) / 2) * r / Real.sqrt (Lam * (t - s))) *
              ((∫ x, |f x|) * ∫ x, |g x|) := by
                rw [hden, hrootden, h2H]
      exact ⟨hTargetInt, hbound⟩

end PDE.Parabolic.Cauchy.Weights
