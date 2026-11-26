module

public import BSlocalmax.FaceInequalities
public import PDEFoundation.Monotonicity.ACF.SliceTrunc
public import PDEFoundation.PDE.Ch4.CaccioppoliEnergy

/-!
# Approximation by smooth functions and the smoothed shell estimate

This file collects the following pieces, in dependency order: SmoothShell, ShellLimitAux, CutoffH1Approx, CutoffH1Aux, CutoffH1.
-/

-- ==== from SmoothShell.lean ====
-- Smooth version of inequality (25): for C¹ functions `w` there is a
-- cube cutoff `η` with Lipschitz control and an explicit bound for `∫ (w-c)₊² |∇η|²`.


@[expose] public section

open MeasureTheory Set PDE PDE.Ch4Infra

namespace PDE.BSlocalmax

variable {n : ℕ}

/-- Sobolev exponent `2* = 2n/(n-2)` of the faces. -/
noncomputable def qexp (n : ℕ) : ℝ := (2 * n : ℝ) / (n - 2)

/-- `δ = 2/2* = (n-2)/n`. -/
noncomputable def dexp (n : ℕ) : ℝ := ((n : ℝ) - 2) / n

/-- Explicit bound of the smooth shell estimate. -/
noncomputable def shellBound (n : ℕ) (Cb ρ σ c ε P : ℝ) : ℝ :=
  (σ - ρ) ^ (-(1 + 1 / dexp n)) *
    (c ^ (-((qexp n - 2) * dexp n)) * (Cb * P) +
      (σ - ρ) * (ε * (2 * ((n : ℝ) + 1) * 2 ^ n)) ^ dexp n) ^ (1 / dexp n)

lemma qexp_gt (hn : 3 ≤ n) : 2 < qexp n := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  unfold qexp
  rw [lt_div_iff₀ (by linarith)]
  linarith

lemma dexp_pos (hn : 3 ≤ n) : 0 < dexp n := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  unfold dexp
  exact div_pos (by linarith) (by linarith)

lemma dexp_le_one (hn : 3 ≤ n) : dexp n ≤ 1 := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  unfold dexp
  rw [div_le_one (by linarith)]
  linarith

lemma faceIntegral_lin {f : Vec (n + 1) → ℝ} (hf : Continuous f) (i : Fin (n + 1))
    (s r a b : ℝ) (hr : 0 ≤ r) :
    faceIntegral i s r (fun x => a * f x + b) =
      a * faceIntegral i s r f + (2 * r) ^ n * b := by
  have hKc : IsCompact (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hL : Continuous (fun y : Fin n → ℝ => (Fin.insertNth i (s * r) y : Vec (n + 1))) :=
    (contDiff_faceMap i (s * r)).continuous
  have h1 : IntegrableOn (fun y : Fin n → ℝ => a * f (Fin.insertNth i (s * r) y))
      (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)) :=
    (continuous_const.mul (hf.comp hL)).continuousOn.integrableOn_compact hKc
  unfold faceIntegral
  rw [integral_add h1 (integrableOn_const hKc.measure_lt_top.ne), integral_const_mul,
    setIntegral_const]
  simp only [Measure.real, volume_real_cube r hr, smul_eq_mul]

lemma cubeBoundaryIntegral_lin {f : Vec (n + 1) → ℝ} (hf : Continuous f) {r : ℝ} (hr : 0 ≤ r)
    (a b : ℝ) :
    cubeBoundaryIntegral r (fun x => a * f x + b) =
      a * cubeBoundaryIntegral r f + (2 * ((n : ℝ) + 1)) * ((2 * r) ^ n * b) := by
  unfold cubeBoundaryIntegral
  simp only [faceIntegral_lin hf _ _ _ a b hr, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.card_pair (show (-1 : ℝ) ≠ 1 by norm_num)]
  push_cast
  ring

lemma cubeBoundaryIntegral_nonneg {f : Vec (n + 1) → ℝ} (hf : ∀ x, 0 ≤ f x) (r : ℝ) :
    0 ≤ cubeBoundaryIntegral r f :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun s _ =>
    setIntegral_nonneg (MeasurableSet.univ_pi (fun _ => measurableSet_Icc)) (fun y _ => hf _)))

lemma measurableSet_shell' (ρ σ : ℝ) : MeasurableSet {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ} :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)

lemma integrableOn_shell_of_continuous {f : Vec (n + 1) → ℝ} (hf : Continuous f) {ρ σ : ℝ}
    (hσ : σ ≤ 1) : IntegrableOn f {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ} := by
  refine (hf.continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : Vec (n + 1)) 1)).mono_set ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (hx.2.le).trans hσ

/-- Pointwise majorant: `(t-c)₊² ≤ c^{-(q-2)} Ψ^q` if `Ψ ≥ t₊`. -/
lemma sq_pos_le_aux {c q t P : ℝ} (hc : 0 < c) (hq : 2 ≤ q) (hP : max t 0 ≤ P) :
    (max (t - c) 0) ^ 2 ≤ c ^ (-(q - 2)) * |P| ^ q := by
  have hP0 : 0 ≤ P := (le_max_right t 0).trans hP
  by_cases htc : t ≤ c
  · rw [max_eq_right (by linarith)]
    have : 0 ≤ c ^ (-(q - 2)) * |P| ^ q :=
      mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg (abs_nonneg _) _)
    simpa using this
  · push_neg at htc
    have ht0 : 0 < t := lt_trans hc htc
    have hPt : t ≤ P := (le_max_left t 0).trans hP
    have h1 : t ^ q ≤ P ^ q := Real.rpow_le_rpow ht0.le hPt (by linarith)
    have h2 : c ^ (q - 2) ≤ t ^ (q - 2) := Real.rpow_le_rpow hc.le htc.le (by linarith)
    have h3 : t ^ q = t ^ 2 * t ^ (q - 2) := by
      have := Real.rpow_add ht0 2 (q - 2)
      rw [show (2 : ℝ) + (q - 2) = q by ring, Real.rpow_two] at this
      exact this
    have hAB : c ^ (-(q - 2)) * c ^ (q - 2) = 1 := by
      rw [← Real.rpow_add hc]; simp
    have hA : 0 < c ^ (-(q - 2)) := Real.rpow_pos_of_pos hc _
    calc max (t - c) 0 ^ 2 = (t - c) ^ 2 := by rw [max_eq_left (by linarith)]
      _ ≤ t ^ 2 := by nlinarith
      _ = c ^ (-(q - 2)) * (t ^ 2 * c ^ (q - 2)) := by rw [mul_left_comm, hAB, mul_one]
      _ ≤ c ^ (-(q - 2)) * (t ^ 2 * t ^ (q - 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (sq_nonneg _)) hA.le
      _ = c ^ (-(q - 2)) * t ^ q := by rw [h3]
      _ ≤ c ^ (-(q - 2)) * |P| ^ q := by
          rw [abs_of_nonneg hP0]
          exact mul_le_mul_of_nonneg_left h1 hA.le

/-- **Smooth shell estimate** (inequality (25), `f = 0`, for `C¹` functions). -/
theorem smooth_shell_bound (hn : 3 ≤ n) :
    ∃ Cb : ℝ, 0 < Cb ∧ ∀ {ρ σ c ε : ℝ}, 1 / 2 ≤ ρ → ρ < σ → σ ≤ 1 → 0 < c → 0 < ε →
      ∀ w : Vec (n + 1) → ℝ, ContDiff ℝ 1 w →
      ∃ (K : ℝ) (η : Vec (n + 1) → ℝ), 0 ≤ K ∧
        K ≤ shellBound n Cb ρ σ c ε
              (∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ},
                ((|w x| + ε) ^ 2 + vecNormSq (classicalGradient w x))) /
            (ε * (2 * ρ) ^ n) ∧
        EucLip K η ∧ (∀ x, η x ∈ Icc (0 : ℝ) 1) ∧
        (∀ x, ‖x‖ ≤ ρ → η x = 1) ∧ (∀ x, σ ≤ ‖x‖ → η x = 0) ∧
        ∃ g : Vec (n + 1) → ℝ, (∀ x, (max (w x - c) 0) ^ 2 ≤ g x) ∧
          IntegrableOn (fun x => g x * vecNormSq (classicalGradient η x))
            {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ} ∧
          ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ}, g x * vecNormSq (classicalGradient η x) ≤
            shellBound n Cb ρ σ c ε
              (∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ},
                ((|w x| + ε) ^ 2 + vecNormSq (classicalGradient w x))) := by
  obtain ⟨Cb, hCb, hbs⟩ := boundary_sobolev hn
  haveI : NeZero n := ⟨by omega⟩
  refine ⟨Cb, hCb, ?_⟩
  intro ρ σ c ε hρ hρσ hσ hc hε w hw
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hq2 : 2 < qexp n := qexp_gt hn
  have hδ : 0 < dexp n := dexp_pos hn
  have hδ1 : dexp n ≤ 1 := dexp_le_one hn
  have hρ0 : 0 < ρ := by linarith
  have hL : 0 < σ - ρ := sub_pos.2 hρσ
  -- Majorant Ψ = ψ_ε ∘ w
  have hΨ : ContDiff ℝ 1 (fun x => psiEps ε (w x)) := (contDiff_psiEps hε).comp hw
  have hΨ0 : ∀ x, 0 ≤ psiEps ε (w x) := fun x => psiEps_nonneg ε _ hε
  have hFc : Continuous (fun x : Vec (n + 1) => |psiEps ε (w x)| ^ qexp n) :=
    hΨ.continuous.abs.rpow_const (fun _ => Or.inr (by linarith))
  have hgc : Continuous (fun x : Vec (n + 1) =>
      c ^ (-(qexp n - 2)) * |psiEps ε (w x)| ^ qexp n + ε) :=
    (continuous_const.mul hFc).add continuous_const
  have hgm : ∀ x, ε ≤ c ^ (-(qexp n - 2)) * |psiEps ε (w x)| ^ qexp n + ε := fun x => by
    have : 0 ≤ c ^ (-(qexp n - 2)) * |psiEps ε (w x)| ^ qexp n :=
      mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg (abs_nonneg _) _)
    linarith
  obtain ⟨hGc, hGge⟩ := boundaryIntegral_hyps hgc hε hgm (σ := σ) hρ0
  have hm : 0 < ε * (2 * ρ) ^ n := by positivity
  obtain ⟨K, η, hK0, hKle, hη, hη01, hη1, hη0, hint, hbound⟩ :=
    exists_cutoff_cubeShell (δ := dexp n) (m := ε * (2 * ρ) ^ n) hρ0 hρσ hδ hm hgc hGc
      (fun r hr => hGge r hr)
  -- Bound for ∫ G^δ
  set P : ℝ := ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ},
      ((|w x| + ε) ^ 2 + vecNormSq (classicalGradient w x)) with hP
  have hS : ∫ r in Ioo ρ σ, (cubeBoundaryIntegral r
      (fun x => c ^ (-(qexp n - 2)) * |psiEps ε (w x)| ^ qexp n + ε)) ^ dexp n ≤
      c ^ (-((qexp n - 2) * dexp n)) * (Cb * P) +
        (σ - ρ) * (ε * (2 * ((n : ℝ) + 1) * 2 ^ n)) ^ dexp n := by
    have hcont : ContinuousOn (fun r => cubeBoundaryIntegral r
        (fun x : Vec (n + 1) => |psiEps ε (w x)| ^ qexp n)) (Icc ρ σ) :=
      (continuousOn_cubeBoundaryIntegral hFc).mono (fun r hr => lt_of_lt_of_le hρ0 hr.1)
    have hI1 : IntegrableOn (fun r => (cubeBoundaryIntegral r
        (fun x => c ^ (-(qexp n - 2)) * |psiEps ε (w x)| ^ qexp n + ε)) ^ dexp n) (Ioo ρ σ) :=
      (ContinuousOn.integrableOn_Icc
        (hGc.rpow_const (fun r _ => Or.inr hδ.le))).mono_set Ioo_subset_Icc_self
    have hI2 : IntegrableOn (fun r => (cubeBoundaryIntegral r
        (fun x : Vec (n + 1) => |psiEps ε (w x)| ^ qexp n)) ^ dexp n) (Ioo ρ σ) :=
      (ContinuousOn.integrableOn_Icc
        (hcont.rpow_const (fun r _ => Or.inr hδ.le))).mono_set Ioo_subset_Icc_self
    have hpt : ∀ r ∈ Ioo ρ σ, (cubeBoundaryIntegral r
        (fun x => c ^ (-(qexp n - 2)) * |psiEps ε (w x)| ^ qexp n + ε)) ^ dexp n ≤
        c ^ (-((qexp n - 2) * dexp n)) * (cubeBoundaryIntegral r
          (fun x : Vec (n + 1) => |psiEps ε (w x)| ^ qexp n)) ^ dexp n +
          (ε * (2 * ((n : ℝ) + 1) * 2 ^ n)) ^ dexp n := by
      intro r hr
      have hr0 : 0 ≤ r := (hρ0.trans hr.1).le
      have hB0 : 0 ≤ cubeBoundaryIntegral r
          (fun x : Vec (n + 1) => |psiEps ε (w x)| ^ qexp n) :=
        cubeBoundaryIntegral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) _) r
      have ha : 0 ≤ c ^ (-(qexp n - 2)) := Real.rpow_nonneg hc.le _
      have hlin := cubeBoundaryIntegral_lin hFc hr0 (c ^ (-(qexp n - 2))) ε
      rw [hlin]
      have hE0 : 0 ≤ (2 * ((n : ℝ) + 1)) * ((2 * r) ^ n * ε) := by positivity
      have hE : (2 * ((n : ℝ) + 1)) * ((2 * r) ^ n * ε) ≤ ε * (2 * ((n : ℝ) + 1) * 2 ^ n) := by
        have h2r : (2 * r) ^ n ≤ 2 ^ n :=
          pow_le_pow_left₀ (by positivity) (by linarith [hr.2]) n
        have : (2 * ((n : ℝ) + 1)) * ((2 * r) ^ n * ε) ≤ (2 * ((n : ℝ) + 1)) * (2 ^ n * ε) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2r hε.le) (by positivity)
        linarith [this]
      calc (c ^ (-(qexp n - 2)) * cubeBoundaryIntegral r
              (fun x : Vec (n + 1) => |psiEps ε (w x)| ^ qexp n) +
            (2 * ((n : ℝ) + 1)) * ((2 * r) ^ n * ε)) ^ dexp n
          ≤ (c ^ (-(qexp n - 2)) * cubeBoundaryIntegral r
              (fun x : Vec (n + 1) => |psiEps ε (w x)| ^ qexp n)) ^ dexp n +
            ((2 * ((n : ℝ) + 1)) * ((2 * r) ^ n * ε)) ^ dexp n :=
            Real.rpow_add_le_add_rpow (mul_nonneg ha hB0) hE0 hδ.le hδ1
        _ ≤ c ^ (-((qexp n - 2) * dexp n)) * (cubeBoundaryIntegral r
              (fun x : Vec (n + 1) => |psiEps ε (w x)| ^ qexp n)) ^ dexp n +
            (ε * (2 * ((n : ℝ) + 1) * 2 ^ n)) ^ dexp n := by
            refine add_le_add (le_of_eq ?_) (Real.rpow_le_rpow hE0 hE hδ.le)
            rw [Real.mul_rpow ha hB0, ← Real.rpow_mul hc.le, neg_mul]
    -- Sobolev on the boundaries
    have hsob := hbs hρ hρσ hσ (fun x => psiEps ε (w x)) hΨ
    have hshell : ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ},
        ((psiEps ε (w x)) ^ 2 + vecNormSq (classicalGradient (fun y => psiEps ε (w y)) x)) ≤ P := by
      refine setIntegral_mono_on ?_ ?_ (measurableSet_shell' ρ σ) (fun x _ => ?_)
      · exact integrableOn_shell_of_continuous
          ((hΨ.continuous.pow 2).add (continuous_vecNormSq_grad hΨ)) hσ
      · exact integrableOn_shell_of_continuous
          (((hw.continuous.abs.add continuous_const).pow 2).add (continuous_vecNormSq_grad hw)) hσ
      · have h1 : psiEps ε (w x) ≤ |w x| + ε := psiEps_le ε _ hε
        have h2 := hΨ0 x
        have h3 := vecNormSq_grad_psiEps_le hε hw x
        have h4 : psiEps ε (w x) ^ 2 ≤ (|w x| + ε) ^ 2 := pow_le_pow_left₀ h2 h1 2
        linarith [h3, h4]
    have hBint : ∫ r in Ioo ρ σ, (cubeBoundaryIntegral r
        (fun x : Vec (n + 1) => |psiEps ε (w x)| ^ qexp n)) ^ dexp n ≤ Cb * P := by
      refine hsob.trans ?_
      refine mul_le_mul_of_nonneg_left (le_trans (le_of_eq ?_) hshell) hCb.le
      rfl
    calc ∫ r in Ioo ρ σ, (cubeBoundaryIntegral r
          (fun x => c ^ (-(qexp n - 2)) * |psiEps ε (w x)| ^ qexp n + ε)) ^ dexp n
        ≤ ∫ r in Ioo ρ σ, (c ^ (-((qexp n - 2) * dexp n)) * (cubeBoundaryIntegral r
          (fun x : Vec (n + 1) => |psiEps ε (w x)| ^ qexp n)) ^ dexp n +
            (ε * (2 * ((n : ℝ) + 1) * 2 ^ n)) ^ dexp n) :=
          setIntegral_mono_on hI1 ((hI2.const_mul _).add (integrableOn_const (by simp)))
            measurableSet_Ioo hpt
      _ = c ^ (-((qexp n - 2) * dexp n)) * (∫ r in Ioo ρ σ, (cubeBoundaryIntegral r
          (fun x : Vec (n + 1) => |psiEps ε (w x)| ^ qexp n)) ^ dexp n) +
            (σ - ρ) * (ε * (2 * ((n : ℝ) + 1) * 2 ^ n)) ^ dexp n := by
          rw [integral_add (hI2.const_mul _) (integrableOn_const (by simp)), integral_const_mul,
            setIntegral_const, Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal hL.le,
            smul_eq_mul]
      _ ≤ _ := by
          have ha : 0 ≤ c ^ (-((qexp n - 2) * dexp n)) := Real.rpow_nonneg hc.le _
          linarith [mul_le_mul_of_nonneg_left hBint ha]
  -- Combine
  have hG0 : 0 ≤ ∫ r in Ioo ρ σ, (cubeBoundaryIntegral r
      (fun x => c ^ (-(qexp n - 2)) * |psiEps ε (w x)| ^ qexp n + ε)) ^ dexp n :=
    setIntegral_nonneg measurableSet_Ioo (fun r hr => Real.rpow_nonneg
      (cubeBoundaryIntegral_nonneg (fun x => add_nonneg (mul_nonneg (Real.rpow_nonneg hc.le _)
        (Real.rpow_nonneg (abs_nonneg _) _)) hε.le) r) _)
  have hT : (σ - ρ) ^ (-(1 + 1 / dexp n)) * (∫ r in Ioo ρ σ, (cubeBoundaryIntegral r
      (fun x => c ^ (-(qexp n - 2)) * |psiEps ε (w x)| ^ qexp n + ε)) ^ dexp n) ^ (1 / dexp n) ≤
      shellBound n Cb ρ σ c ε P := by
    unfold shellBound
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hG0 hS (by positivity)) (Real.rpow_nonneg hL.le _)
  have hK1 : K ≤ shellBound n Cb ρ σ c ε P / (ε * (2 * ρ) ^ n) :=
    hKle.trans (div_le_div_of_nonneg_right hT hm.le)
  refine ⟨K, η, hK0, hK1, hη, hη01, hη1, hη0,
    fun x => c ^ (-(qexp n - 2)) * |psiEps ε (w x)| ^ qexp n + ε, fun x => ?_, hint,
    hbound.trans hT⟩
  have := sq_pos_le_aux (c := c) (q := qexp n) (t := w x) (P := psiEps ε (w x)) hc hq2.le
    (psiEps_ge ε _ hε)
  linarith

end PDE.BSlocalmax
end

-- ==== from ShellLimitAux.lean ====
-- Auxiliary lemmas for the passage to the limit smooth → H¹:
-- pointwise AM-GM estimates and L¹-closeness of `(w_i - c)₊²` to `(z - c)₊²`.


@[expose] public section

open MeasureTheory Set Filter PDE PDE.Ch4Infra

namespace PDE.BSlocalmax

lemma amgm_sq (a b l : ℝ) (hl : 0 < l) : (a + b) ^ 2 ≤ (1 + l) * a ^ 2 + (1 + 1 / l) * b ^ 2 := by
  rw [← sub_nonneg]
  have h : (1 + l) * a ^ 2 + (1 + 1 / l) * b ^ 2 - (a + b) ^ 2 = (l * a - b) ^ 2 / l := by
    field_simp
    ring
  rw [h]
  positivity

lemma amgm_vec {d : ℕ} (X Y : Vec d) (l : ℝ) (hl : 0 < l) :
    vecNormSq X ≤ (1 + l) * vecNormSq Y + (1 + 1 / l) * vecNormSq (X - Y) := by
  have h1 : vecEuclideanNorm X ≤ vecEuclideanNorm Y + vecEuclideanNorm (X - Y) := by
    have := vecEuclideanNorm_add_le Y (X - Y)
    simpa using this
  have h2 := amgm_sq (vecEuclideanNorm Y) (vecEuclideanNorm (X - Y)) l hl
  have h3 : vecEuclideanNorm X ^ 2 ≤ (vecEuclideanNorm Y + vecEuclideanNorm (X - Y)) ^ 2 :=
    pow_le_pow_left₀ (vecEuclideanNorm_nonneg _) h1 2
  rw [vecEuclideanNorm_sq] at h3
  rw [vecEuclideanNorm_sq, vecEuclideanNorm_sq] at h2
  linarith

lemma sqdiff_bound (a b c l : ℝ) (hc : 0 ≤ c) (hl : 0 < l) :
    |max (a - c) 0 ^ 2 - max (b - c) 0 ^ 2| ≤ 4 * l * b ^ 2 + (1 / (4 * l) + 1) * (a - b) ^ 2 := by
  set u := max (a - c) 0 with hu
  set v := max (b - c) 0 with hv
  set d := |a - b| with hd
  have hu0 : 0 ≤ u := le_max_right _ _
  have hv0 : 0 ≤ v := le_max_right _ _
  have h1 : |u - v| ≤ d := by
    have := abs_max_sub_max_le_abs (a - c) (b - c) 0
    simpa [hu, hv, hd] using this
  have hvb : v ≤ |b| := max_le (by linarith [le_abs_self b]) (abs_nonneg b)
  have hua : u ≤ |a| := max_le (by linarith [le_abs_self a]) (abs_nonneg a)
  have hab : |a| ≤ |b| + d := by
    have := abs_sub_abs_le_abs_sub a b
    linarith
  have hd0 : 0 ≤ d := abs_nonneg _
  have h2 : |u ^ 2 - v ^ 2| ≤ d * (2 * |b| + d) := by
    have : u ^ 2 - v ^ 2 = (u - v) * (u + v) := by ring
    rw [this, abs_mul, abs_of_nonneg (by linarith : 0 ≤ u + v)]
    exact mul_le_mul h1 (by linarith) (by linarith) hd0
  have h3 : 2 * d * |b| ≤ 4 * l * |b| ^ 2 + d ^ 2 / (4 * l) := by
    rw [← sub_nonneg]
    have : 4 * l * |b| ^ 2 + d ^ 2 / (4 * l) - 2 * d * |b| = (4 * l * |b| - d) ^ 2 / (4 * l) := by
      field_simp
      ring
    rw [this]
    positivity
  have hdd : d ^ 2 = (a - b) ^ 2 := sq_abs _
  have hbb : |b| ^ 2 = b ^ 2 := sq_abs _
  have h4 : d ^ 2 / (4 * l) = 1 / (4 * l) * d ^ 2 := by ring
  calc |u ^ 2 - v ^ 2| ≤ d * (2 * |b| + d) := h2
    _ = 2 * d * |b| + d ^ 2 := by ring
    _ ≤ 4 * l * |b| ^ 2 + d ^ 2 / (4 * l) + d ^ 2 := by linarith
    _ = 4 * l * b ^ 2 + (1 / (4 * l) + 1) * (a - b) ^ 2 := by
      rw [h4, hbb, hdd]; ring

/-- L¹-closeness: `∫_S (w_i - z)² → 0` implies `∫_S |(w_i-c)₊² - (z-c)₊²| → 0`. -/
lemma eventually_L1_close {d : ℕ} {S : Set (Vec d)} {w : ℕ → Vec d → ℝ} {z : Vec d → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hz : IntegrableOn (fun x => z x ^ 2) S)
    (hdv : ∀ i, IntegrableOn (fun x => (w i x - z x) ^ 2) S)
    (hcv : Tendsto (fun i => ∫ x in S, (w i x - z x) ^ 2) atTop (nhds 0))
    (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ i in atTop, ∫ x in S, |max (w i x - c) 0 ^ 2 - max (z x - c) 0 ^ 2| ≤ θ := by
  set B : ℝ := ∫ x in S, z x ^ 2 with hB
  have hB0 : 0 ≤ B := setIntegral_nonneg_of_ae_restrict
    (Filter.Eventually.of_forall (fun x => sq_nonneg _))
  set l : ℝ := θ / (8 * (B + 1)) with hl
  have hl0 : 0 < l := by positivity
  set A : ℝ := 1 / (4 * l) + 1 with hA
  have hA0 : 0 < A := by positivity
  have hev : ∀ᶠ i in atTop, ∫ x in S, (w i x - z x) ^ 2 < θ / (2 * A) :=
    (tendsto_order.1 hcv).2 _ (by positivity)
  filter_upwards [hev] with i hi
  have hpt : ∀ x, |max (w i x - c) 0 ^ 2 - max (z x - c) 0 ^ 2| ≤
      4 * l * z x ^ 2 + A * (w i x - z x) ^ 2 := fun x =>
    sqdiff_bound (w i x) (z x) c l hc hl0
  have hint : IntegrableOn (fun x => 4 * l * z x ^ 2 + A * (w i x - z x) ^ 2) S :=
    (hz.const_mul _).add ((hdv i).const_mul _)
  calc ∫ x in S, |max (w i x - c) 0 ^ 2 - max (z x - c) 0 ^ 2|
      ≤ ∫ x in S, (4 * l * z x ^ 2 + A * (w i x - z x) ^ 2) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => abs_nonneg _)) hint
          (Filter.Eventually.of_forall hpt)
    _ = 4 * l * B + A * ∫ x in S, (w i x - z x) ^ 2 := by
        rw [integral_add (hz.const_mul _) ((hdv i).const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ θ := by
        have h1 : 4 * l * B ≤ θ / 2 := by
          rw [hl]
          have : 4 * (θ / (8 * (B + 1))) * B = θ / 2 * (B / (B + 1)) := by
            field_simp
            ring
          rw [this]
          have : B / (B + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
          nlinarith
        have h2 : A * ∫ x in S, (w i x - z x) ^ 2 ≤ θ / 2 := by
          have := mul_le_mul_of_nonneg_left hi.le hA0.le
          have e : A * (θ / (2 * A)) = θ / 2 := by field_simp
          linarith
        linarith

end PDE.BSlocalmax
end

-- ==== from CutoffH1Approx.lean ====
-- Smooth approximation of (u-δ)₊ in H¹ on the cube Metric.ball 0 1.


@[expose] public section

open MeasureTheory Set Filter PDE
open scoped ENNReal Topology

namespace PDE.BSlocalmax

theorem isOpenBoundedConvexDomain_cube (d : ℕ) :
    IsOpenBoundedConvexDomain (Metric.ball (0 : Vec d) 1) :=
  ⟨Metric.isOpen_ball, Bornology.IsBounded.isBoundedDomain Metric.isBounded_ball,
    convex_ball _ _⟩

theorem exists_smooth_approx_cube {d : ℕ} (u : H1Function (Metric.ball (0 : Vec d) 1))
    (δ : ℝ) :
    ∃ w : ℕ → Vec d → ℝ, (∀ n, ContDiff ℝ 1 (w n)) ∧
      IntegrableOn (fun x => (max (u.toFun x - δ) 0) ^ 2) (Metric.ball (0 : Vec d) 1) ∧
      IntegrableOn (fun x => vecNormSq ({y | δ < u.toFun y}.indicator u.grad x))
        (Metric.ball (0 : Vec d) 1) ∧
      (∀ n, IntegrableOn (fun x => w n x ^ 2) (Metric.ball (0 : Vec d) 1)) ∧
      (∀ n, IntegrableOn (fun x => vecNormSq (classicalGradient (w n) x))
        (Metric.ball (0 : Vec d) 1)) ∧
      (∀ n, IntegrableOn (fun x => (w n x - max (u.toFun x - δ) 0) ^ 2)
        (Metric.ball (0 : Vec d) 1)) ∧
      (∀ n, IntegrableOn (fun x => vecNormSq (classicalGradient (w n) x -
        {y | δ < u.toFun y}.indicator u.grad x)) (Metric.ball (0 : Vec d) 1)) ∧
      Tendsto (fun n => ∫ x in Metric.ball (0 : Vec d) 1,
        (w n x - max (u.toFun x - δ) 0) ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x in Metric.ball (0 : Vec d) 1,
        vecNormSq (classicalGradient (w n) x -
          {y | δ < u.toFun y}.indicator u.grad x)) atTop (𝓝 0) := by
  have hU := isOpenBoundedConvexDomain_cube d
  have hr0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hball : Metric.closedBall (0 : Vec d) (1 / 2) ⊆ Metric.ball (0 : Vec d) 1 :=
    Metric.closedBall_subset_ball (by norm_num)
  set V := u.positivePartSubConst hU δ with hV
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  set W := fun n => W1pFunction.convexApproxSmoothW1p hU hp V.toW1pFunction (0 : Vec d) hr0 n
    with hW
  have hVv : V.toFun = fun y => max (u.toFun y - δ) 0 := rfl
  have hVg : V.grad = {y | δ < u.toFun y}.indicator u.grad := rfl
  have hWg : ∀ n, (W n).grad = classicalGradient (W n).toFun := fun n => rfl
  have hVmem : MemLp V.toFun 2 (volume.restrict (Metric.ball (0 : Vec d) 1)) := V.memL2
  have hVgmem : ∀ i, MemLp (fun x => V.grad x i) 2
      (volume.restrict (Metric.ball (0 : Vec d) 1)) := V.gradMemL2
  have hWmem : ∀ n, MemLp (W n).toFun 2 (volume.restrict (Metric.ball (0 : Vec d) 1)) :=
    fun n => (W n).memLp
  have hWgmem : ∀ n i, MemLp (fun x => (W n).grad x i) 2
      (volume.restrict (Metric.ball (0 : Vec d) 1)) := fun n => (W n).gradMemLp
  have hdiffg : ∀ n, Integrable (fun x => vecNormSq ((W n).grad x - V.grad x))
      (volume.restrict (Metric.ball (0 : Vec d) 1)) := fun n =>
    integrable_vecNormSq_of_coord fun i => (hWgmem n i).sub (hVgmem i)
  refine ⟨fun n => (W n).toFun, fun n => ?_, hVmem.integrable_sq,
    integrable_vecNormSq_of_coord hVgmem, fun n => (hWmem n).integrable_sq,
    fun n => integrable_vecNormSq_of_coord (hWgmem n),
    fun n => ((hWmem n).sub hVmem).integrable_sq, hdiffg, ?_, ?_⟩
  · exact (W1pFunction.contDiff_convexApproxSmoothW1p_toFun hU hp V.toW1pFunction
      (0 : Vec d) hr0 n).of_le (by simp)
  · refine (tendsto_integral_sq_of_eLpNorm (f := fun n x => (W n).toFun x - V.toFun x)
      (fun n => (hWmem n).sub hVmem) ?_)
    exact W1pFunction.tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub hU hp (by norm_num)
      V.toW1pFunction hball hr0
  · have hmeas : ∀ n, AEStronglyMeasurable
        (fun x => vecEuclideanNorm ((W n).grad x - V.grad x))
        (volume.restrict (Metric.ball (0 : Vec d) 1)) := fun n =>
      aestronglyMeasurable_vecEuclideanNorm fun i =>
        (hWgmem n i).aestronglyMeasurable.sub (hVgmem i).aestronglyMeasurable
    have hmem : ∀ n, MemLp (fun x => vecEuclideanNorm ((W n).grad x - V.grad x)) 2
        (volume.restrict (Metric.ball (0 : Vec d) 1)) := fun n =>
      (memLp_two_iff_integrable_sq (hmeas n)).2 (by
        simpa only [vecEuclideanNorm_sq] using hdiffg n)
    have := tendsto_integral_sq_of_eLpNorm hmem
      (W1pFunction.tendsto_convexApproxSmoothW1p_grad_euclidean_eLpNorm_sub hU hp (by norm_num)
        V.toW1pFunction hball hr0)
    simp only [vecEuclideanNorm_sq] at this
    exact this

end PDE.BSlocalmax
end

-- ==== from CutoffH1Aux.lean ====
-- Auxiliary lemmas: monotonicity/continuity of `shellBound`, vanishing of ∇η
-- outside the shell.


@[expose] public section

open MeasureTheory Set Filter PDE PDE.Ch4Infra

namespace PDE.BSlocalmax

variable {n : ℕ}

lemma shellBound_mono (hn : 3 ≤ n) {Cb ρ σ c ε P P' : ℝ} (hCb : 0 ≤ Cb) (hρσ : ρ ≤ σ)
    (hc : 0 < c) (hε : 0 ≤ ε) (hP : 0 ≤ P) (hPP : P ≤ P') :
    shellBound n Cb ρ σ c ε P ≤ shellBound n Cb ρ σ c ε P' := by
  have hδ := dexp_pos hn
  unfold shellBound
  have h0 : 0 ≤ σ - ρ := by linarith
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg h0 _)
  have hc0 : 0 ≤ c ^ (-((qexp n - 2) * dexp n)) := Real.rpow_nonneg hc.le _
  have hT : 0 ≤ (σ - ρ) * (ε * (2 * ((n : ℝ) + 1) * 2 ^ n)) ^ dexp n :=
    mul_nonneg h0 (Real.rpow_nonneg (by positivity) _)
  have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPP hCb) hc0
  refine Real.rpow_le_rpow (add_nonneg (mul_nonneg hc0 (mul_nonneg hCb hP)) hT) ?_
    (one_div_nonneg.2 hδ.le)
  linarith

lemma continuous_shellBound (hn : 3 ≤ n) (Cb ρ σ c : ℝ) {e p : ℝ → ℝ} (he : Continuous e)
    (hp : Continuous p) :
    Continuous (fun t => shellBound n Cb ρ σ c (e t) (p t)) := by
  have hδ := dexp_pos hn
  unfold shellBound
  refine continuous_const.mul
    (Continuous.rpow_const ?_ (fun _ => Or.inr (one_div_nonneg.2 hδ.le)))
  exact (continuous_const.mul (continuous_const.mul hp)).add
    (continuous_const.mul
      (Continuous.rpow_const (he.mul continuous_const) (fun _ => Or.inr hδ.le)))

lemma classicalGradient_eq_zero_of_eventually {d : ℕ} {η : Vec d → ℝ} {x : Vec d} {c : ℝ}
    (h : ∀ᶠ y in nhds x, η y = c) : classicalGradient η x = 0 := by
  funext i
  have h' : η =ᶠ[nhds x] fun _ => c := h
  have : fderiv ℝ η x = 0 := by
    rw [h'.fderiv_eq]
    simp
  simp [classicalGradient, this]

lemma setIntegral_cube_eq_shell {ρ σ : ℝ} {η : Vec (n + 1) → ℝ} (hσ : σ ≤ 1)
    (h1 : ∀ x, ‖x‖ ≤ ρ → η x = 1) (h0 : ∀ x, σ ≤ ‖x‖ → η x = 0) (f : Vec (n + 1) → ℝ) :
    ∫ x in Metric.ball (0 : Vec (n + 1)) 1, f x * vecNormSq (classicalGradient η x) =
      ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ},
        f x * vecNormSq (classicalGradient η x) := by
  refine setIntegral_eq_of_subset_of_ae_diff_eq_zero
    Metric.isOpen_ball.measurableSet.nullMeasurableSet ?_ ?_
  · intro x hx
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_lt_of_le hx.2 hσ
  · have hn1 : ∀ᵐ x : Vec (n + 1) ∂volume, ‖x‖ ≠ ρ := by
      have := volume_supNorm_sphere (d := n + 1) (0 : Vec (n + 1)) ρ
      rw [ae_iff]
      simpa using this
    have hn2 : ∀ᵐ x : Vec (n + 1) ∂volume, ‖x‖ ≠ σ := by
      have := volume_supNorm_sphere (d := n + 1) (0 : Vec (n + 1)) σ
      rw [ae_iff]
      simpa using this
    have hz : vecNormSq (0 : Vec (n + 1)) = 0 := by simp [vecNormSq, vecDot]
    filter_upwards [hn1, hn2] with x hx1 hx2 hx
    obtain ⟨_, hxS⟩ := hx
    have hxn : ‖x‖ ≤ ρ ∨ σ ≤ ‖x‖ := by
      by_contra hc
      push_neg at hc
      exact hxS ⟨hc.1, hc.2⟩
    rcases hxn with h | h
    · have hlt : ‖x‖ < ρ := lt_of_le_of_ne h hx1
      have hev : ∀ᶠ y in nhds x, η y = 1 :=
        Filter.mem_of_superset ((isOpen_lt continuous_norm continuous_const).mem_nhds hlt)
          (fun y hy => h1 y (le_of_lt hy))
      rw [classicalGradient_eq_zero_of_eventually hev, hz, mul_zero]
    · have hlt : σ < ‖x‖ := lt_of_le_of_ne h (Ne.symm hx2)
      have hev : ∀ᶠ y in nhds x, η y = 0 :=
        Filter.mem_of_superset ((isOpen_lt continuous_const continuous_norm).mem_nhds hlt)
          (fun y hy => h0 y (le_of_lt hy))
      rw [classicalGradient_eq_zero_of_eventually hev, hz, mul_zero]

end PDE.BSlocalmax
end

-- ==== from CutoffH1.lean ====
-- Passage to the limit smooth → H¹: cutoff lemma for (u-h)₊ ∈ H¹(cube).


@[expose] public section

open MeasureTheory Set Filter PDE PDE.Ch4Infra
open scoped Topology

namespace PDE.BSlocalmax

variable {n : ℕ}

lemma max_sub_max_eq (a c : ℝ) (hc : 0 ≤ c) : max (max a 0 - c) 0 = max (a - c) 0 := by
  rcases le_total a 0 with ha | ha
  · rw [max_eq_right ha, max_eq_right (by linarith : 0 - c ≤ 0),
      max_eq_right (by linarith : a - c ≤ 0)]
  · rw [max_eq_left ha]

lemma sqdiff_bound' (a b c : ℝ) (hc : 0 ≤ c) :
    |max (a - c) 0 ^ 2 - max (b - c) 0 ^ 2| ≤ b ^ 2 + 2 * (a - b) ^ 2 := by
  have h := sqdiff_bound a b c (1 / 4) hc (by norm_num)
  have e1 : 4 * (1 / 4 : ℝ) * b ^ 2 = b ^ 2 := by ring
  have e2 : (1 / (4 * (1 / 4 : ℝ)) + 1) = 2 := by norm_num
  rw [e1, e2] at h
  exact h

lemma shell_subset_cube {ρ σ : ℝ} (hσ : σ ≤ 1) :
    {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ} ⊆ Metric.ball (0 : Vec (n + 1)) 1 := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right]
  exact lt_of_lt_of_le hx.2 hσ

lemma shell_subset_pi {ρ σ : ℝ} (hσ : σ ≤ 1) :
    {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ} ⊆
      Set.pi univ (fun _ : Fin (n + 1) => Icc (-1 : ℝ) 1) := by
  intro x hx
  refine Set.mem_univ_pi.2 fun i => ?_
  have h1 : |x i| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i
  have h2 : ‖x‖ < 1 := lt_of_lt_of_le hx.2 hσ
  exact abs_le.1 (by linarith)

lemma volume_shell_ne_top {ρ σ : ℝ} (hσ : σ ≤ 1) :
    volume {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ} ≠ ⊤ :=
  ne_top_of_le_ne_top (isCompact_univ_pi (fun _ => isCompact_Icc)).measure_lt_top.ne
    (measure_mono (shell_subset_pi hσ))

lemma volume_shell_le {ρ σ : ℝ} (hσ : σ ≤ 1) :
    (volume {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ}).toReal ≤ 2 ^ (n + 1) := by
  have hfin : volume (Set.pi univ (fun _ : Fin (n + 1) => Icc (-1 : ℝ) 1)) ≠ ⊤ :=
    (isCompact_univ_pi (fun _ => isCompact_Icc)).measure_lt_top.ne
  calc (volume {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ}).toReal
      ≤ (volume (Set.pi univ (fun _ : Fin (n + 1) => Icc (-1 : ℝ) 1))).toReal :=
        ENNReal.toReal_mono hfin (measure_mono (shell_subset_pi hσ))
    _ = (2 * 1) ^ (n + 1) := volume_real_cube (n := n + 1) 1 zero_le_one
    _ = 2 ^ (n + 1) := by norm_num

set_option maxHeartbeats 1600000 in
/-- **Cutoff lemma for `H¹`** (inequality (25), `f = 0`). -/
theorem cutoff_H1 (hn : 3 ≤ n) :
    ∃ Cb : ℝ, 0 < Cb ∧ ∀ {ρ σ c h : ℝ}, 1 / 2 ≤ ρ → ρ < σ → σ ≤ 1 → 0 < c →
      ∀ u : H1Function (Metric.ball (0 : Vec (n + 1)) 1), ∀ θ : ℝ, 0 < θ →
      ∃ (K : ℝ) (η : Vec (n + 1) → ℝ), 0 ≤ K ∧ EucLip K η ∧
        (∀ x, η x ∈ Icc (0 : ℝ) 1) ∧ (∀ x, ‖x‖ ≤ ρ → η x = 1) ∧
        (∀ x, (ρ + σ) / 2 ≤ ‖x‖ → η x = 0) ∧
        ∫ x in Metric.ball (0 : Vec (n + 1)) 1,
            (max (u.toFun x - h - c) 0) ^ 2 * vecNormSq (classicalGradient η x) ≤
          shellBound n Cb ρ ((ρ + σ) / 2) c 0
            (4 * ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < (ρ + σ) / 2},
              ((max (u.toFun x - h) 0) ^ 2 +
                vecNormSq ({y | h < u.toFun y}.indicator u.grad x))) + θ := by
  obtain ⟨Cb, hCb, hbs⟩ := smooth_shell_bound hn
  refine ⟨Cb, hCb, ?_⟩
  intro ρ σ c h hρ hρσ hσ hc u θ hθ
  have hρσ' : ρ < (ρ + σ) / 2 := by linarith
  have hσ' : (ρ + σ) / 2 ≤ 1 := by linarith
  obtain ⟨w, hw, hzi, hgi, hw2, hdw2, hdv, hdg, hconv_v, hconv_g⟩ :=
    exists_smooth_approx_cube u h
  -- Abbreviations
  set S : Set (Vec (n + 1)) := {x | ρ < ‖x‖ ∧ ‖x‖ < (ρ + σ) / 2} with hS
  have hSU : S ⊆ (Metric.ball (0 : Vec (n + 1)) 1) := shell_subset_cube hσ'
  have hSm : MeasurableSet S := measurableSet_shell' _ _
  set z : Vec (n + 1) → ℝ := fun x => max (u.toFun x - h) 0 with hz
  set g : Vec (n + 1) → Vec (n + 1) := {y | h < u.toFun y}.indicator u.grad with hg
  have hzi' : IntegrableOn (fun x => z x ^ 2) (Metric.ball (0 : Vec (n + 1)) 1) := hzi
  have hgi' : IntegrableOn (fun x => vecNormSq (g x)) (Metric.ball (0 : Vec (n + 1)) 1) := hgi
  have hdv' : ∀ i, IntegrableOn (fun x => (w i x - z x) ^ 2) (Metric.ball (0 : Vec (n + 1)) 1) := hdv
  have hdg' : ∀ i, IntegrableOn (fun x => vecNormSq (classicalGradient (w i) x - g x)) (Metric.ball (0 : Vec (n + 1)) 1) := hdg
  have hconv_v' : Tendsto (fun i => ∫ x in (Metric.ball (0 : Vec (n + 1)) 1), (w i x - z x) ^ 2) atTop (𝓝 0) := hconv_v
  have hconv_g' : Tendsto (fun i => ∫ x in (Metric.ball (0 : Vec (n + 1)) 1), vecNormSq (classicalGradient (w i) x - g x))
      atTop (𝓝 0) := hconv_g
  -- P0, T0, F
  set P0 : ℝ := ∫ x in S, (z x ^ 2 + vecNormSq (g x)) with hP0
  have hP0nn : 0 ≤ P0 := setIntegral_nonneg hSm (fun x _ => add_nonneg (sq_nonneg _)
    (vecNormSq_nonneg' _))
  set T0 : ℝ := shellBound n Cb ρ ((ρ + σ) / 2) c 0 (4 * P0) with hT0
  set F : ℝ → ℝ := fun t => shellBound n Cb ρ ((ρ + σ) / 2) c t
    (4 * P0 + 2 ^ (n + 3) * t ^ 2 + t) with hF
  have hFc : Continuous F :=
    continuous_shellBound hn Cb ρ ((ρ + σ) / 2) c (e := fun t => t)
      (p := fun t => 4 * P0 + 2 ^ (n + 3) * t ^ 2 + t) continuous_id (by fun_prop)
  have hF0 : F 0 = T0 := by simp [hF, hT0]
  obtain ⟨ε, hε, hFε⟩ : ∃ ε : ℝ, 0 < ε ∧ F ε < T0 + θ / 2 := by
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), F t < T0 + θ / 2 :=
      (hFc.tendsto 0).eventually (gt_mem_nhds (by rw [hF0]; linarith))
    obtain ⟨r, hr, H⟩ := Metric.eventually_nhds_iff.1 hev
    refine ⟨r / 2, by positivity, H ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  set P1 : ℝ := 4 * P0 + 2 ^ (n + 3) * ε ^ 2 + ε with hP1
  set Kb : ℝ := F ε / (ε * (2 * ρ) ^ n) with hKb
  have hρ0 : 0 < ρ := by linarith
  have hθ' : 0 < θ / (2 * (Kb ^ 2 + 1)) := by positivity
  -- Approximation
  have hnn1 : ∀ i, 0 ≤ ∫ x in (Metric.ball (0 : Vec (n + 1)) 1), (w i x - z x) ^ 2 := fun i =>
    setIntegral_nonneg Metric.isOpen_ball.measurableSet (fun x _ => sq_nonneg _)
  have hnn2 : ∀ i, 0 ≤ ∫ x in (Metric.ball (0 : Vec (n + 1)) 1), vecNormSq (classicalGradient (w i) x - g x) := fun i =>
    setIntegral_nonneg Metric.isOpen_ball.measurableSet (fun x _ => vecNormSq_nonneg' _)
  have ev1 : ∀ᶠ i in atTop, ∫ x in (Metric.ball (0 : Vec (n + 1)) 1), (w i x - z x) ^ 2 < ε / 4 :=
    (tendsto_order.1 hconv_v').2 _ (by positivity)
  have ev2 : ∀ᶠ i in atTop, ∫ x in (Metric.ball (0 : Vec (n + 1)) 1), vecNormSq (classicalGradient (w i) x - g x) < ε / 4 :=
    (tendsto_order.1 hconv_g').2 _ (by positivity)
  have hzS : IntegrableOn (fun x => z x ^ 2) S := hzi'.mono_set hSU
  have hdvS : ∀ i, IntegrableOn (fun x => (w i x - z x) ^ 2) S := fun i => (hdv' i).mono_set hSU
  have hcvS : Tendsto (fun i => ∫ x in S, (w i x - z x) ^ 2) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv_v'
      (fun i => setIntegral_nonneg hSm (fun x _ => sq_nonneg _)) (fun i => ?_)
    exact setIntegral_mono_set (hdv' i) (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      (HasSubset.Subset.eventuallyLE hSU)
  have ev3 := eventually_L1_close hc.le hzS hdvS hcvS _ hθ'
  obtain ⟨i, hi1, hi2, hi3⟩ := (ev1.and (ev2.and ev3)).exists
  -- smooth shell estimate for w i
  obtain ⟨K, η, hK0, hK1, hη, hη01, hη1, hη0, g', hg'ge, hg'int, hg'bound⟩ :=
    hbs hρ hρσ' hσ' hc hε (w i) (hw i)
  -- bound for P_i
  set Pi : ℝ := ∫ x in S, ((|w i x| + ε) ^ 2 + vecNormSq (classicalGradient (w i) x)) with hPi
  have hPi0 : 0 ≤ Pi := setIntegral_nonneg hSm (fun x _ => add_nonneg (sq_nonneg _)
    (vecNormSq_nonneg' _))
  have hI1 : IntegrableOn (fun x => z x ^ 2 + vecNormSq (g x)) S :=
    (hzi'.add hgi').mono_set hSU
  have hI2 : IntegrableOn (fun _ : Vec (n + 1) => 4 * ε ^ 2) S :=
    integrableOn_const (volume_shell_ne_top hσ')
  have hI3 : IntegrableOn (fun x => (w i x - z x) ^ 2) S := hdvS i
  have hI4 : IntegrableOn (fun x => vecNormSq (classicalGradient (w i) x - g x)) S :=
    (hdg' i).mono_set hSU
  have hpt : ∀ x, ((|w i x| + ε) ^ 2 + vecNormSq (classicalGradient (w i) x)) ≤
      4 * (z x ^ 2 + vecNormSq (g x)) + 4 * ε ^ 2 + 2 * (w i x - z x) ^ 2 +
        2 * vecNormSq (classicalGradient (w i) x - g x) := by
    intro x
    have h1 : (|w i x| + ε) ^ 2 ≤ 4 * z x ^ 2 + 4 * ε ^ 2 + 2 * (w i x - z x) ^ 2 := by
      have hz0 : |w i x| ≤ |z x| + |w i x - z x| := by
        have := abs_add_le (z x) (w i x - z x)
        simpa using this
      have hle : (|w i x| + ε) ^ 2 ≤ ((|z x| + ε) + |w i x - z x|) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      have h2 := amgm_sq (|z x| + ε) (|w i x - z x|) 1 one_pos
      have e1 : (|z x| + ε) ^ 2 ≤ 2 * z x ^ 2 + 2 * ε ^ 2 := by
        nlinarith [sq_abs (z x), sq_nonneg (|z x| - ε)]
      have e2 : |w i x - z x| ^ 2 = (w i x - z x) ^ 2 := sq_abs _
      nlinarith
    have h2 := amgm_vec (classicalGradient (w i) x) (g x) 1 one_pos
    have h3 := vecNormSq_nonneg' (g x)
    linarith
  have hA : IntegrableOn (fun x => 4 * (z x ^ 2 + vecNormSq (g x))) S := hI1.const_mul 4
  have hB : IntegrableOn (fun x => 4 * (z x ^ 2 + vecNormSq (g x)) + 4 * ε ^ 2) S := hA.add hI2
  have hC : IntegrableOn (fun x => 4 * (z x ^ 2 + vecNormSq (g x)) + 4 * ε ^ 2 +
      2 * (w i x - z x) ^ 2) S := hB.add (hI3.const_mul 2)
  have hR := hC.add (hI4.const_mul 2)
  have hPiInt : IntegrableOn (fun x => (|w i x| + ε) ^ 2 +
      vecNormSq (classicalGradient (w i) x)) S :=
    integrableOn_shell_of_continuous
      (((hw i).continuous.abs.add continuous_const).pow 2 |>.add
        (continuous_vecNormSq_grad (hw i))) hσ'
  have hcst : ∫ x in S, (4 * ε ^ 2) = 4 * ε ^ 2 * (volume S).toReal := by
    rw [setIntegral_const]
    simp only [Measure.real, smul_eq_mul]
    ring
  have hsum : ∫ x in S, (4 * (z x ^ 2 + vecNormSq (g x)) + 4 * ε ^ 2 +
      2 * (w i x - z x) ^ 2 + 2 * vecNormSq (classicalGradient (w i) x - g x)) =
      4 * P0 + 4 * ε ^ 2 * (volume S).toReal +
        2 * (∫ x in S, (w i x - z x) ^ 2) +
        2 * (∫ x in S, vecNormSq (classicalGradient (w i) x - g x)) := by
    have e1 : ∫ x in S, 4 * (z x ^ 2 + vecNormSq (g x)) = 4 * P0 := integral_const_mul _ _
    have e3 : ∫ x in S, 2 * (w i x - z x) ^ 2 = 2 * ∫ x in S, (w i x - z x) ^ 2 :=
      integral_const_mul _ _
    have e4 : ∫ x in S, 2 * vecNormSq (classicalGradient (w i) x - g x) =
        2 * ∫ x in S, vecNormSq (classicalGradient (w i) x - g x) := integral_const_mul _ _
    rw [integral_add hC (hI4.const_mul 2), integral_add hB (hI3.const_mul 2),
      integral_add hA hI2, e1, hcst, e3, e4]
  have hPiR : Pi ≤ 4 * P0 + 4 * ε ^ 2 * (volume S).toReal +
      2 * (∫ x in S, (w i x - z x) ^ 2) +
      2 * (∫ x in S, vecNormSq (classicalGradient (w i) x - g x)) := by
    rw [← hsum]
    exact integral_mono hPiInt hR hpt
  have hIv : ∫ x in S, (w i x - z x) ^ 2 ≤ ε / 4 :=
    (setIntegral_mono_set (hdv' i) (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      (HasSubset.Subset.eventuallyLE hSU)).trans hi1.le
  have hIg : ∫ x in S, vecNormSq (classicalGradient (w i) x - g x) ≤ ε / 4 :=
    (setIntegral_mono_set (hdg' i)
      (Filter.Eventually.of_forall (fun x => vecNormSq_nonneg' _))
      (HasSubset.Subset.eventuallyLE hSU)).trans hi2.le
  have hvolS := volume_shell_le (n := n) (ρ := ρ) hσ'
  have hPiP1 : Pi ≤ P1 := by
    have h4 : 4 * ε ^ 2 * (volume S).toReal ≤ 4 * ε ^ 2 * 2 ^ (n + 1) :=
      mul_le_mul_of_nonneg_left hvolS (by positivity)
    have h8 : (2 : ℝ) ^ (n + 3) = 4 * 2 ^ (n + 1) := by ring
    have hε2 : 0 ≤ ε ^ 2 * 2 ^ (n + 1) := by positivity
    rw [hP1, h8]
    nlinarith
  have hFi : shellBound n Cb ρ ((ρ + σ) / 2) c ε Pi ≤ F ε :=
    shellBound_mono hn hCb.le hρσ'.le hc hε.le hPi0 hPiP1
  have hKle : K ≤ Kb := hK1.trans (div_le_div_of_nonneg_right hFi (by positivity))
  have hK2 : K ^ 2 ≤ Kb ^ 2 := pow_le_pow_left₀ hK0 hKle 2
  have hfin : K ^ 2 * (θ / (2 * (Kb ^ 2 + 1))) ≤ θ / 2 := by
    calc K ^ 2 * (θ / (2 * (Kb ^ 2 + 1))) ≤ Kb ^ 2 * (θ / (2 * (Kb ^ 2 + 1))) :=
          mul_le_mul_of_nonneg_right hK2 hθ'.le
      _ ≤ θ / 2 := by
          rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [sq_nonneg Kb]
  -- Integrability of |A - B|
  have hu : AEStronglyMeasurable u.toFun (volume.restrict S) :=
    (u.memL2.aestronglyMeasurable).mono_measure (Measure.restrict_mono hSU le_rfl)
  have hΦ : Continuous (fun t : ℝ => (max (max (t - h) 0 - c) 0) ^ 2) := by fun_prop
  have hBm : AEStronglyMeasurable (fun x => max (z x - c) 0 ^ 2) (volume.restrict S) :=
    hΦ.comp_aestronglyMeasurable hu
  have hAm : AEStronglyMeasurable (fun x => max (w i x - c) 0 ^ 2) (volume.restrict S) :=
    (by fun_prop : Continuous (fun x => max (w i x - c) 0 ^ 2)) |>.aestronglyMeasurable
  have hABm : AEStronglyMeasurable (fun x => |max (w i x - c) 0 ^ 2 - max (z x - c) 0 ^ 2|)
      (volume.restrict S) :=
    continuous_abs.comp_aestronglyMeasurable (hAm.sub hBm)
  have hAB : IntegrableOn (fun x => |max (w i x - c) 0 ^ 2 - max (z x - c) 0 ^ 2|) S := by
    refine Integrable.mono' (hzS.add (hI3.const_mul 2)) hABm (Filter.Eventually.of_forall
      (fun x => ?_))
    rw [Real.norm_eq_abs, abs_abs]
    exact sqdiff_bound' (w i x) (z x) c hc.le
  have hrhs : IntegrableOn (fun x => g' x * vecNormSq (classicalGradient η x) +
      K ^ 2 * |max (w i x - c) 0 ^ 2 - max (z x - c) 0 ^ 2|) S :=
    hg'int.add (hAB.const_mul _)
  have hpt2 : ∀ x, (max (u.toFun x - h - c) 0) ^ 2 * vecNormSq (classicalGradient η x) ≤
      g' x * vecNormSq (classicalGradient η x) +
        K ^ 2 * |max (w i x - c) 0 ^ 2 - max (z x - c) 0 ^ 2| := by
    intro x
    have hB : max (u.toFun x - h - c) 0 = max (z x - c) 0 := (max_sub_max_eq _ c hc.le).symm
    rw [hB]
    have hD0 : 0 ≤ vecNormSq (classicalGradient η x) := vecNormSq_nonneg' _
    have hDK : vecNormSq (classicalGradient η x) ≤ K ^ 2 := by
      have := pow_le_pow_left₀ (vecEuclideanNorm_nonneg _)
        (hη.vecEuclideanNorm_classicalGradient_le' hK0 x) 2
      rwa [vecEuclideanNorm_sq] at this
    have h1 : max (z x - c) 0 ^ 2 ≤ max (w i x - c) 0 ^ 2 +
        |max (w i x - c) 0 ^ 2 - max (z x - c) 0 ^ 2| := by
      have := le_abs_self (max (z x - c) 0 ^ 2 - max (w i x - c) 0 ^ 2)
      rw [abs_sub_comm] at this
      linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hD0
    have h3 := mul_le_mul_of_nonneg_right (hg'ge x) hD0
    have h4 := mul_le_mul_of_nonneg_left hDK
      (abs_nonneg (max (w i x - c) 0 ^ 2 - max (z x - c) 0 ^ 2))
    nlinarith
  refine ⟨K, η, hK0, hη, hη01, hη1, hη0, ?_⟩
  calc ∫ x in Metric.ball (0 : Vec (n + 1)) 1,
        (max (u.toFun x - h - c) 0) ^ 2 * vecNormSq (classicalGradient η x)
      = ∫ x in S, (max (u.toFun x - h - c) 0) ^ 2 * vecNormSq (classicalGradient η x) :=
        setIntegral_cube_eq_shell hσ' hη1 hη0 (fun x => (max (u.toFun x - h - c) 0) ^ 2)
    _ ≤ ∫ x in S, (g' x * vecNormSq (classicalGradient η x) +
          K ^ 2 * |max (w i x - c) 0 ^ 2 - max (z x - c) 0 ^ 2|) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x =>
          mul_nonneg (sq_nonneg _) (vecNormSq_nonneg' _))) hrhs
          (Filter.Eventually.of_forall hpt2)
    _ = (∫ x in S, g' x * vecNormSq (classicalGradient η x)) +
          K ^ 2 * ∫ x in S, |max (w i x - c) 0 ^ 2 - max (z x - c) 0 ^ 2| := by
        rw [integral_add hg'int (hAB.const_mul _), integral_const_mul]
    _ ≤ shellBound n Cb ρ ((ρ + σ) / 2) c ε Pi + K ^ 2 * (θ / (2 * (Kb ^ 2 + 1))) :=
        add_le_add hg'bound (mul_le_mul_of_nonneg_left hi3 (sq_nonneg K))
    _ ≤ T0 + θ := by linarith
end PDE.BSlocalmax
end
