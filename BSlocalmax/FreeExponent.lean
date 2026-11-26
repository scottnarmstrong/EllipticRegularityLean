module

public import BSlocalmax.HighDim
public import BSlocalmax.ShellSmoothing
public import PDEFoundation.PDE.Ch4.CaccioppoliEnergy

/-!
# The iteration chain with a free exponent q > 2

This file collects the following pieces, in dependency order: SmoothShellQ, CutoffH1Q, Step1Q, Step2AlgQ, Step2Q, Step3Q, IterationExplicit, MainQ.
-/

-- ==== from SmoothShellQ.lean ====
-- Variant of the smooth shell estimate with a free exponent `q > 2` (needed for `d = 3`),
-- the boundary Sobolev inequality being a hypothesis with constant `Cb`.


@[expose] public section

open MeasureTheory Set PDE PDE.Ch4Infra

namespace PDE.BSlocalmax

variable {n : ℕ}

/-- Explicit bound of the smooth shell estimate, free exponent `q` (`δ = 2/q`). -/
noncomputable def shellBoundQ (n : ℕ) (q Cb ρ σ c ε P : ℝ) : ℝ :=
  (σ - ρ) ^ (-(1 + 1 / (2 / q))) *
    (c ^ (-((q - 2) * (2 / q))) * (Cb * P) +
      (σ - ρ) * (ε * (2 * ((n : ℝ) + 1) * 2 ^ n)) ^ (2 / q)) ^ (1 / (2 / q))

/-- Boundary Sobolev inequality, as a hypothesis. -/
def BoundarySob (n : ℕ) (q Cb : ℝ) : Prop :=
  ∀ {ρ σ : ℝ}, 1 / 2 ≤ ρ → ρ < σ → σ ≤ 1 → ∀ u : Vec (n + 1) → ℝ, ContDiff ℝ 1 u →
    ∫ r in Ioo ρ σ, (cubeBoundaryIntegral r (fun x => |u x| ^ q)) ^ (2 / q) ≤
      Cb * ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ},
        (u x ^ 2 + vecNormSq (classicalGradient u x))

/-- **Smooth shell estimate** with free exponent `q`. -/
theorem smooth_shell_boundQ (hn : 1 ≤ n) {q Cb : ℝ} (hq : 2 < q) (hCb : 0 < Cb)
    (hbs : BoundarySob n q Cb) :
    ∀ {ρ σ c ε : ℝ}, 1 / 2 ≤ ρ → ρ < σ → σ ≤ 1 → 0 < c → 0 < ε →
      ∀ w : Vec (n + 1) → ℝ, ContDiff ℝ 1 w →
      ∃ (K : ℝ) (η : Vec (n + 1) → ℝ), 0 ≤ K ∧
        K ≤ shellBoundQ n q Cb ρ σ c ε
              (∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ},
                ((|w x| + ε) ^ 2 + vecNormSq (classicalGradient w x))) /
            (ε * (2 * ρ) ^ n) ∧
        EucLip K η ∧ (∀ x, η x ∈ Icc (0 : ℝ) 1) ∧
        (∀ x, ‖x‖ ≤ ρ → η x = 1) ∧ (∀ x, σ ≤ ‖x‖ → η x = 0) ∧
        ∃ g : Vec (n + 1) → ℝ, (∀ x, (max (w x - c) 0) ^ 2 ≤ g x) ∧
          IntegrableOn (fun x => g x * vecNormSq (classicalGradient η x))
            {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ} ∧
          ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ}, g x * vecNormSq (classicalGradient η x) ≤
            shellBoundQ n q Cb ρ σ c ε
              (∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ},
                ((|w x| + ε) ^ 2 + vecNormSq (classicalGradient w x))) := by
  haveI : NeZero n := ⟨by omega⟩
  intro ρ σ c ε hρ hρσ hσ hc hε w hw
  have hq2 : 2 < q := hq
  have hδ : 0 < (2 / q) := div_pos two_pos (by linarith)
  have hδ1 : (2 / q) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hρ0 : 0 < ρ := by linarith
  have hL : 0 < σ - ρ := sub_pos.2 hρσ
  -- Majorant Ψ = ψ_ε ∘ w
  have hΨ : ContDiff ℝ 1 (fun x => psiEps ε (w x)) := (contDiff_psiEps hε).comp hw
  have hΨ0 : ∀ x, 0 ≤ psiEps ε (w x) := fun x => psiEps_nonneg ε _ hε
  have hFc : Continuous (fun x : Vec (n + 1) => |psiEps ε (w x)| ^ q) :=
    hΨ.continuous.abs.rpow_const (fun _ => Or.inr (by linarith))
  have hgc : Continuous (fun x : Vec (n + 1) =>
      c ^ (-(q - 2)) * |psiEps ε (w x)| ^ q + ε) :=
    (continuous_const.mul hFc).add continuous_const
  have hgm : ∀ x, ε ≤ c ^ (-(q - 2)) * |psiEps ε (w x)| ^ q + ε := fun x => by
    have : 0 ≤ c ^ (-(q - 2)) * |psiEps ε (w x)| ^ q :=
      mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg (abs_nonneg _) _)
    linarith
  obtain ⟨hGc, hGge⟩ := boundaryIntegral_hyps hgc hε hgm (σ := σ) hρ0
  have hm : 0 < ε * (2 * ρ) ^ n := by positivity
  obtain ⟨K, η, hK0, hKle, hη, hη01, hη1, hη0, hint, hbound⟩ :=
    exists_cutoff_cubeShell (δ := (2 / q)) (m := ε * (2 * ρ) ^ n) hρ0 hρσ hδ hm hgc hGc
      (fun r hr => hGge r hr)
  -- Bound for ∫ G^δ
  set P : ℝ := ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ},
      ((|w x| + ε) ^ 2 + vecNormSq (classicalGradient w x)) with hP
  have hS : ∫ r in Ioo ρ σ, (cubeBoundaryIntegral r
      (fun x => c ^ (-(q - 2)) * |psiEps ε (w x)| ^ q + ε)) ^ (2 / q) ≤
      c ^ (-((q - 2) * (2 / q))) * (Cb * P) +
        (σ - ρ) * (ε * (2 * ((n : ℝ) + 1) * 2 ^ n)) ^ (2 / q) := by
    have hcont : ContinuousOn (fun r => cubeBoundaryIntegral r
        (fun x : Vec (n + 1) => |psiEps ε (w x)| ^ q)) (Icc ρ σ) :=
      (continuousOn_cubeBoundaryIntegral hFc).mono (fun r hr => lt_of_lt_of_le hρ0 hr.1)
    have hI1 : IntegrableOn (fun r => (cubeBoundaryIntegral r
        (fun x => c ^ (-(q - 2)) * |psiEps ε (w x)| ^ q + ε)) ^ (2 / q)) (Ioo ρ σ) :=
      (ContinuousOn.integrableOn_Icc
        (hGc.rpow_const (fun r _ => Or.inr hδ.le))).mono_set Ioo_subset_Icc_self
    have hI2 : IntegrableOn (fun r => (cubeBoundaryIntegral r
        (fun x : Vec (n + 1) => |psiEps ε (w x)| ^ q)) ^ (2 / q)) (Ioo ρ σ) :=
      (ContinuousOn.integrableOn_Icc
        (hcont.rpow_const (fun r _ => Or.inr hδ.le))).mono_set Ioo_subset_Icc_self
    have hpt : ∀ r ∈ Ioo ρ σ, (cubeBoundaryIntegral r
        (fun x => c ^ (-(q - 2)) * |psiEps ε (w x)| ^ q + ε)) ^ (2 / q) ≤
        c ^ (-((q - 2) * (2 / q))) * (cubeBoundaryIntegral r
          (fun x : Vec (n + 1) => |psiEps ε (w x)| ^ q)) ^ (2 / q) +
          (ε * (2 * ((n : ℝ) + 1) * 2 ^ n)) ^ (2 / q) := by
      intro r hr
      have hr0 : 0 ≤ r := (hρ0.trans hr.1).le
      have hB0 : 0 ≤ cubeBoundaryIntegral r
          (fun x : Vec (n + 1) => |psiEps ε (w x)| ^ q) :=
        cubeBoundaryIntegral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) _) r
      have ha : 0 ≤ c ^ (-(q - 2)) := Real.rpow_nonneg hc.le _
      have hlin := cubeBoundaryIntegral_lin hFc hr0 (c ^ (-(q - 2))) ε
      rw [hlin]
      have hE0 : 0 ≤ (2 * ((n : ℝ) + 1)) * ((2 * r) ^ n * ε) := by positivity
      have hE : (2 * ((n : ℝ) + 1)) * ((2 * r) ^ n * ε) ≤ ε * (2 * ((n : ℝ) + 1) * 2 ^ n) := by
        have h2r : (2 * r) ^ n ≤ 2 ^ n :=
          pow_le_pow_left₀ (by positivity) (by linarith [hr.2]) n
        have : (2 * ((n : ℝ) + 1)) * ((2 * r) ^ n * ε) ≤ (2 * ((n : ℝ) + 1)) * (2 ^ n * ε) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2r hε.le) (by positivity)
        linarith [this]
      calc (c ^ (-(q - 2)) * cubeBoundaryIntegral r
              (fun x : Vec (n + 1) => |psiEps ε (w x)| ^ q) +
            (2 * ((n : ℝ) + 1)) * ((2 * r) ^ n * ε)) ^ (2 / q)
          ≤ (c ^ (-(q - 2)) * cubeBoundaryIntegral r
              (fun x : Vec (n + 1) => |psiEps ε (w x)| ^ q)) ^ (2 / q) +
            ((2 * ((n : ℝ) + 1)) * ((2 * r) ^ n * ε)) ^ (2 / q) :=
            Real.rpow_add_le_add_rpow (mul_nonneg ha hB0) hE0 hδ.le hδ1
        _ ≤ c ^ (-((q - 2) * (2 / q))) * (cubeBoundaryIntegral r
              (fun x : Vec (n + 1) => |psiEps ε (w x)| ^ q)) ^ (2 / q) +
            (ε * (2 * ((n : ℝ) + 1) * 2 ^ n)) ^ (2 / q) := by
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
        (fun x : Vec (n + 1) => |psiEps ε (w x)| ^ q)) ^ (2 / q) ≤ Cb * P := by
      refine hsob.trans ?_
      refine mul_le_mul_of_nonneg_left (le_trans (le_of_eq ?_) hshell) hCb.le
      rfl
    calc ∫ r in Ioo ρ σ, (cubeBoundaryIntegral r
          (fun x => c ^ (-(q - 2)) * |psiEps ε (w x)| ^ q + ε)) ^ (2 / q)
        ≤ ∫ r in Ioo ρ σ, (c ^ (-((q - 2) * (2 / q))) * (cubeBoundaryIntegral r
          (fun x : Vec (n + 1) => |psiEps ε (w x)| ^ q)) ^ (2 / q) +
            (ε * (2 * ((n : ℝ) + 1) * 2 ^ n)) ^ (2 / q)) :=
          setIntegral_mono_on hI1 ((hI2.const_mul _).add (integrableOn_const (by simp)))
            measurableSet_Ioo hpt
      _ = c ^ (-((q - 2) * (2 / q))) * (∫ r in Ioo ρ σ, (cubeBoundaryIntegral r
          (fun x : Vec (n + 1) => |psiEps ε (w x)| ^ q)) ^ (2 / q)) +
            (σ - ρ) * (ε * (2 * ((n : ℝ) + 1) * 2 ^ n)) ^ (2 / q) := by
          rw [integral_add (hI2.const_mul _) (integrableOn_const (by simp)), integral_const_mul,
            setIntegral_const, Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal hL.le,
            smul_eq_mul]
      _ ≤ _ := by
          have ha : 0 ≤ c ^ (-((q - 2) * (2 / q))) := Real.rpow_nonneg hc.le _
          linarith [mul_le_mul_of_nonneg_left hBint ha]
  -- Combine
  have hG0 : 0 ≤ ∫ r in Ioo ρ σ, (cubeBoundaryIntegral r
      (fun x => c ^ (-(q - 2)) * |psiEps ε (w x)| ^ q + ε)) ^ (2 / q) :=
    setIntegral_nonneg measurableSet_Ioo (fun r hr => Real.rpow_nonneg
      (cubeBoundaryIntegral_nonneg (fun x => add_nonneg (mul_nonneg (Real.rpow_nonneg hc.le _)
        (Real.rpow_nonneg (abs_nonneg _) _)) hε.le) r) _)
  have hT : (σ - ρ) ^ (-(1 + 1 / (2 / q))) * (∫ r in Ioo ρ σ, (cubeBoundaryIntegral r
      (fun x => c ^ (-(q - 2)) * |psiEps ε (w x)| ^ q + ε)) ^ (2 / q)) ^ (1 / (2 / q)) ≤
      shellBoundQ n q Cb ρ σ c ε P := by
    unfold shellBoundQ
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hG0 hS (by positivity)) (Real.rpow_nonneg hL.le _)
  have hK1 : K ≤ shellBoundQ n q Cb ρ σ c ε P / (ε * (2 * ρ) ^ n) :=
    hKle.trans (div_le_div_of_nonneg_right hT hm.le)
  refine ⟨K, η, hK0, hK1, hη, hη01, hη1, hη0,
    fun x => c ^ (-(q - 2)) * |psiEps ε (w x)| ^ q + ε, fun x => ?_, hint,
    hbound.trans hT⟩
  have := sq_pos_le_aux (c := c) (q := q) (t := w x) (P := psiEps ε (w x)) hc hq2.le
    (psiEps_ge ε _ hε)
  linarith

end PDE.BSlocalmax
end

-- ==== from CutoffH1Q.lean ====
-- Cutoff lemma for `H¹` with free exponent `q > 2`.


@[expose] public section

open MeasureTheory Set Filter PDE PDE.Ch4Infra
open scoped Topology

namespace PDE.BSlocalmax

variable {n : ℕ} {q : ℝ}

lemma shellBoundQ_mono (hq : 2 < q) {Cb ρ σ c ε P P' : ℝ} (hCb : 0 ≤ Cb) (hρσ : ρ ≤ σ)
    (hc : 0 < c) (hε : 0 ≤ ε) (hP : 0 ≤ P) (hPP : P ≤ P') :
    shellBoundQ n q Cb ρ σ c ε P ≤ shellBoundQ n q Cb ρ σ c ε P' := by
  have hδ : 0 < 2 / q := div_pos two_pos (by linarith)
  unfold shellBoundQ
  have h0 : 0 ≤ σ - ρ := by linarith
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg h0 _)
  have hc0 : 0 ≤ c ^ (-((q - 2) * (2 / q))) := Real.rpow_nonneg hc.le _
  have hT : 0 ≤ (σ - ρ) * (ε * (2 * ((n : ℝ) + 1) * 2 ^ n)) ^ (2 / q) :=
    mul_nonneg h0 (Real.rpow_nonneg (by positivity) _)
  have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPP hCb) hc0
  refine Real.rpow_le_rpow (add_nonneg (mul_nonneg hc0 (mul_nonneg hCb hP)) hT) ?_
    (one_div_nonneg.2 hδ.le)
  linarith

lemma continuous_shellBoundQ (hq : 2 < q) (Cb ρ σ c : ℝ) {e p : ℝ → ℝ} (he : Continuous e)
    (hp : Continuous p) :
    Continuous (fun t => shellBoundQ n q Cb ρ σ c (e t) (p t)) := by
  have hδ : 0 < 2 / q := div_pos two_pos (by linarith)
  unfold shellBoundQ
  refine continuous_const.mul
    (Continuous.rpow_const ?_ (fun _ => Or.inr (one_div_nonneg.2 hδ.le)))
  exact (continuous_const.mul (continuous_const.mul hp)).add
    (continuous_const.mul
      (Continuous.rpow_const (he.mul continuous_const) (fun _ => Or.inr hδ.le)))

set_option maxHeartbeats 1600000 in
/-- **Cutoff lemma for `H¹`** (inequality (25), `f = 0`). -/
theorem cutoff_H1Q (hn : 1 ≤ n) {q Cb : ℝ} (hq : 2 < q) (hCb : 0 < Cb)
    (hbs : BoundarySob n q Cb) :
    ∀ {ρ σ c h : ℝ}, 1 / 2 ≤ ρ → ρ < σ → σ ≤ 1 → 0 < c →
      ∀ u : H1Function (Metric.ball (0 : Vec (n + 1)) 1), ∀ θ : ℝ, 0 < θ →
      ∃ (K : ℝ) (η : Vec (n + 1) → ℝ), 0 ≤ K ∧ EucLip K η ∧
        (∀ x, η x ∈ Icc (0 : ℝ) 1) ∧ (∀ x, ‖x‖ ≤ ρ → η x = 1) ∧
        (∀ x, (ρ + σ) / 2 ≤ ‖x‖ → η x = 0) ∧
        ∫ x in Metric.ball (0 : Vec (n + 1)) 1,
            (max (u.toFun x - h - c) 0) ^ 2 * vecNormSq (classicalGradient η x) ≤
          shellBoundQ n q Cb ρ ((ρ + σ) / 2) c 0
            (4 * ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < (ρ + σ) / 2},
              ((max (u.toFun x - h) 0) ^ 2 +
                vecNormSq ({y | h < u.toFun y}.indicator u.grad x))) + θ := by
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
  set T0 : ℝ := shellBoundQ n q Cb ρ ((ρ + σ) / 2) c 0 (4 * P0) with hT0
  set F : ℝ → ℝ := fun t => shellBoundQ n q Cb ρ ((ρ + σ) / 2) c t
    (4 * P0 + 2 ^ (n + 3) * t ^ 2 + t) with hF
  have hFc : Continuous F :=
    continuous_shellBoundQ hq Cb ρ ((ρ + σ) / 2) c (e := fun t => t)
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
    smooth_shell_boundQ hn hq hCb hbs hρ hρσ' hσ' hc hε (w i) (hw i)
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
  have hFi : shellBoundQ n q Cb ρ ((ρ + σ) / 2) c ε Pi ≤ F ε :=
    shellBoundQ_mono hq hCb.le hρσ'.le hc hε.le hPi0 hPiP1
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
    _ ≤ shellBoundQ n q Cb ρ ((ρ + σ) / 2) c ε Pi + K ^ 2 * (θ / (2 * (Kb ^ 2 + 1))) :=
        add_le_add hg'bound (mul_le_mul_of_nonneg_left hi3 (sq_nonneg K))
    _ ≤ T0 + θ := by linarith
end PDE.BSlocalmax
end

-- ==== from Step1Q.lean ====
-- Step 1 (inequality (20)): gradient estimate for (u-k)₊ on the inner cube.


@[expose] public section

open MeasureTheory Set Filter PDE PDE.Ch4Infra

namespace PDE.BSlocalmax

variable {n : ℕ}

set_option maxHeartbeats 1600000 in
/-- **Step 1**: `∫_{Q_ρ} |∇(u-h-c)₊|² ≤ 10 Λ · shellBound(…, 4 ∫_shell ((u-h)₊² + |∇(u-h)₊|²))`. -/
theorem step1_gradient_boundQ (hn : 1 ≤ n) {q Cb : ℝ} (hq : 2 < q) (hCb : 0 < Cb)
    (hbs : BoundarySob n q Cb) :
    ∀ {Λ ρ σ c h : ℝ} {a : CoeffField (n + 1)}, 1 / 2 ≤ ρ → ρ < σ → σ ≤ 1 →
      0 < c →
      (∀ i j, AEMeasurable (fun x => a x i j) (volumeOn (Metric.ball (0 : Vec (n + 1)) 1))) →
      (∀ x ∈ Metric.ball (0 : Vec (n + 1)) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ {u : H1Function (Metric.ball (0 : Vec (n + 1)) 1)},
        IsWeakDivergenceFormSubharmonicOn a (Metric.ball (0 : Vec (n + 1)) 1) u →
        ∫ x in Metric.ball (0 : Vec (n + 1)) ρ,
            vecNormSq ({y | h + c < u.toFun y}.indicator u.grad x) ≤
          10 * Λ * shellBoundQ n q Cb ρ ((ρ + σ) / 2) c 0
            (4 * ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < (ρ + σ) / 2},
              ((max (u.toFun x - h) 0) ^ 2 +
                vecNormSq ({y | h < u.toFun y}.indicator u.grad x))) := by
  intro Λ ρ σ c h a hρ hρσ hσ hc ha hEll u hsub
  have hU : IsOpen (Metric.ball (0 : Vec (n + 1)) 1) := Metric.isOpen_ball
  have hfin : volume (Metric.ball (0 : Vec (n + 1)) 1) ≠ ⊤ :=
    Metric.isBounded_ball.measure_lt_top.ne
  have hΛ : 1 ≤ Λ := (hEll 0 (Metric.mem_ball_self one_pos)).lam_le_Lam
  have hρσ' : ρ < (ρ + σ) / 2 := by linarith
  have hσ' : (ρ + σ) / 2 < 1 := by linarith
  have hρ1 : ρ ≤ 1 := by linarith
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hθ : 0 < ε / (10 * Λ) := by positivity
  obtain ⟨K, η, hK0, hη, hη01, hη1, hη0, hint⟩ := cutoff_H1Q hn hq hCb hbs hρ hρσ hσ hc u _ hθ
  have hM : ∀ x, |η x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (hη01 x).1]; exact (hη01 x).2
  have hηsub : Function.support η ⊆ Metric.closedBall (0 : Vec (n + 1)) ((ρ + σ) / 2) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hc'
    exact hx (hη0 x (le_of_lt (not_le.1 hc')))
  have hηc : HasCompactSupport η :=
    HasCompactSupport.intro (isCompact_closedBall _ _) (fun x hx => by
      by_contra hx0
      exact hx (hηsub hx0))
  have hηU : tsupport η ⊆ Metric.ball (0 : Vec (n + 1)) 1 := by
    refine (closure_minimal hηsub Metric.isClosed_closedBall).trans ?_
    exact Metric.closedBall_subset_ball hσ'
  set k : ℝ := h + c with hk
  have hcacc := caccioppoli_energy_positivePart_ten_open hU hfin ha hEll hsub k hη hK0 hM hηc hηU
  -- Integrability of the energy density
  have hηcont : Continuous η := hη.continuous hK0
  have hwL2 : MemL2On (Metric.ball (0 : Vec (n + 1)) 1) (fun x => max (u.toFun x - k) 0) :=
    memL2On_positivePart_of_finite u hfin k
  have hξL2 : MemVectorL2On (Metric.ball (0 : Vec (n + 1)) 1)
      (fun x => {y | k < u.toFun y}.indicator u.grad x) := posPartGrad_gradMemL2 u k
  have hA : MemVectorL2On (Metric.ball (0 : Vec (n + 1)) 1)
      (fun x => η x • {y | k < u.toFun y}.indicator u.grad x) := fun i => by
    simpa only [Pi.smul_apply, smul_eq_mul] using memL2On_mul_bounded (hξL2 i) hηcont hM
  have hB : MemVectorL2On (Metric.ball (0 : Vec (n + 1)) 1)
      (fun x => max (u.toFun x - k) 0 • classicalGradient η x) := fun i => by
    simpa only [Pi.smul_apply, smul_eq_mul, classicalGradient] using
      memL2On_mul_partialDeriv hη hK0 hwL2 i
  have hABsq := integrableOn_vecNormSq_of_memVectorL2On (fun i => (hA i).add (hB i))
  -- inner cube
  have hin : ∫ x in Metric.ball (0 : Vec (n + 1)) ρ,
        vecNormSq ({y | k < u.toFun y}.indicator u.grad x) =
      ∫ x in Metric.ball (0 : Vec (n + 1)) ρ,
        vecNormSq (η x • {y | k < u.toFun y}.indicator u.grad x +
          max (u.toFun x - k) 0 • classicalGradient η x) := by
    refine setIntegral_congr_fun Metric.isOpen_ball.measurableSet (fun x hx => ?_)
    have hxn : ‖x‖ < ρ := by simpa using hx
    have hev : ∀ᶠ y in nhds x, η y = 1 :=
      Filter.mem_of_superset ((isOpen_lt continuous_norm continuous_const).mem_nhds hxn)
        (fun y hy => hη1 y (le_of_lt hy))
    have h0 := classicalGradient_eq_zero_of_eventually hev
    simp only [hη1 x hxn.le, h0, one_smul, smul_zero, add_zero]
  have hmono : ∫ x in Metric.ball (0 : Vec (n + 1)) ρ,
        vecNormSq (η x • {y | k < u.toFun y}.indicator u.grad x +
          max (u.toFun x - k) 0 • classicalGradient η x) ≤
      ∫ x in Metric.ball (0 : Vec (n + 1)) 1,
        vecNormSq (η x • {y | k < u.toFun y}.indicator u.grad x +
          max (u.toFun x - k) 0 • classicalGradient η x) :=
    setIntegral_mono_set hABsq (Filter.Eventually.of_forall (fun x => vecNormSq_nonneg' _))
      (HasSubset.Subset.eventuallyLE (Metric.ball_subset_ball hρ1))
  have hint' : ∫ x in Metric.ball (0 : Vec (n + 1)) 1,
      (max (u.toFun x - k) 0) ^ 2 * vecNormSq (classicalGradient η x) ≤
        shellBoundQ n q Cb ρ ((ρ + σ) / 2) c 0
          (4 * ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < (ρ + σ) / 2},
            ((max (u.toFun x - h) 0) ^ 2 +
              vecNormSq ({y | h < u.toFun y}.indicator u.grad x))) + ε / (10 * Λ) := by
    simpa only [hk, sub_sub] using hint
  calc ∫ x in Metric.ball (0 : Vec (n + 1)) ρ,
        vecNormSq ({y | h + c < u.toFun y}.indicator u.grad x)
      ≤ 10 * Λ * ∫ x in Metric.ball (0 : Vec (n + 1)) 1,
          (max (u.toFun x - k) 0) ^ 2 * vecNormSq (classicalGradient η x) :=
        hin.le.trans (hmono.trans hcacc)
    _ ≤ 10 * Λ * (shellBoundQ n q Cb ρ ((ρ + σ) / 2) c 0
          (4 * ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < (ρ + σ) / 2},
            ((max (u.toFun x - h) 0) ^ 2 +
              vecNormSq ({y | h < u.toFun y}.indicator u.grad x))) + ε / (10 * Λ)) :=
        mul_le_mul_of_nonneg_left hint' (by positivity)
    _ = _ := by
        field_simp

end PDE.BSlocalmax
end

-- ==== from Step2AlgQ.lean ====
-- Step 2, algebraic part with free exponent `q`: `shellBoundQ` at `ε = 0`.


@[expose] public section

namespace PDE.BSlocalmax

variable {n : ℕ}

/-- `shellBoundQ` at `ε = 0`. -/
theorem shellBoundQ_zero {q : ℝ} (hq : 2 < q) {Cb ρ σ c P : ℝ} (hρσ : ρ < σ) (hc : 0 < c)
    (hCb : 0 ≤ Cb) (hP : 0 ≤ P) :
    shellBoundQ n q Cb ρ σ c 0 P =
      (σ - ρ) ^ (-(1 + q / 2)) * (c ^ (-(q - 2)) * (Cb * P) ^ (q / 2)) := by
  have hδ : 0 < 2 / q := div_pos two_pos (by linarith)
  have hq0 : 0 < q := by linarith
  have hσρ : 0 < σ - ρ := sub_pos.2 hρσ
  have h1 : 1 / (2 / q) = q / 2 := by field_simp
  unfold shellBoundQ
  rw [zero_mul, Real.zero_rpow hδ.ne', mul_zero, add_zero, h1,
    Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hc.le]
  have e1 : -((q - 2) * (2 / q)) * (q / 2) = -(q - 2) := by
    field_simp
  rw [e1]

end PDE.BSlocalmax
end

-- ==== from Step2Q.lean ====
-- Step 2 with free exponent `q > 2`: improvement inequality (26) for the energy.


@[expose] public section

open MeasureTheory Set PDE PDE.Ch4Infra

namespace PDE.BSlocalmax

variable {n : ℕ}

/-- Pure algebra of the constants. -/
lemma G_const_algQ {q Λ Cb ρ σ c E : ℝ} (hρσ : ρ < σ) (hCb : 0 ≤ Cb) (hE : 0 ≤ E) :
    10 * Λ * (((ρ + σ) / 2 - ρ) ^ (-(1 + q / 2)) *
      (c ^ (-(q - 2)) * (Cb * (4 * E)) ^ (q / 2))) =
    Λ * (10 * 2 ^ (1 + q / 2) * (4 * Cb) ^ (q / 2)) * (σ - ρ) ^ (-(1 + q / 2)) *
      c ^ (-(q - 2)) * E ^ (q / 2) := by
  have hσρ : 0 < σ - ρ := sub_pos.2 hρσ
  have e1 : (ρ + σ) / 2 - ρ = (σ - ρ) / 2 := by ring
  have e2 : Cb * (4 * E) = (4 * Cb) * E := by ring
  have e3 : ((σ - ρ) / 2) ^ (-(1 + q / 2)) =
      2 ^ (1 + q / 2) * (σ - ρ) ^ (-(1 + q / 2)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_neg hσρ.le, Real.div_rpow hσρ.le (by norm_num)]
    field_simp
  rw [e1, e2, e3, Real.mul_rpow (by positivity) hE]
  ring

set_option maxHeartbeats 1600000 in
/-- **Step 2**: improvement (26) in energy form. -/
theorem step2_EQ (hn : 2 ≤ n) :
    ∃ C2 : ℝ, 0 < C2 ∧ ∀ {q Cb : ℝ}, 2 < q → 0 < Cb → BoundarySob n q Cb →
      ∀ {Λ ρ σ h k : ℝ} {a : CoeffField (n + 1)}, 1 / 2 ≤ ρ → ρ < σ → σ ≤ 1 →
      h < k →
      (∀ i j, AEMeasurable (fun x => a x i j) (volumeOn (Metric.ball (0 : Vec (n + 1)) 1))) →
      (∀ x ∈ Metric.ball (0 : Vec (n + 1)) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ {u : H1Function (Metric.ball (0 : Vec (n + 1)) 1)},
        IsWeakDivergenceFormSubharmonicOn a (Metric.ball (0 : Vec (n + 1)) 1) u →
        Eng u k ρ ≤
          (1 + C2 ^ 2) * (10 * 2 ^ (1 + q / 2) * (4 * Cb) ^ (q / 2)) * Λ * (σ - ρ) ^ (-(1 + q / 2)) * (k - h) ^ (-(q - 2)) *
              Eng u h σ ^ (q / 2) +
            4 * Eng u h σ ^ (1 + 2 / ((n : ℝ) + 1)) * (k - h) ^ (-(4 / ((n : ℝ) + 1))) := by
  obtain ⟨C2, hC2, hL⟩ := l2_control (d := n + 1) (by omega)
  refine ⟨C2, hC2, ?_⟩
  intro q Cb hq hCb hbs Λ ρ σ h k a hρ hρσ hσ hhk ha hEll u hsub
  have hΛ : 1 ≤ Λ := (hEll 0 (Metric.mem_ball_self one_pos)).lam_le_Lam
  have hc : 0 < k - h := sub_pos.2 hhk
  have hρ1 : ρ ≤ 1 := by linarith
  have hρσ' : (ρ + σ) / 2 ≤ σ := by linarith
  have hd : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  -- Abbreviations
  set Eh : ℝ := Eng u h σ with hEh
  set V : ℝ := ∫ x in Metric.ball (0 : Vec (n + 1)) ρ, (max (u.toFun x - k) 0) ^ 2 with hV
  set G : ℝ := ∫ x in Metric.ball (0 : Vec (n + 1)) ρ,
    vecNormSq ({y | k < u.toFun y}.indicator u.grad x) with hG
  set M : ℝ := ∫ x in Metric.ball (0 : Vec (n + 1)) ρ, (max (u.toFun x - h) 0) ^ 2 with hM
  have hfin : volume (Metric.ball (0 : Vec (n + 1)) 1) ≠ ⊤ := Metric.isBounded_ball.measure_lt_top.ne
  have hsqI : ∀ s : ℝ, IntegrableOn (fun x => (max (u.toFun x - s) 0) ^ 2)
      (Metric.ball (0 : Vec (n + 1)) ρ) := fun s => by
    have hL2 := memL2On_positivePart_of_finite u hfin s
    have : IntegrableOn (fun x => (max (u.toFun x - s) 0) ^ 2) (Metric.ball (0 : Vec (n + 1)) 1) := by
      simpa only [pow_two] using integrableOn_mul_of_memL2On hL2 hL2
    exact this.mono_set (Metric.ball_subset_ball hρ1)
  have hξI : ∀ s : ℝ, IntegrableOn (fun x => vecNormSq ({y | s < u.toFun y}.indicator u.grad x))
      (Metric.ball (0 : Vec (n + 1)) ρ) := fun s => by
    have hξ : MemVectorL2On (Metric.ball (0 : Vec (n + 1)) 1)
        (fun x => {y | s < u.toFun y}.indicator u.grad x) := posPartGrad_gradMemL2 u s
    exact (integrableOn_vecNormSq_of_memVectorL2On hξ).mono_set (Metric.ball_subset_ball hρ1)
  have hV0 : 0 ≤ V := integral_nonneg fun x => sq_nonneg _
  have hG0 : 0 ≤ G := integral_nonneg fun x => vecNormSq_nonneg' _
  have hM0 : 0 ≤ M := integral_nonneg fun x => sq_nonneg _
  have hEk : Eng u k ρ = V + G := integral_add (hsqI k) (hξI k)
  -- V ≤ M
  have hVM : V ≤ M := integral_mono (hsqI k) (hsqI h) (fun x => by
    have h1 : max (u.toFun x - k) 0 ≤ max (u.toFun x - h) 0 :=
      max_le_max (by linarith) le_rfl
    exact pow_le_pow_left₀ (le_max_right _ _) h1 2)
  -- M ≤ Eh
  have hEh0 : 0 ≤ Eh := integral_nonneg fun x => eng_integrand_nonneg u h x
  have hMEh : M ≤ Eh := by
    have h1 : M ≤ ∫ x in Metric.ball (0 : Vec (n + 1)) ρ, ((max (u.toFun x - h) 0) ^ 2 +
        vecNormSq ({y | h < u.toFun y}.indicator u.grad x)) :=
      integral_mono (hsqI h) (eng_integrand_integrable u h hρ1)
        (fun x => le_add_of_nonneg_right (vecNormSq_nonneg' _))
    refine h1.trans ?_
    exact setIntegral_mono_set (eng_integrand_integrable u h hσ)
      (Filter.Eventually.of_forall (eng_integrand_nonneg u h))
      (HasSubset.Subset.eventuallyLE (Metric.ball_subset_ball hρσ.le))
  -- shell integral ≤ Eh
  have hI : ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < (ρ + σ) / 2},
      ((max (u.toFun x - h) 0) ^ 2 + vecNormSq ({y | h < u.toFun y}.indicator u.grad x)) ≤ Eh := by
    refine setIntegral_mono_set (eng_integrand_integrable u h hσ)
      (Filter.Eventually.of_forall (eng_integrand_nonneg u h))
      (HasSubset.Subset.eventuallyLE ?_)
    intro x hx
    rw [Metric.mem_ball, dist_zero_right]
    linarith [hx.2]
  have hI0 : 0 ≤ ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < (ρ + σ) / 2},
      ((max (u.toFun x - h) 0) ^ 2 + vecNormSq ({y | h < u.toFun y}.indicator u.grad x)) :=
    integral_nonneg fun x => eng_integrand_nonneg u h x
  -- Step 1
  have h1 := step1_gradient_boundQ (by omega) hq hCb hbs (Λ := Λ) (ρ := ρ) (σ := σ) (c := k - h) (h := h) hρ hρσ hσ hc ha hEll hsub
  rw [add_sub_cancel] at h1
  have hGle : G ≤ 10 * Λ * shellBoundQ n q Cb ρ ((ρ + σ) / 2) (k - h) 0 (4 * Eh) := by
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    exact shellBoundQ_mono hq hCb.le (by linarith) hc le_rfl (by positivity) (by linarith)
  rw [shellBoundQ_zero hq (by linarith) hc hCb.le (by positivity), G_const_algQ hρσ hCb.le hEh0] at hGle
  -- L² control
  have hl := hL (r := ρ) (h := h) (k := k) hρ hρ1 hhk u
  -- alg_split
  have hsqrt : ∀ x : ℝ, 0 ≤ x → (x ^ (1 / 2 : ℝ)) ^ 2 = x := fun x hx => by
    rw [← Real.sqrt_eq_rpow]; exact Real.sq_sqrt hx
  have hε0 : 0 ≤ (M / (k - h) ^ 2) ^ (1 / ((n + 1 : ℕ) : ℝ)) :=
    Real.rpow_nonneg (div_nonneg hM0 (by positivity)) _
  have hal := alg_split (s := V ^ (1 / 2 : ℝ)) (t := G ^ (1 / 2 : ℝ))
    (M := M) (ε := (M / (k - h) ^ 2) ^ (1 / ((n + 1 : ℕ) : ℝ))) (C := C2)
    (Real.rpow_nonneg hV0 _) (Real.rpow_nonneg hG0 _) hε0 hC2.le
    (by rw [hsqrt V hV0]; exact hVM) hl
  rw [hsqrt V hV0, hsqrt G hG0] at hal
  -- ε²·M ≤ Eh^(1+2/d) c^(-4/d)
  have hε2M : 4 * ((M / (k - h) ^ 2) ^ (1 / ((n + 1 : ℕ) : ℝ))) ^ 2 * M ≤
      4 * Eh ^ (1 + 2 / ((n : ℝ) + 1)) * (k - h) ^ (-(4 / ((n : ℝ) + 1))) := by
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hc2 : 0 < (k - h) ^ 2 := by positivity
    have e1 : ((M / (k - h) ^ 2) ^ (1 / ((n : ℝ) + 1))) ^ 2 = (M / (k - h) ^ 2) ^ (2 / ((n : ℝ) + 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hM0 hc2.le)]
      congr 1; push_cast; ring
    have e2 : (M / (k - h) ^ 2) ^ (2 / ((n : ℝ) + 1)) ≤ (Eh / (k - h) ^ 2) ^ (2 / ((n : ℝ) + 1)) :=
      Real.rpow_le_rpow (div_nonneg hM0 hc2.le) (div_le_div_of_nonneg_right hMEh hc2.le) (by positivity)
    have e3 : (Eh / (k - h) ^ 2) ^ (2 / ((n : ℝ) + 1)) * Eh =
        Eh ^ (1 + 2 / ((n : ℝ) + 1)) * (k - h) ^ (-(4 / ((n : ℝ) + 1))) := by
      rw [Real.div_rpow hEh0 hc2.le, ← Real.rpow_natCast (k - h) 2, ← Real.rpow_mul hc.le,
        Real.rpow_neg hc.le, Real.rpow_add' hEh0 (by positivity), Real.rpow_one]
      have : ((2 : ℕ) : ℝ) * (2 / ((n : ℝ) + 1)) = 4 / ((n : ℝ) + 1) := by push_cast; ring
      rw [this]
      field_simp
    rw [e1]
    calc 4 * (M / (k - h) ^ 2) ^ (2 / ((n : ℝ) + 1)) * M
        ≤ 4 * (Eh / (k - h) ^ 2) ^ (2 / ((n : ℝ) + 1)) * Eh := by
          have := mul_le_mul e2 hMEh hM0 (Real.rpow_nonneg (div_nonneg hEh0 hc2.le) _)
          linarith
      _ = _ := by rw [mul_assoc, e3]; ring
  -- Assembly
  have hGnn : 0 ≤ G := hG0
  calc Eng u k ρ = V + G := hEk
    _ ≤ (1 + C2 ^ 2) * G + 4 * ((M / (k - h) ^ 2) ^ (1 / ((n + 1 : ℕ) : ℝ))) ^ 2 * M := by
        nlinarith [sq_nonneg C2]
    _ ≤ (1 + C2 ^ 2) * (Λ * (10 * 2 ^ (1 + q / 2) * (4 * Cb) ^ (q / 2)) *
          (σ - ρ) ^ (-(1 + q / 2)) * (k - h) ^ (-(q - 2)) * Eh ^ (q / 2)) +
        4 * Eh ^ (1 + 2 / ((n : ℝ) + 1)) * (k - h) ^ (-(4 / ((n : ℝ) + 1))) := by
        have := mul_le_mul_of_nonneg_left hGle (by positivity : (0 : ℝ) ≤ 1 + C2 ^ 2)
        linarith
    _ = _ := by ring

end PDE.BSlocalmax
end

-- ==== from Step3Q.lean ====
-- Verification of `IterHyp` for the rescaled energy, free exponent `q > 2`.


@[expose] public section

open MeasureTheory Set PDE PDE.Ch4Infra

namespace PDE.BSlocalmax

variable {n : ℕ}

set_option maxHeartbeats 1600000 in
theorem iterHyp_FnQ (hn : 2 ≤ n) :
    ∃ C2 : ℝ, 0 < C2 ∧ ∀ {q Cb : ℝ}, 2 < q → 0 < Cb → BoundarySob n q Cb →
      ∀ {Λ : ℝ} {a : CoeffField (n + 1)},
      (∀ i j, AEMeasurable (fun x => a x i j) (volumeOn (Metric.ball (0 : Vec (n + 1)) 1))) →
      (∀ x ∈ Metric.ball (0 : Vec (n + 1)) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ {u : H1Function (Metric.ball (0 : Vec (n + 1)) 1)},
        IsWeakDivergenceFormSubharmonicOn a (Metric.ball (0 : Vec (n + 1)) 1) u →
        IterHyp (q / 2) (2 / ((n : ℝ) + 1)) ((1 + q / 2) / 2)
          (Real.sqrt (((1 + C2 ^ 2) * (10 * 2 ^ (1 + q / 2) * (4 * Cb) ^ (q / 2))) * Λ) * 2 ^ ((1 + q / 2) / 2)) 2 (Fn u) := by
  obtain ⟨C2, hC2, hS⟩ := step2_EQ hn
  refine ⟨C2, hC2, ?_⟩
  intro q Cb hq hCb hbs Λ a ha hEll u hsub
  have hAp : 0 < ((1 + C2 ^ 2) * (10 * 2 ^ (1 + q / 2) * (4 * Cb) ^ (q / 2))) := by positivity
  refine ⟨fun k r => Real.sqrt_nonneg _, ?_, ?_⟩
  · intro k k' r r' hk hr
    unfold Fn
    have hs' := clamp_le r'
    have hs := clamp_le r
    have hle : max 0 (min r' 1) ≤ max 0 (min r 1) := max_le_max le_rfl (min_le_min hr le_rfl)
    refine Real.sqrt_le_sqrt ((eng_anti_k u hk (by linarith)).trans
      (eng_mono_r u k (by linarith) (by linarith)))
  · intro h k ρ σ hhk hρ hρσ hσ
    have hΛ : 1 ≤ Λ := (hEll 0 (Metric.mem_ball_self one_pos)).lam_le_Lam
    have hcl : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → max 0 (min r 1) = r := fun r h0 h1 => by
      rw [min_eq_left h1, max_eq_right h0]
    have hρ' : max 0 (min ρ 1) = ρ := hcl ρ (by linarith) (by linarith)
    have hσ' : max 0 (min σ 1) = σ := hcl σ (by linarith) (by linarith)
    unfold Fn
    rw [hρ', hσ']
    have h2 := hS hq hCb hbs (Λ := Λ) (ρ := 1 / 4 + ρ / 2) (σ := 1 / 4 + σ / 2) (h := h) (k := k)
      (by linarith) (by linarith) (by linarith) hhk ha hEll hsub
    have eσ : (1 / 4 + σ / 2) - (1 / 4 + ρ / 2) = (σ - ρ) / 2 := by ring
    have eg : -(2 * (q / 2) - 2) = -(q - 2) := by ring
    have eθ : -(2 * (2 / ((n : ℝ) + 1))) = -(4 / ((n : ℝ) + 1)) := by ring
    rw [eσ] at h2
    have hAΛ : 0 ≤ ((1 + C2 ^ 2) * (10 * 2 ^ (1 + q / 2) * (4 * Cb) ^ (q / 2))) * Λ := by positivity
    have := sqrt_step (B := ((1 + C2 ^ 2) * (10 * 2 ^ (1 + q / 2) * (4 * Cb) ^ (q / 2))) * Λ) (s := σ - ρ) (c := k - h) (X := Eng u k (1 / 4 + ρ / 2))
      (Y := Eng u h (1 / 4 + σ / 2)) (g := q / 2) (θ := 2 / ((n : ℝ) + 1)) hAΛ
      (by linarith) (sub_pos.2 hhk) (eng_nonneg u _ _) (eng_nonneg u _ _)
      (by rw [eg, eθ]; exact h2)
    have e1 : q / 2 - 1 = (q / 2) - 1 := rfl
    convert this using 3

end PDE.BSlocalmax
end

-- ==== from IterationExplicit.lean ====
@[expose] public section

namespace PDE.BSlocalmax

/-- The explicit iteration constant. -/
noncomputable def iterConst (γ θ α b : ℝ) : ℝ :=
  2 * max ((2 / (1 / (2 * (2 : ℝ) ^ (α / (γ - 1))))) ^ (1 / (γ - 1)) * ((2 : ℝ) ^ (α / (γ - 1))) ^ 2)
    ((2 * b / (1 / (2 * (2 : ℝ) ^ (α / (γ - 1))))) ^ (1 / θ)) + 1

/-- **Iteration lemma** (Step 3, `f = 0`) with explicit constant `iterConst γ θ α b`. -/
theorem iteration_limit_explicit {γ θ α b : ℝ} (hγ : 1 < γ) (hθ : 0 < θ) (hα : 0 ≤ α)
    (hb : 0 < b) :
    0 < iterConst γ θ α b ∧ ∀ a : ℝ, 0 < a → ∀ F : ℝ → ℝ → ℝ, IterHyp γ θ α a b F →
      ∀ k₀ : ℝ, F (k₀ + iterConst γ θ α b * (1 + a ^ (1 / (γ - 1))) * F k₀ 1) (1 / 2) = 0 := by
  have hr : 0 < γ - 1 := sub_pos.mpr hγ
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (2 : ℝ) ^ (α / (γ - 1)) := ⟨_, rfl⟩
  have hρ1 : 1 ≤ ρ := by rw [hρ]; exact one_le_rho hγ hα
  have hρ0 : 0 < ρ := by linarith
  have hρne : ρ ≠ 0 := hρ0.ne'
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = 1 / (2 * ρ) := ⟨_, rfl⟩
  have hτ0 : 0 < τ := by rw [hτ]; positivity
  have hτne : τ ≠ 0 := hτ0.ne'
  have hτ1 : τ ≤ 1 / 2 := by
    rw [hτ, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hτρ : τ * ρ = 1 / 2 := by rw [hτ]; field_simp
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ, K1 = (2 / τ) ^ (1 / (γ - 1)) * ρ ^ 2 := ⟨_, rfl⟩
  obtain ⟨K3, hK3⟩ : ∃ K3 : ℝ, K3 = (2 * b / τ) ^ (1 / θ) := ⟨_, rfl⟩
  have hK1pos : 0 < K1 := by rw [hK1]; positivity
  have hK3pos : 0 < K3 := by rw [hK3]; positivity
  have hm : 0 ≤ max K1 K3 := le_max_of_le_left hK1pos.le
  have hc : iterConst γ θ α b = 2 * max K1 K3 + 1 := by
    rw [iterConst, hK1, hK3, hτ, hρ]
  rw [hc]
  refine ⟨by linarith, ?_⟩
  intro a ha F hF k₀
  obtain ⟨J0, hJ0⟩ : ∃ J0 : ℝ, J0 = F k₀ 1 := ⟨_, rfl⟩
  rw [← hJ0]
  have hJ0nn : 0 ≤ J0 := by rw [hJ0]; exact hF.nonneg _ _
  rcases hJ0nn.eq_or_lt with h0 | hpos
  · -- trivial case `J0 = 0`
    rw [← h0, mul_zero, add_zero]
    have h1 := hF.anti k₀ k₀ 1 (1 / 2) le_rfl (by norm_num)
    have h2 := hF.nonneg k₀ (1 / 2)
    rw [← hJ0, ← h0] at h1
    linarith
  · have hJne : J0 ≠ 0 := hpos.ne'
    obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (2 * a / τ) ^ (1 / (γ - 1)) * ρ ^ 2 * J0 := ⟨_, rfl⟩
    obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = K3 * J0 := ⟨_, rfl⟩
    have hP0 : 0 < P := by rw [hP]; positivity
    have hQ0 : 0 < Q := by rw [hQ]; positivity
    obtain ⟨S, hS⟩ : ∃ S : ℕ → ℝ, ∀ i, S i =
        ∑ j ∈ Finset.range i, (P * (1 / 2 : ℝ) ^ j + Q * τ ^ j) := ⟨fun i => _, fun i => rfl⟩
    have hS0 : S 0 = 0 := by rw [hS, Finset.sum_range_zero]
    have hSsucc : ∀ i, S (i + 1) = S i + (P * (1 / 2 : ℝ) ^ i + Q * τ ^ i) := by
      intro i; rw [hS, hS, Finset.sum_range_succ]
    have hSle : ∀ i, S i ≤ 2 * P + 2 * Q := by
      intro i
      have hs1 := sum_geometric_two_le i
      have hs3 : ∑ j ∈ Finset.range i, τ ^ j ≤ 2 :=
        le_trans (Finset.sum_le_sum fun j _ => pow_le_pow_left₀ hτ0.le hτ1 j) hs1
      rw [hS, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      linarith [mul_le_mul_of_nonneg_left hs1 hP0.le, mul_le_mul_of_nonneg_left hs3 hQ0.le]
    -- the main induction
    have claim : ∀ i : ℕ, F (k₀ + S i) (1 / 2 + (1 / 2 : ℝ) ^ (i + 1)) ≤ τ ^ i * J0 := by
      intro i
      induction i with
      | zero =>
        have e : (1 / 2 : ℝ) + (1 / 2) ^ (0 + 1) = 1 := by norm_num
        rw [hS0, add_zero, pow_zero, one_mul, e]
        exact hJ0.symm.le
      | succ i ih =>
        have hx : 0 < τ ^ i * J0 := by positivity
        obtain ⟨D, hD⟩ : ∃ D : ℝ, D = P * (1 / 2 : ℝ) ^ i + Q * τ ^ i := ⟨_, rfl⟩
        have hDpos : 0 < D := by rw [hD]; positivity
        have hFi0 := hF.nonneg (k₀ + S i) (1 / 2 + (1 / 2 : ℝ) ^ (i + 1))
        have hkh : k₀ + S (i + 1) - (k₀ + S i) = D := by rw [hSsucc, hD]; ring
        have hgap : (1 / 2 + (1 / 2 : ℝ) ^ (i + 1)) - (1 / 2 + (1 / 2 : ℝ) ^ (i + 1 + 1))
            = (1 / 2 : ℝ) ^ (i + 2) := by ring
        have hpos1 : (0 : ℝ) < (1 / 2) ^ (i + 1) := by positivity
        have hstep := hF.step (k₀ + S i) (k₀ + S (i + 1)) (1 / 2 + (1 / 2 : ℝ) ^ (i + 1 + 1))
          (1 / 2 + (1 / 2 : ℝ) ^ (i + 1))
          (by rw [hSsucc]; have : 0 < P * (1 / 2 : ℝ) ^ i + Q * τ ^ i := by positivity
              linarith)
          (by have : (0 : ℝ) ≤ (1 / 2) ^ (i + 1 + 1) := by positivity
              linarith)
          (by rw [pow_succ (1 / 2 : ℝ) (i + 1)]; linarith)
          (by rw [pow_succ (1 / 2 : ℝ) i]
              have := pow_le_one₀ (n := i) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
              linarith)
        rw [hkh, hgap] at hstep
        obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ((1 / 2 : ℝ) ^ (i + 2)) ^ (-α) := ⟨_, rfl⟩
        rw [← hW] at hstep
        have hW0 : 0 < W := by rw [hW]; positivity
        have hWp : W ^ (1 / (γ - 1)) = ρ ^ (i + 2) := by rw [hW, weight_pow, hρ]
        have htpos : 0 < τ ^ (i + 1) * J0 / 2 := by positivity
        have hτi : τ ^ i * ρ ^ (i + 2) = ρ ^ 2 * (1 / 2 : ℝ) ^ i := by
          rw [← hτρ, mul_pow]; ring
        -- first term
        have hcond1 : (τ ^ i * J0) *
            ((a * W) * (τ ^ i * J0) / (τ ^ (i + 1) * J0 / 2)) ^ (1 / (γ - 1)) ≤ D := by
          have e1 : (a * W) * (τ ^ i * J0) / (τ ^ (i + 1) * J0 / 2) = (2 * a / τ) * W := by
            field_simp; ring
          rw [e1, Real.mul_rpow (by positivity) hW0.le, hWp]
          have e2 : (τ ^ i * J0) * ((2 * a / τ) ^ (1 / (γ - 1)) * ρ ^ (i + 2))
              = P * (1 / 2 : ℝ) ^ i := by
            rw [hP]
            linear_combination ((2 * a / τ) ^ (1 / (γ - 1)) * J0) * hτi
          rw [e2, hD]
          have : 0 ≤ Q * τ ^ i := by positivity
          linarith
        have T1 := rpow_term_le hγ (mul_pos ha hW0) hx hDpos htpos hcond1
        -- second term
        have hq : (1 + θ) - 1 = θ := by ring
        have hcond2 : (τ ^ i * J0) *
            (b * (τ ^ i * J0) / (τ ^ (i + 1) * J0 / 2)) ^ (1 / ((1 + θ) - 1)) ≤ D := by
          have e3 : b * (τ ^ i * J0) / (τ ^ (i + 1) * J0 / 2) = 2 * b / τ := by
            field_simp; ring
          rw [e3, hq, ← hK3]
          have e4 : (τ ^ i * J0) * K3 = Q * τ ^ i := by rw [hQ]; ring
          rw [e4, hD]
          have : 0 ≤ P * (1 / 2 : ℝ) ^ i := by positivity
          linarith
        have T2 := rpow_term_le (γ := 1 + θ) (by linarith) hb hx hDpos htpos hcond2
        rw [hq] at T2
        have M1 : a * W * F (k₀ + S i) (1 / 2 + (1 / 2 : ℝ) ^ (i + 1)) ^ γ * D ^ (-(γ - 1))
            ≤ a * W * (τ ^ i * J0) ^ γ * D ^ (-(γ - 1)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hFi0 ih (by linarith))
              (mul_pos ha hW0).le)
            (Real.rpow_nonneg hDpos.le _)
        have M2 : b * F (k₀ + S i) (1 / 2 + (1 / 2 : ℝ) ^ (i + 1)) ^ (1 + θ) * D ^ (-θ)
            ≤ b * (τ ^ i * J0) ^ (1 + θ) * D ^ (-θ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hFi0 ih (by linarith)) hb.le)
            (Real.rpow_nonneg hDpos.le _)
        calc F (k₀ + S (i + 1)) (1 / 2 + (1 / 2 : ℝ) ^ (i + 1 + 1))
            ≤ _ := hstep
          _ ≤ a * W * (τ ^ i * J0) ^ γ * D ^ (-(γ - 1)) +
              b * (τ ^ i * J0) ^ (1 + θ) * D ^ (-θ) := add_le_add M1 M2
          _ ≤ τ ^ (i + 1) * J0 / 2 + τ ^ (i + 1) * J0 / 2 := add_le_add T1 T2
          _ = τ ^ (i + 1) * J0 := by ring
    -- conclusion
    have hap : 0 ≤ a ^ (1 / (γ - 1)) := Real.rpow_nonneg ha.le _
    have hP' : P = K1 * a ^ (1 / (γ - 1)) * J0 := by
      rw [hP, hK1, show 2 * a / τ = 2 / τ * a by ring,
        Real.mul_rpow (by positivity) ha.le]
      ring
    have hQ' : Q = K3 * J0 := hQ
    have h1 : K1 * a ^ (1 / (γ - 1)) * J0 ≤ max K1 K3 * a ^ (1 / (γ - 1)) * J0 := by
      gcongr
      exact le_max_left _ _
    have h2 : K3 * J0 ≤ max K1 K3 * J0 := by
      gcongr
      exact le_max_right _ _
    have hKb : ∀ i, k₀ + S i ≤
        k₀ + (2 * max K1 K3 + 1) * (1 + a ^ (1 / (γ - 1))) * J0 := by
      intro i
      have := hSle i
      rw [hP', hQ'] at this
      nlinarith [mul_nonneg hap hJ0nn, hJ0nn]
    have hle : ∀ i : ℕ, F (k₀ + (2 * max K1 K3 + 1) * (1 + a ^ (1 / (γ - 1))) * J0) (1 / 2)
        ≤ τ ^ i * J0 := by
      intro i
      refine le_trans (hF.anti (k₀ + S i) _ (1 / 2 + (1 / 2 : ℝ) ^ (i + 1)) (1 / 2)
        (hKb i) ?_) (claim i)
      have : (0 : ℝ) ≤ (1 / 2) ^ (i + 1) := by positivity
      linarith
    have hlim : Filter.Tendsto (fun i : ℕ => τ ^ i * J0) Filter.atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hτ0.le (by linarith)).mul_const J0
    exact le_antisymm (ge_of_tendsto' hlim hle) (hF.nonneg _ _)

end PDE.BSlocalmax
end

-- ==== from MainQ.lean ====
/-!
# Sharp local maximum principle on cubes: general exponent `q` (used for `d = 3`)

For every `q > 2` and `Cb` such that the boundary Sobolev inequality `BoundarySob n q Cb` holds,
the sup over `Q_{1/2}` is bounded by `c · C₁ · √C₀ · Λ^{p/2 + 1/2} · ‖u‖_{L²(Q_1)}` with
`p = 1/(q/2-1)`, `c = iterConst`, and `C₁ = 1 + A^{p/2} (2^{(1+q/2)/2})^p`,
`A = (1+C₂²) · 10 · 2^{1+q/2} (4 Cb)^{q/2}`.
-/

@[expose] public section

namespace PDE.BSlocalmax

open MeasureTheory PDE PDE.Ch4Infra

set_option maxHeartbeats 1600000 in
theorem sharpLocalMax_cube_Q (n : ℕ) (hn : 2 ≤ n) :
    ∃ C2 C0 : ℝ, 0 < C2 ∧ 0 < C0 ∧ ∀ {q Cb : ℝ}, 2 < q → 0 < Cb → BoundarySob n q Cb →
    ∀ (Λ : ℝ) (a : CoeffField (n + 1)),
      (∀ i j : Fin (n + 1), AEMeasurable (fun x => a x i j)
        (volumeOn (Metric.ball (0 : Vec (n + 1)) 1))) →
      (∀ x ∈ Metric.ball (0 : Vec (n + 1)) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (Metric.ball (0 : Vec (n + 1)) 1),
      IsWeakDivergenceFormSubharmonicOn a (Metric.ball (0 : Vec (n + 1)) 1) u →
        essSup (fun x => ENNReal.ofReal (u.toFun x))
            (volumeOn (Metric.ball (0 : Vec (n + 1)) (1 / 2))) ≤
          ENNReal.ofReal (iterConst (q / 2) (2 / ((n : ℝ) + 1)) ((1 + q / 2) / 2) 2 *
              (1 + ((1 + C2 ^ 2) * (10 * 2 ^ (1 + q / 2) * (4 * Cb) ^ (q / 2))) ^
                  (1 / (q / 2 - 1) / 2) *
                (2 ^ ((1 + q / 2) / 2)) ^ (1 / (q / 2 - 1)) ) *
              Real.sqrt C0 * Λ ^ (1 / (q / 2 - 1) / 2 + 1 / 2)) *
            eLpNorm u.toFun 2 (volumeOn (Metric.ball (0 : Vec (n + 1)) 1)) := by
  obtain ⟨C2, hC2, hH⟩ := iterHyp_FnQ hn
  obtain ⟨C0, hC0, hI⟩ := initial_energy_gen (n := n)
  refine ⟨C2, C0, hC2, hC0, ?_⟩
  intro q Cb hq hCb hbs
  set A : ℝ := (1 + C2 ^ 2) * (10 * 2 ^ (1 + q / 2) * (4 * Cb) ^ (q / 2)) with hAdef
  have hA : 0 < A := by rw [hAdef]; positivity
  obtain ⟨hc, hIt⟩ := iteration_limit_explicit (γ := q / 2) (θ := 2 / ((n : ℝ) + 1))
    (α := (1 + q / 2) / 2) (b := 2) (by linarith) (by positivity) (by positivity)
    (by norm_num)
  obtain ⟨c, hcdef⟩ : ∃ c, c = iterConst (q / 2) (2 / ((n : ℝ) + 1)) ((1 + q / 2) / 2) 2 :=
    ⟨_, rfl⟩
  rw [← hcdef] at hc hIt
  set p : ℝ := 1 / (q / 2 - 1) with hp
  have hp0 : 0 ≤ p := by rw [hp]; apply div_nonneg zero_le_one; linarith
  set C1 : ℝ := 1 + A ^ (p / 2) * (2 ^ ((1 + q / 2) / 2)) ^ p with hC1
  have hC1pos : 0 < C1 := by positivity
  intro Λ a ha hEll u hsub
  have hΛ : 1 ≤ Λ := (hEll 0 (Metric.mem_ball_self one_pos)).lam_le_Lam
  have hΛ0 : 0 < Λ := by linarith
  have hHyp := hH hq hCb hbs ha hEll hsub
  have haC : 0 < Real.sqrt (A * Λ) * 2 ^ ((1 + q / 2) / 2) := by positivity
  have hres := hIt _ haC (Fn u) hHyp 0
  set K : ℝ := 0 + c * (1 + (Real.sqrt (A * Λ) * 2 ^ ((1 + q / 2) / 2)) ^ p) * Fn u 0 1
    with hK
  have e12 : max 0 (min (1 / 2 : ℝ) 1) = 1 / 2 := by
    rw [min_eq_left (by norm_num), max_eq_right (by norm_num)]
  have e1 : max 0 (min (1 : ℝ) 1) = 1 := by simp
  -- Eng = 0
  have hEng0 : Eng u K (1 / 2) = 0 := by
    unfold Fn at hres
    rw [e12] at hres
    have := (Real.sqrt_eq_zero (eng_nonneg u _ _)).1 hres
    convert this using 2; norm_num
  -- almost everywhere u ≤ K
  have hint : IntegrableOn (fun x => (max (u.toFun x - K) 0) ^ 2 +
      vecNormSq ({y | K < u.toFun y}.indicator u.grad x)) (Metric.ball (0 : Vec (n + 1)) (1 / 2)) :=
    eng_integrand_integrable u K (by norm_num)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => eng_integrand_nonneg u K x) hint).1 hEng0
  have hess : essSup (fun x => ENNReal.ofReal (u.toFun x))
      (volumeOn (Metric.ball (0 : Vec (n + 1)) (1 / 2))) ≤ ENNReal.ofReal K := by
    refine essSup_le_of_ae_le _ ?_
    filter_upwards [hae] with x hx
    have hx' : (max (u.toFun x - K) 0) ^ 2 + vecNormSq ({y | K < u.toFun y}.indicator u.grad x) = 0 :=
      hx
    have h1 : (max (u.toFun x - K) 0) ^ 2 = 0 := by
      nlinarith [sq_nonneg (max (u.toFun x - K) 0), vecNormSq_nonneg' ({y | K < u.toFun y}.indicator u.grad x)]
    have h2 : max (u.toFun x - K) 0 = 0 := pow_eq_zero_iff (by norm_num) |>.1 h1
    have h3 : u.toFun x - K ≤ 0 := h2 ▸ le_max_left _ _
    exact ENNReal.ofReal_le_ofReal (by linarith)
  -- Estimate of K
  have hmem : MemLp u.toFun 2 (volumeOn (Metric.ball (0 : Vec (n + 1)) 1)) := u.memL2
  set E0 : ℝ := (eLpNorm u.toFun 2 (volumeOn (Metric.ball (0 : Vec (n + 1)) 1))).toReal with hE0
  have hE0n : 0 ≤ E0 := ENNReal.toReal_nonneg
  have hE0sq : E0 ^ 2 = ∫ x in Metric.ball (0 : Vec (n + 1)) 1, (u.toFun x) ^ 2 :=
    toReal_eLpNorm_two_sq_eq_integral_sq hmem
  have hF0 : Fn u 0 1 ≤ Real.sqrt C0 * Λ ^ (1 / 2 : ℝ) * E0 := by
    unfold Fn
    rw [e1, show ((1 : ℝ) / 4 + 1 / 2) = 3 / 4 by norm_num]
    have hI' := hI ha hEll hsub
    rw [← hE0sq] at hI'
    calc Real.sqrt (Eng u 0 (3 / 4))
        ≤ Real.sqrt (C0 * Λ * E0 ^ 2) := Real.sqrt_le_sqrt hI'
      _ = Real.sqrt C0 * Λ ^ (1 / 2 : ℝ) * E0 := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hC0.le, Real.sqrt_sq hE0n,
            Real.sqrt_eq_rpow Λ]
  have hpΛ : 1 ≤ Λ ^ (p / 2) := Real.one_le_rpow hΛ (by positivity)
  have h1a : 1 + (Real.sqrt (A * Λ) * 2 ^ ((1 + q / 2) / 2)) ^ p ≤ C1 * Λ ^ (p / 2) := by
    rw [Real.mul_rpow (Real.sqrt_nonneg _) (by positivity), rpow_sqrt' (by positivity),
      Real.mul_rpow hA.le hΛ0.le]
    rw [hC1]
    have hX : 0 ≤ A ^ (p / 2) * (2 ^ ((1 + q / 2) / 2)) ^ p := by positivity
    nlinarith [mul_nonneg hX (sub_nonneg.2 hpΛ)]
  have hpow : Λ ^ (p / 2) * Λ ^ (1 / 2 : ℝ) = Λ ^ (p / 2 + 1 / 2) := by
    rw [← Real.rpow_add hΛ0]
  have hKle : K ≤ (c * C1 * Real.sqrt C0) * Λ ^ (p / 2 + 1 / 2) * E0 := by
    have hFn0 : 0 ≤ Fn u 0 1 := Real.sqrt_nonneg _
    calc K = c * (1 + (Real.sqrt (A * Λ) * 2 ^ ((1 + q / 2) / 2)) ^ p) * Fn u 0 1 := by
          rw [hK]; ring
      _ ≤ c * (C1 * Λ ^ (p / 2)) * (Real.sqrt C0 * Λ ^ (1 / 2 : ℝ) * E0) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1a hc.le) hF0 hFn0 (by positivity)
      _ = (c * C1 * Real.sqrt C0) * (Λ ^ (p / 2) * Λ ^ (1 / 2 : ℝ)) * E0 := by ring
      _ = _ := by rw [hpow]
  -- Conclusion
  rw [← hcdef]
  refine hess.trans ?_
  have hfin : eLpNorm u.toFun 2 (volumeOn (Metric.ball (0 : Vec (n + 1)) 1)) ≠ ⊤ :=
    hmem.eLpNorm_ne_top
  calc ENNReal.ofReal K
      ≤ ENNReal.ofReal ((c * C1 * Real.sqrt C0) * Λ ^ (p / 2 + 1 / 2) * E0) :=
        ENNReal.ofReal_le_ofReal hKle
    _ = ENNReal.ofReal ((c * C1 * Real.sqrt C0) * Λ ^ (p / 2 + 1 / 2)) *
          eLpNorm u.toFun 2 (volumeOn (Metric.ball (0 : Vec (n + 1)) 1)) := by
        rw [ENNReal.ofReal_mul (by positivity), hE0, ENNReal.ofReal_toReal hfin]

end PDE.BSlocalmax
end
