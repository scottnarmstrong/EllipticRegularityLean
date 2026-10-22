module

public import EllipticRegularity.Ch4.GreenFunction.D3Upper
public import EllipticRegularity.Ch4.GreenFunction.D3Lower
public import EllipticRegularity.Ch4.GreenFunction.D3Real

/-!
# Two-sided Green function bounds (Proposition 4.42)

On `D_r = B_{3r/2} \ B_{r/4}`, `r ≤ R/2`, the Harnack constant `m` of `G` satisfies
`m ≤ K₁ r^{2-d}` (Stampacchia mean bound) and `exp(C_H √Λ) m ≥ (K₂ Λ)⁻¹ r^{2-d}` (flux versus
Caccioppoli); absorbing the constants with `Λ ≥ 1` gives
`exp(-C √Λ) r^{2-d} ≤ G ≤ exp(C √Λ) r^{2-d}` a.e. on `D_r ⊇ A_r`, and pointwise for the continuous
representative.

`greenD3_full` has, after `(d) (hd)` and the explicit interface hypotheses `hDir`, `hMax`,
exactly the type of the statement `PDE.greenD3`.
-/

@[expose] public section

open scoped Topology ENNReal

namespace PDE.Ch4Green

open MeasureTheory PDE Filter

variable {d : ℕ}

/-- **Bounds on `D_r`.** -/
theorem isGreen_bounds_D (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Λ R : ℝ} {a : CoeffField d} (S : ApproxSetting d Λ R a),
      (∀ n, ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), 0 ≤ (S.G n).toH1Function.toFun x) →
      ∀ {G : Vec d → ℝ}, IsGreenFunction a R G → ∀ {r : ℝ}, 0 < r → r ≤ R / 2 →
      ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) (3 * r / 2) \ euclideanBall (0 : Vec d) (r / 4)),
        Real.exp (-(C * Real.sqrt Λ)) * r ^ (2 - (d : ℝ)) ≤ G x ∧
        G x ≤ Real.exp (C * Real.sqrt Λ) * r ^ (2 - (d : ℝ)) := by
  obtain ⟨CH, hCH, hHarn⟩ := ApproxSetting.isGreen_harnack (d := d) hd
  obtain ⟨C₀, hC₀, hstamp⟩ := stampacchia_approx (d := d) hd
  set b := (volume (euclideanBall (0 : Vec d) 1)).toReal with hbdef
  have hb : 0 < b := volume_euclideanBall_toReal_pos _ one_pos
  set K₁ := C₀ * (b / 2) ^ ((2 - (d : ℝ)) / d) with hK₁
  have hK₁pos : 0 < K₁ := mul_pos hC₀ (Real.rpow_pos_of_pos (by positivity) _)
  set β := (3 / 2 : ℝ) ^ d * b with hβ
  have hβpos : 0 < β := by positivity
  set K₂ := 24 * β with hK₂
  have hK₂pos : 0 < K₂ := by positivity
  refine ⟨CH + 2 + logPlus K₁ + logPlus K₂,
    by linarith [logPlus_nonneg K₁, logPlus_nonneg K₂], ?_⟩
  intro Λ R a S hGnn G hG r hr hrR
  have hR := S.hR
  have hΛ := S.one_le_Lam
  have hΛ0 : 0 < Λ := by linarith
  have hs : 0 ≤ Real.sqrt Λ := Real.sqrt_nonneg _
  obtain ⟨m, hm0, hmae⟩ := hHarn S hGnn hG hr hrR
  set D := euclideanBall (0 : Vec d) (3 * r / 2) \ euclideanBall (0 : Vec d) (r / 4)
  set A := euclideanBall (0 : Vec d) r \ euclideanBall (0 : Vec d) (r / 2)
  have hAD : A ⊆ D := fun x hx =>
    ⟨euclideanBall_mono hr.le (by linarith) hx.1,
      fun h => hx.2 (euclideanBall_mono (by positivity) (by linarith) h)⟩
  have hAB : A ⊆ euclideanBall (0 : Vec d) R := fun x hx =>
    euclideanBall_mono hr.le (by linarith) hx.1
  -- upper bound on `m`
  have hmup : m ≤ K₁ * r ^ (2 - (d : ℝ)) := by
    refine le_of_ae_le_of_stampacchia hd hr hC₀.le hm0
      ((ae_restrict_of_ae_restrict_of_subset hAD hmae).mono fun x hx => hx.1) ?_
    exact S.isGreen_lintegral_le hd hGnn hC₀.le (hstamp S) hG A
      ((measurableSet_euclideanBall _ _).diff (measurableSet_euclideanBall _ _)) hAB
  -- lower bound on `exp(CH √Λ) m`
  set M := Real.exp (CH * Real.sqrt Λ) * m with hM
  have hM0 : 0 ≤ M := by positivity
  have hlow := S.isGreen_lower_aux hd hGnn hG hr hrR (M := M) (hmae.mono fun x hx => hx.2)
  have hV : (volume (euclideanBall (0 : Vec d) (3 * r / 2))).toReal = β * r ^ d := by
    rw [volume_euclideanBall_toReal_eq_unit_mul_of_pos _ (by positivity), ← hbdef, hβ,
      show 3 * r / 2 = (3 / 2) * r by ring, mul_pow]
    ring
  rw [hV] at hlow
  set ρ := r ^ ((d : ℝ) - 2) with hρ
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos hr _
  have hrd : r ^ d = ρ * r ^ 2 := by
    rw [hρ, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add hr]
    congr 1
    ring
  have hsq : 1 ≤ (K₂ * Λ * ρ * M) ^ 2 := by
    have hr4 : r ^ 4 = r ^ 2 * r ^ 2 := by ring
    have : 576 * Λ ^ 2 * (β * r ^ d) ^ 2 / r ^ 4 * M ^ 2 = (K₂ * Λ * ρ * M) ^ 2 := by
      rw [hrd, hK₂, hr4]
      field_simp
      ring
    rwa [this] at hlow
  have hone : 1 ≤ K₂ * Λ * ρ * M := by
    have h0 : 0 ≤ K₂ * Λ * ρ * M := by positivity
    by_contra h
    push Not at h
    have := pow_lt_one₀ h0 h two_ne_zero
    linarith
  have hMlow : (K₂ * Λ)⁻¹ * r ^ (2 - (d : ℝ)) ≤ M := by
    have hr2d : r ^ (2 - (d : ℝ)) = ρ⁻¹ := by
      rw [hρ, ← Real.rpow_neg hr.le]
      congr 1
      ring
    rw [hr2d, ← mul_inv, inv_le_iff_one_le_mul₀' (by positivity)]
    linarith
  -- constants
  have hK₁exp := le_exp_logPlus_mul hK₁pos hΛ
  have hK₂exp := exp_neg_logPlus_mul_le_inv hK₂pos hΛ
  have hΛexp := exp_neg_two_sqrt_le_inv hΛ
  have hr2d0 : 0 < r ^ (2 - (d : ℝ)) := Real.rpow_pos_of_pos hr _
  filter_upwards [hmae] with x ⟨hmx, hxM⟩
  constructor
  · -- lower
    have e : Real.exp (-(CH * Real.sqrt Λ)) * M = m := by
      rw [hM, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    have hmlow : Real.exp (-(CH * Real.sqrt Λ)) * ((K₂ * Λ)⁻¹ * r ^ (2 - (d : ℝ))) ≤ m :=
      (mul_le_mul_of_nonneg_left hMlow (Real.exp_pos _).le).trans (le_of_eq e)
    refine le_trans ?_ (hmlow.trans hmx)
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hr2d0.le
    rw [mul_inv]
    calc Real.exp (-((CH + 2 + logPlus K₁ + logPlus K₂) * Real.sqrt Λ))
        ≤ Real.exp (-(CH * Real.sqrt Λ)) * (Real.exp (-(logPlus K₂ * Real.sqrt Λ)) *
            Real.exp (-(2 * Real.sqrt Λ))) := by
          rw [← Real.exp_add, ← Real.exp_add]
          apply Real.exp_le_exp.2
          linarith [mul_nonneg (logPlus_nonneg K₁) (Real.sqrt_nonneg Λ)]
      _ ≤ Real.exp (-(CH * Real.sqrt Λ)) * (K₂⁻¹ * Λ⁻¹) := by
          gcongr
  · -- upper
    calc G x ≤ M := hxM
      _ ≤ Real.exp (CH * Real.sqrt Λ) * (K₁ * r ^ (2 - (d : ℝ))) :=
          mul_le_mul_of_nonneg_left hmup (Real.exp_pos _).le
      _ ≤ Real.exp (CH * Real.sqrt Λ) * (Real.exp (logPlus K₁ * Real.sqrt Λ) *
            r ^ (2 - (d : ℝ))) := by gcongr
      _ = Real.exp ((CH + logPlus K₁) * Real.sqrt Λ) * r ^ (2 - (d : ℝ)) := by
          rw [← mul_assoc, ← Real.exp_add]
          ring_nf
      _ ≤ Real.exp ((CH + 2 + logPlus K₁ + logPlus K₂) * Real.sqrt Λ) * r ^ (2 - (d : ℝ)) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right
            (by linarith [logPlus_nonneg K₂]) hs)) hr2d0.le

/-- **Proposition 4.42**: two-sided bounds `exp(∓C Λ^{1/2}) r^{2-d}` for the Green function
on the annuli `A_r`, `r ≤ R/2`, and pointwise for the representative continuous in `B_R \ {0}`. -/
theorem greenD3_full (d : ℕ) (hd : 3 ≤ d) (hDir : GreenDirichletConcl d)
    (hMax : GreenMaxPrincipleConcl d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ R : ℝ), 0 < R → ∀ a : CoeffField d,
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) R))) →
      (∀ x ∈ euclideanBall (0 : Vec d) R, IsEllipticMatrix 1 Λ (a x)) →
      ∀ G : Vec d → ℝ, IsGreenFunction a R G →
        (∀ r : ℝ, 0 < r → r ≤ R / 2 →
          ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) r \ euclideanBall (0 : Vec d) (r / 2))),
            Real.exp (-(C * Real.sqrt Λ)) * r ^ (2 - (d : ℝ)) ≤ G x ∧
            G x ≤ Real.exp (C * Real.sqrt Λ) * r ^ (2 - (d : ℝ))) ∧
        (∀ Gc : Vec d → ℝ, ContinuousOn Gc (euclideanBall (0 : Vec d) R \ {0}) →
          Gc =ᵐ[volumeOn (euclideanBall (0 : Vec d) R)] G →
          ∀ x : Vec d, 0 < vecEuclideanNorm x → vecEuclideanNorm x ≤ R / 2 →
            Real.exp (-(C * Real.sqrt Λ)) * vecEuclideanNorm x ^ (2 - (d : ℝ)) ≤ Gc x ∧
            Gc x ≤ Real.exp (C * Real.sqrt Λ) * vecEuclideanNorm x ^ (2 - (d : ℝ))) := by
  obtain ⟨C, hC, hbounds⟩ := isGreen_bounds_D (d := d) hd
  refine ⟨C, hC, ?_⟩
  intro Λ R hR a hmeas hell G hG
  obtain ⟨S⟩ := ApproxSetting.nonempty_ofDirichlet hDir hR hmeas hell
  have hGnn : ∀ n, ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)),
      0 ≤ (S.G n).toH1Function.toFun x := fun n =>
    (hMax Λ R hR a hmeas hell a (Or.inl rfl)).2 _ (memL2On_approxSource hR.le _)
      (Eventually.of_forall fun x => approxSource_nonneg _ x) (S.G n) (S.solG n)
  refine ⟨fun r hr hrR => ?_, fun Gc hGc hGcae x hx0 hxR => ?_⟩
  · have hAD : euclideanBall (0 : Vec d) r \ euclideanBall (0 : Vec d) (r / 2) ⊆
        euclideanBall (0 : Vec d) (3 * r / 2) \ euclideanBall (0 : Vec d) (r / 4) := fun x hx =>
      ⟨euclideanBall_mono hr.le (by linarith) hx.1,
        fun h => hx.2 (euclideanBall_mono (by positivity) (by linarith) h)⟩
    exact ae_restrict_of_ae_restrict_of_subset hAD (hbounds S hGnn hG hr hrR)
  · set r := vecEuclideanNorm x with hrdef
    set O := euclideanBall (0 : Vec d) (3 * r / 2) \ euclideanClosedBall (0 : Vec d) (r / 4)
    have hOo : IsOpen O := (isOpen_euclideanBall _ _).sdiff (isClosed_euclideanClosedBall _ _)
    have hOD : O ⊆ euclideanBall (0 : Vec d) (3 * r / 2) \ euclideanBall (0 : Vec d) (r / 4) :=
      fun y hy => ⟨hy.1, fun h => hy.2 (euclideanBall_subset_euclideanClosedBall _ _ h)⟩
    have hOB : O ⊆ euclideanBall (0 : Vec d) R := fun y hy =>
      euclideanBall_mono (by positivity) (by linarith) hy.1
    have hOp : O ⊆ euclideanBall (0 : Vec d) R \ {0} := by
      intro y hy
      refine ⟨hOB hy, fun h0 => hy.2 ?_⟩
      rw [Set.mem_singleton_iff.1 h0]
      exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
        (by rw [sub_zero, vecEuclideanNorm_eq_zero_iff.2 rfl]; positivity)
    have hae : ∀ᵐ y ∂volumeOn O,
        Real.exp (-(C * Real.sqrt Λ)) * r ^ (2 - (d : ℝ)) ≤ Gc y ∧
        Gc y ≤ Real.exp (C * Real.sqrt Λ) * r ^ (2 - (d : ℝ)) := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hOD (hbounds S hGnn hG hx0 hxR),
        ae_restrict_of_ae_restrict_of_subset hOB hGcae] with y hy hyc
      rw [hyc]
      exact hy
    have hxO : x ∈ O := by
      refine ⟨?_, ?_⟩
      · rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity), sub_zero]; linarith
      · rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity), sub_zero]
        intro h
        linarith
    exact Ch4GreenHarnack.forall_mem_of_ae_bounds hOo (hGc.mono hOp) hae x hxO

end PDE.Ch4Green
