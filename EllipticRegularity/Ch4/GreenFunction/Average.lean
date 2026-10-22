module

public import PDEFoundation

/-!
# Averages over small centred balls

Averages over `B_ρ(0)` of a function continuous on `B_s(0)` converge to its value at the
origin as `ρ → 0`, and are bounded by a uniform bound of the function on `B_s(0)`.
-/

@[expose] public section

open scoped Topology

namespace PDE.Ch4Green

open MeasureTheory PDE Filter

variable {d : ℕ}

/-- An average is within `δ` of `c` if the function is within `δ` of `c` on the set. -/
theorem abs_integralAverage_sub_le {f : Vec d → ℝ} {S : Set (Vec d)}
    (h0 : volume S ≠ 0) (hfin : volume S ≠ ⊤) (hf : IntegrableOn f S) {c δ : ℝ}
    (hδ : ∀ x ∈ S, |f x - c| ≤ δ) : |integralAverage S f - c| ≤ δ := by
  have hpos : 0 < (volume S).toReal := ENNReal.toReal_pos h0 hfin
  have hint : IntegrableOn (fun _ : Vec d => c) S := integrableOn_const hfin
  have hsplit : integralAverage S f - c =
      (volume S).toReal⁻¹ * ∫ x in S, (f x - c) := by
    rw [integralAverage, integral_sub hf hint, setIntegral_const, smul_eq_mul, mul_sub,
      Measure.real, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  rw [hsplit, abs_mul, abs_inv, abs_of_pos hpos]
  have hb : ‖∫ x in S, (f x - c)‖ ≤ δ * volume.real S :=
    norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.2 hfin)
      (fun x hx => by simpa [Real.norm_eq_abs] using hδ x hx)
  rw [Real.norm_eq_abs, Measure.real] at hb
  calc (volume S).toReal⁻¹ * |∫ x in S, (f x - c)|
      ≤ (volume S).toReal⁻¹ * (δ * (volume S).toReal) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hpos.le)
    _ = δ := by field_simp

/-- A uniform bound on a ball bounds the averages over smaller centred balls. -/
theorem abs_integralAverage_le_of_abs_le {f : Vec d → ℝ} {s ρ M : ℝ} (hρ : 0 < ρ)
    (hρs : ρ ≤ s) (hM : ∀ x ∈ euclideanBall (0 : Vec d) s, |f x| ≤ M) :
    |integralAverage (euclideanBall (0 : Vec d) ρ) f| ≤ M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 (center_mem_euclideanBall _ (hρ.trans_le hρs)))
  have hpos := volume_euclideanBall_toReal_pos (0 : Vec d) hρ
  have hb : ‖∫ x in euclideanBall (0 : Vec d) ρ, f x‖ ≤
      M * volume.real (euclideanBall (0 : Vec d) ρ) :=
    norm_setIntegral_le_of_norm_le_const
      (lt_top_iff_ne_top.2 (volume_euclideanBall_ne_top _ hρ.le))
      (fun x hx => by
        rw [Real.norm_eq_abs]
        exact hM x (euclideanBall_mono hρ.le hρs hx))
  rw [Real.norm_eq_abs, Measure.real] at hb
  rw [integralAverage, abs_mul, abs_inv, ENNReal.abs_toReal]
  calc (volume (euclideanBall (0 : Vec d) ρ)).toReal⁻¹ * |∫ x in euclideanBall (0 : Vec d) ρ, f x|
      ≤ (volume (euclideanBall (0 : Vec d) ρ)).toReal⁻¹ *
          (M * (volume (euclideanBall (0 : Vec d) ρ)).toReal) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hpos.le)
    _ = M := by field_simp

/-- Averages over centred balls of a function continuous near the origin converge to its value
at the origin. -/
theorem tendsto_integralAverage_euclideanBall {f : Vec d → ℝ} {s : ℝ} (hs : 0 < s)
    (hf : ContinuousOn f (euclideanBall (0 : Vec d) s)) :
    Tendsto (fun ρ => integralAverage (euclideanBall (0 : Vec d) ρ) f) (𝓝[>] 0)
      (𝓝 (f 0)) := by
  have hcont : ContinuousAt f 0 :=
    hf.continuousAt ((isOpen_euclideanBall _ _).mem_nhds (center_mem_euclideanBall _ hs))
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨r, hr, hball⟩ := Metric.continuousAt_iff.1 hcont (δ / 2) (half_pos hδ)
  -- the sup-norm ball of radius `r` contains the Euclidean ball of radius `r`
  have hsub : ∀ x ∈ euclideanBall (0 : Vec d) r, dist x 0 < r := by
    intro x hx
    have h := (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx
    rw [sub_zero] at h
    rw [dist_zero_right]
    exact lt_of_le_of_lt (norm_le_vecEuclideanNorm x) h
  have hevent : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 0 < ρ ∧ ρ < min r s :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT (lt_min hr hs)) fun ρ hρ => hρ
  filter_upwards [hevent] with ρ ⟨hρ, hρlt⟩
  have hρr : ρ < r := hρlt.trans_le (min_le_left _ _)
  have hρs : ρ < s := hρlt.trans_le (min_le_right _ _)
  have hint : IntegrableOn f (euclideanBall (0 : Vec d) ρ) := by
    have hK : IntegrableOn f (euclideanClosedBall (0 : Vec d) ρ) :=
      (hf.mono (euclideanClosedBall_subset_euclideanBall hρ.le hρs)).integrableOn_compact
        (isCompact_euclideanClosedBall _ hρ.le)
    exact hK.mono_set (euclideanBall_subset_euclideanClosedBall _ _)
  have hle := abs_integralAverage_sub_le (volume_euclideanBall_pos (0 : Vec d) hρ).ne'
    (volume_euclideanBall_ne_top _ hρ.le) hint (c := f 0) (δ := δ / 2) (fun x hx => by
      have := hball (hsub x (euclideanBall_mono hρ.le hρr.le hx))
      rw [Real.dist_eq] at this
      exact this.le)
  rw [Real.dist_eq]
  linarith

/-- Averages over centred balls only depend on the a.e. class on a larger set. -/
theorem integralAverage_congr_ae {f g : Vec d → ℝ} {S T : Set (Vec d)} (hST : S ⊆ T)
    (hfg : f =ᵐ[volumeOn T] g) : integralAverage S f = integralAverage S g := by
  rw [integralAverage, integralAverage,
    integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hST hfg)]

end PDE.Ch4Green
