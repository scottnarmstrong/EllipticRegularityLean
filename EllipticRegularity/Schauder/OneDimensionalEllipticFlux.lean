module

public import EllipticRegularity.Schauder.OneDimensional

/-! # One-dimensional elliptic constant-flux estimates

Scalar constant-flux estimates on the unit interval under the full elliptic
coefficient range `1 ≤ k ≤ Λ`.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- An actual constant flux with coefficient between `1` and `Λ` is controlled
by the gradient and forcing norms. -/
theorem abs_constantFlux_le_elliptic_norms
    {k g F : ℝ → ℝ} {p c Lam : ℝ} (hp : 1 < p) (hLam : 1 ≤ Lam)
    (hg : MemLp g 2 (volume.restrict (Ioo (-1 : ℝ) 1)))
    (hF : MemLp F (ENNReal.ofReal p) (volume.restrict (Ioo (-1 : ℝ) 1)))
    (hq : IntegrableOn (fun t => k t * g t + F t) (Ioo (-1 : ℝ) 1))
    (hk : ∀ᵐ t ∂volume.restrict (Ioo (-1 : ℝ) 1), 1 ≤ k t ∧ k t ≤ Lam)
    (hc : (fun t => k t * g t + F t) =ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)]
      fun _ => c) :
    |c| ≤ 2 * (Lam *
        (eLpNorm g 2 (volume.restrict (Ioo (-1 : ℝ) 1))).toReal +
      (eLpNorm F (ENNReal.ofReal p)
        (volume.restrict (Ioo (-1 : ℝ) 1))).toReal) := by
  have hgabs : IntegrableOn (fun t => |g t|) (Ioo (-1 : ℝ) 1) := by
    simpa only [Real.norm_eq_abs] using! (hg.integrable (by norm_num)).norm
  have hFabs : IntegrableOn (fun t => |F t|) (Ioo (-1 : ℝ) 1) := by
    simpa only [Real.norm_eq_abs] using!
      (hF.integrable (ENNReal.one_le_ofReal.mpr hp.le)).norm
  have heq : (∫ t in Ioo (-1 : ℝ) 1, k t * g t + F t) = 2 * c := by
    rw [integral_congr_ae hc, setIntegral_const, measureReal_def, Real.volume_Ioo]
    norm_num [smul_eq_mul]
  have habs : (∫ t in Ioo (-1 : ℝ) 1, |k t * g t + F t|) ≤
      Lam * (∫ t in Ioo (-1 : ℝ) 1, |g t|) +
        ∫ t in Ioo (-1 : ℝ) 1, |F t| := by
    calc
      _ ≤ ∫ t in Ioo (-1 : ℝ) 1, Lam * |g t| + |F t| := by
        apply integral_mono_ae hq.norm ((hgabs.const_mul Lam).add hFabs)
        filter_upwards [hk] with t ht
        exact (abs_add_le _ _).trans
          (add_le_add (by
            rw [abs_mul, abs_of_nonneg (zero_le_one.trans ht.1)]
            exact mul_le_mul_of_nonneg_right ht.2 (abs_nonneg _)) le_rfl)
      _ = _ := by
        rw [integral_add (hgabs.const_mul Lam) hFabs, integral_const_mul]
  have hnorm : 2 * |c| ≤ (∫ t in Ioo (-1 : ℝ) 1, |k t * g t + F t|) := by
    have h := norm_integral_le_integral_norm (fun t => k t * g t + F t)
      (μ := volume.restrict (Ioo (-1 : ℝ) 1))
    simpa only [Real.norm_eq_abs, heq, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)] using h
  have hgint := setIntegral_abs_unitInterval_le_two_eLpNorm
    (by norm_num : (1 : ℝ) < 2) (by simpa only [ENNReal.ofReal_ofNat] using hg)
  simp only [ENNReal.ofReal_ofNat] at hgint
  have hFint := setIntegral_abs_unitInterval_le_two_eLpNorm hp hF
  have hLam0 : 0 ≤ Lam := zero_le_one.trans hLam
  have hg0 : 0 ≤ (eLpNorm g 2
      (volume.restrict (Ioo (-1 : ℝ) 1))).toReal := ENNReal.toReal_nonneg
  have hF0 : 0 ≤ (eLpNorm F (ENNReal.ofReal p)
      (volume.restrict (Ioo (-1 : ℝ) 1))).toReal := ENNReal.toReal_nonneg
  have habs' := hnorm.trans habs
  calc
    |c| ≤ Lam * (eLpNorm g 2
          (volume.restrict (Ioo (-1 : ℝ) 1))).toReal +
        (eLpNorm F (ENNReal.ofReal p)
          (volume.restrict (Ioo (-1 : ℝ) 1))).toReal := by
      nlinarith
    _ ≤ 2 * (Lam * (eLpNorm g 2
          (volume.restrict (Ioo (-1 : ℝ) 1))).toReal +
        (eLpNorm F (ENNReal.ofReal p)
          (volume.restrict (Ioo (-1 : ℝ) 1))).toReal) := by nlinarith

/-- The scalar elliptic constant-flux identity gives a Hölder representative
on the half interval. -/
theorem exists_holder_representative_of_unitInterval_elliptic_constantFlux
    {k u g F : ℝ → ℝ} {α p c Lam : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hp : 1 < p) (hpα : 1 - 1 / p = α)
    (hLam : 1 ≤ Lam)
    (hu : MemLp u 2 (volume.restrict (Ioo (-1 : ℝ) 1)))
    (hg : MemLp g 2 (volume.restrict (Ioo (-1 : ℝ) 1)))
    (hweak : HasWeakDerivOnIoo (-1) 1 u g)
    (hF : MemLp F (ENNReal.ofReal p) (volume.restrict (Ioo (-1 : ℝ) 1)))
    (hq : IntegrableOn (fun t => k t * g t + F t) (Ioo (-1 : ℝ) 1))
    (hk : ∀ᵐ t ∂volume.restrict (Ioo (-1 : ℝ) 1), 1 ≤ k t ∧ k t ≤ Lam)
    (hc : (fun t => k t * g t + F t) =ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)]
      fun _ => c) :
    ∃ v : ℝ → ℝ, u =ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)] v ∧
      ∀ x ∈ Ioo (-1 / 2 : ℝ) (1 / 2), ∀ y ∈ Ioo (-1 / 2 : ℝ) (1 / 2),
        |v x - v y| ≤ 8 * (1 + Lam) *
          ((eLpNorm g 2 (volume.restrict (Ioo (-1 : ℝ) 1))).toReal +
            (eLpNorm F (ENNReal.ofReal p)
              (volume.restrict (Ioo (-1 : ℝ) 1))).toReal) * |x - y| ^ α := by
  have hcBound := abs_constantFlux_le_elliptic_norms hp hLam hg hF hq hk hc
  have hderiv : ∀ᵐ t ∂volume.restrict (Ioo (-1 : ℝ) 1),
      |g t| ≤ |c| + |F t| := by
    filter_upwards [hk, hc] with t ht hct
    have hkg : |k t * g t| ≤ |c| + |F t| := by
      have heq : k t * g t = c - F t := by linarith
      rw [heq]
      exact abs_sub c (F t)
    rw [abs_mul, abs_of_nonneg (zero_le_one.trans ht.1)] at hkg
    nlinarith [abs_nonneg (g t)]
  obtain ⟨v, _, huv, hv⟩ :=
    exists_continuousOn_representative_with_forced_holder_increment (by norm_num)
      hu hg hweak hp hF (abs_nonneg c) (by norm_num : (0 : ℝ) ≤ 1)
        (by simpa only [one_mul] using hderiv)
  refine ⟨v, huv, ?_⟩
  intro x hx y hy
  have hxclosed : x ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hyclosed : y ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hdist : |x - y| ≤ 1 :=
    (abs_le).mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
  have hpow : |x - y| ≤ |x - y| ^ α := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg _) hdist hα.le hα1.le
  have hincrement := hv x hxclosed y hyclosed
  rw [hpα] at hincrement
  have hp0 : 0 ≤ |x - y| ^ α := Real.rpow_nonneg (abs_nonneg _) _
  have hF0 : 0 ≤ (eLpNorm F (ENNReal.ofReal p)
      (volume.restrict (Ioo (-1 : ℝ) 1))).toReal := ENNReal.toReal_nonneg
  have hg0 : 0 ≤ (eLpNorm g 2
      (volume.restrict (Ioo (-1 : ℝ) 1))).toReal := ENNReal.toReal_nonneg
  have hLam0 : 0 ≤ Lam := zero_le_one.trans hLam
  have hreplace := mul_le_mul_of_nonneg_left hpow (abs_nonneg c)
  have hcoefficient : |c| +
      (eLpNorm F (ENNReal.ofReal p)
        (volume.restrict (Ioo (-1 : ℝ) 1))).toReal ≤
      8 * (1 + Lam) *
        ((eLpNorm g 2 (volume.restrict (Ioo (-1 : ℝ) 1))).toReal +
          (eLpNorm F (ENNReal.ofReal p)
            (volume.restrict (Ioo (-1 : ℝ) 1))).toReal) := by
    calc
      _ ≤ 2 * (Lam * (eLpNorm g 2
            (volume.restrict (Ioo (-1 : ℝ) 1))).toReal +
          (eLpNorm F (ENNReal.ofReal p)
            (volume.restrict (Ioo (-1 : ℝ) 1))).toReal) +
          (eLpNorm F (ENNReal.ofReal p)
            (volume.restrict (Ioo (-1 : ℝ) 1))).toReal :=
        add_le_add hcBound le_rfl
      _ ≤ _ := by
        nlinarith [mul_nonneg hLam0 hg0, mul_nonneg hLam0 hF0]
  calc
    |v x - v y| ≤ |c| * |x - y| +
        (eLpNorm F (ENNReal.ofReal p)
          (volume.restrict (Ioo (-1 : ℝ) 1))).toReal * |x - y| ^ α := by
      simpa only [one_mul] using hincrement
    _ ≤ |c| * |x - y| ^ α +
        (eLpNorm F (ENNReal.ofReal p)
          (volume.restrict (Ioo (-1 : ℝ) 1))).toReal * |x - y| ^ α :=
      add_le_add hreplace le_rfl
    _ = (|c| + (eLpNorm F (ENNReal.ofReal p)
          (volume.restrict (Ioo (-1 : ℝ) 1))).toReal) * |x - y| ^ α := by ring
    _ ≤ (8 * (1 + Lam) *
        ((eLpNorm g 2 (volume.restrict (Ioo (-1 : ℝ) 1))).toReal +
          (eLpNorm F (ENNReal.ofReal p)
            (volume.restrict (Ioo (-1 : ℝ) 1))).toReal)) * |x - y| ^ α :=
      mul_le_mul_of_nonneg_right hcoefficient hp0
    _ = _ := by ring

end

end PDE
