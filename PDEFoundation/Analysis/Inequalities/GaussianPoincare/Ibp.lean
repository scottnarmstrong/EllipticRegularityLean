module

public import PDEFoundation.Analysis.Inequalities.GaussianPoincare.Deriv
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import PDEFoundation.Ambient.Basis

/-!
# Gaussian integration by parts along the rotation-invariant direction

For `v_i = (-sin φ e_i, cos φ e_i)` the rotated point `zc φ` is constant along `v_i`, which turns the
Gaussian integration by parts into the cross-term cancellation of the manuscript proof.
-/

@[expose] public section

open MeasureTheory Real

namespace PDE.GaussianPoincare

variable {d : ℕ}

theorem vecDot_smul_right {d : ℕ} (x a : Vec d) (r : ℝ) : vecDot x (r • a) = r * vecDot x a := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem zc_add_smul (φ : ℝ) (i : Fin d) (p : Vec d × Vec d) (τ : ℝ) :
    zc φ (p + τ • ((-Real.sin φ • basisVec i, Real.cos φ • basisVec i) : Vec d × Vec d)) =
      zc φ p := by
  ext j
  simp only [zc, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem ibp_coord {t : ℝ} (ht : 0 < t) {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hc : HasCompactSupport u) (φ : ℝ) (i : Fin d) :
    ∫ p : Vec d × Vec d, u p.1 * classicalGradient u (zc φ p) i *
        (wc φ p i * pairHeat d t p) =
      -(2 * t * Real.sin φ) * ∫ p : Vec d × Vec d,
        classicalGradient u p.1 i * classicalGradient u (zc φ p) i * pairHeat d t p := by
  obtain ⟨M, L, hM0, hL0, hM, hL⟩ := exists_bounds hu hc
  have hu1 := contDiff_one_of_top hu
  set s := Real.sin φ with hs
  set c := Real.cos φ with hcdef
  have hGc := continuous_classicalGradient_apply hu i
  have hG : ∀ x, |classicalGradient u x i| ≤ L := fun x => abs_classicalGradient_le hL x i
  set v : Vec d × Vec d := (-s • basisVec i, c • basisVec i) with hv
  set G : Vec d → ℝ := fun x => classicalGradient u x i with hGdef
  set f : Vec d × Vec d → ℝ := fun p => u p.1 * G (zc φ p) with hf
  set f' : Vec d × Vec d → ℝ := fun p => (-s * G p.1) * G (zc φ p) with hf'
  set g' : Vec d × Vec d → ℝ := fun p => -(1 / (2 * t)) * (wc φ p i * pairHeat d t p) with hg'
  have hfc : Continuous f := (hu.continuous.comp continuous_fst).mul
    (hGc.comp (continuous_zc φ))
  have hf'c : Continuous f' := (continuous_const.mul (hGc.comp continuous_fst)).mul
    (hGc.comp (continuous_zc φ))
  have hs1 : |s| ≤ 1 := Real.abs_sin_le_one φ
  have hlf : ∀ p, HasLineDerivAt ℝ f (f' p) p v := by
    intro p
    unfold HasLineDerivAt
    have hfun : (fun τ : ℝ => f (p + τ • v)) =
        fun τ => u (p.1 + τ • (-s • basisVec i)) * G (zc φ p) := by
      funext τ
      simp only [hf]
      rw [hv, zc_add_smul]
      simp
    rw [hfun]
    have h1 : HasDerivAt (fun τ : ℝ => p.1 + τ • (-s • (basisVec i : Vec d)))
        (-s • basisVec i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (-s • (basisVec i : Vec d))).const_add p.1
    have hdu : HasFDerivAt u (fderiv ℝ u p.1) (p.1 + (0 : ℝ) • (-s • (basisVec i : Vec d))) := by
      simpa using (hu.differentiable (by simp)).differentiableAt.hasFDerivAt
    have h2 := hdu.comp_hasDerivAt (0 : ℝ) h1
    have h3 := h2.mul_const (G (zc φ p))
    refine h3.congr_deriv ?_
    show _ = (-s * G p.1) * G (zc φ p)
    rw [map_smul, smul_eq_mul]
    rfl
  have hlg : ∀ p, HasLineDerivAt ℝ (pairHeat d t) (g' p) p v := by
    intro p
    have := hasDerivAt_pairHeat_line ht p v
    unfold HasLineDerivAt
    convert this using 1
    simp only [hg', hv, vecDot_smul_right, vecDot_basisVec_right, wc, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  have i1 : Integrable (fun p => f' p * pairHeat d t p) :=
    integrable_bdd_mul_pairHeat ht (h := f') hf'c (C := L * L) fun p => by
      simp only [hf', abs_mul, abs_neg]
      have := hG p.1
      have := hG (zc φ p)
      have h0 := abs_nonneg (G p.1)
      have h1 := abs_nonneg (G (zc φ p))
      calc |s| * |G p.1| * |G (zc φ p)| ≤ 1 * L * L := by gcongr
        _ = L * L := by ring
  have i2 : Integrable (fun p => f p * pairHeat d t p) :=
    integrable_bdd_mul_pairHeat ht (h := f) hfc (C := M * L) fun p => by
      simp only [hf, abs_mul]
      exact mul_le_mul (hM _) (hG _) (abs_nonneg _) hM0
  have i3 : Integrable (fun p => f p * g' p) := by
    have := integrable_bdd_mul_lin_pairHeat ht (h := fun p => f p * (-(1 / (2 * t))))
      (q := fun p => wc φ p i) (hfc.mul continuous_const) (C := M * L * (1 / (2 * t)))
      (fun p => by
        rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * t))]
        have : |f p| ≤ M * L := by
          simp only [hf, abs_mul]
          exact mul_le_mul (hM _) (hG _) (abs_nonneg _) hM0
        exact mul_le_mul_of_nonneg_right this (by positivity))
      ((continuous_apply i).comp (continuous_wc φ)) (abs_wc_apply_le φ · i)
    convert this using 1
    funext p
    simp only [hg']
    ring
  have : (volume : Measure (Vec d × Vec d)).IsAddHaarMeasure :=
    MeasureTheory.Measure.prod.instIsAddHaarMeasure (volume : Measure (Vec d))
      (volume : Measure (Vec d))
  have hibp := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure (Vec d × Vec d))) (B := ContinuousLinearMap.mul ℝ ℝ)
    (f := f) (f' := f') (g := pairHeat d t) (g' := g') (v := v)
    (by simpa using i1) (by simpa using i3) (by simpa using i2)
    (fun p _ => hlf p) (fun p _ => hlg p)
  simp only [ContinuousLinearMap.mul_apply'] at hibp
  have e1 : ∫ p, f p * g' p =
      -(1 / (2 * t)) * ∫ p : Vec d × Vec d, u p.1 * classicalGradient u (zc φ p) i *
        (wc φ p i * pairHeat d t p) := by
    rw [← integral_const_mul]
    congr 1
    funext p
    simp only [hg', hf, hGdef]
    ring
  have e2 : ∫ p, f' p * pairHeat d t p = -s * ∫ p : Vec d × Vec d,
      classicalGradient u p.1 i * classicalGradient u (zc φ p) i * pairHeat d t p := by
    rw [← integral_const_mul]
    congr 1
    funext p
    simp only [hf', hGdef]
    ring
  rw [e1, e2] at hibp
  have ht2 : (2 * t) ≠ 0 := by positivity
  generalize (∫ p : Vec d × Vec d, u p.1 * classicalGradient u (zc φ p) i *
        (wc φ p i * pairHeat d t p)) = I at hibp ⊢
  generalize (∫ p : Vec d × Vec d,
        classicalGradient u p.1 i * classicalGradient u (zc φ p) i * pairHeat d t p) = J at hibp ⊢
  have hI : I = -(2 * t) * (-(1 / (2 * t)) * I) := by field_simp
  rw [hI, hibp]
  simp only [hs]
  ring

end PDE.GaussianPoincare
