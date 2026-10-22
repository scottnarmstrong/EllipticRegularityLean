module

public import PDEFoundation.Measure.PlanarWeightedRadialAverage
public import PDEFoundation.Measure.EuclideanRadialLogMoment
public import PDEFoundation.Measure.RadialLogModeLp

/-! # Exact planar logarithmic gradient energy -/

@[expose] public section

namespace PDE

open MeasureTheory Set

noncomputable section

private theorem gamma_two : Real.Gamma (2 : ℝ) = 1 := by
  norm_num [← Real.Gamma_nat_eq_factorial 1]

private theorem gamma_three : Real.Gamma (3 : ℝ) = 2 := by
  norm_num [← Real.Gamma_nat_eq_factorial 2]


private theorem integralAverage_add_of_integrable {d : ℕ} {U : Set (Vec d)}
    {f g : Vec d → ℝ} (hf : IntegrableOn f U) (hg : IntegrableOn g U) :
    integralAverage U (fun x => f x + g x) = integralAverage U f + integralAverage U g := by
  unfold integralAverage
  rw [integral_add hf hg]
  ring

private theorem integralAverage_sub_of_integrable {d : ℕ} {U : Set (Vec d)}
    {f g : Vec d → ℝ} (hf : IntegrableOn f U) (hg : IntegrableOn g U) :
    integralAverage U (fun x => f x - g x) = integralAverage U f - integralAverage U g := by
  unfold integralAverage
  rw [integral_sub hf hg]
  ring

private theorem integralAverage_const_mul_of_integrable {d : ℕ} {U : Set (Vec d)}
    {f : Vec d → ℝ} (c : ℝ) :
    integralAverage U (fun x => c * f x) = c * integralAverage U f := by
  unfold integralAverage
  rw [integral_const_mul]
  ring

private theorem integralAverage_const_of_pos_of_ne_top {d : ℕ} {U : Set (Vec d)}
    (hpos : 0 < volume U) (htop : volume U ≠ ⊤) (c : ℝ) :
    integralAverage U (fun _ => c) = c := by
  unfold integralAverage
  rw [setIntegral_const]
  have hreal : (volume U).toReal ≠ 0 := (ENNReal.toReal_pos hpos.ne' htop).ne'
  change (volume U).toReal⁻¹ * ((volume U).toReal * c) = c
  field_simp

/-- Exact normalized energy of the planar logarithmic coordinate mode on a
round ball. -/
theorem integralAverage_vecNormSq_radialLogGradientField_planar
    {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun x : Vec 2 => vecNormSq (radialLogGradientField 0 x))
        (euclideanBall 0 R) ∧
      integralAverage (euclideanBall (0 : Vec 2) R)
          (fun x => vecNormSq (radialLogGradientField 0 x)) =
        Real.log R ^ 2 + 1 / 2 := by
  let B := euclideanBall (0 : Vec 2) R
  let L : Vec 2 → ℝ := fun x => Real.log (vecEuclideanNorm x)
  let t : Vec 2 → ℝ := fun x => -Real.log (vecEuclideanNorm x / R)
  let w : Vec 2 → ℝ := fun x => x 0 ^ 2 / vecNormSq x
  have hBtop : volume B ≠ ⊤ := volume_euclideanBall_ne_top 0 hR.le
  have hBpos : 0 < volume B := volume_euclideanBall_pos 0 hR
  have hvolReal : (volume B).toReal ≠ 0 :=
    (ENNReal.toReal_pos hBpos.ne' hBtop).ne'
  have ht : IntegrableOn t B := by
    simpa [B, t] using
      integrableOn_neg_log_vecEuclideanNorm_div_euclideanBall
        (d := 2) (by norm_num) hR (by norm_num : (0 : ℝ) < 1)
  have ht2 : IntegrableOn (fun x => t x ^ 2) B := by
    simpa [B, t] using
      integrableOn_neg_log_vecEuclideanNorm_div_euclideanBall
        (d := 2) (by norm_num) hR (by norm_num : (0 : ℝ) < 2)
  have hneVol : ∀ᵐ x ∂volume, x ≠ (0 : Vec 2) := by
    rw [ae_iff]
    simpa only [not_ne_iff] using! (measure_singleton (μ := volume) (0 : Vec 2))
  have hne : ∀ᵐ x ∂volume.restrict B, x ≠ (0 : Vec 2) :=
    hneVol.filter_mono (ae_mono Measure.restrict_le_self)
  have hLB : ∀ᵐ x ∂volume.restrict B, L x = Real.log R - t x := by
    filter_upwards [hne] with x hx
    have hnorm : vecEuclideanNorm x ≠ 0 := (vecEuclideanNorm_pos_iff.mpr hx).ne'
    dsimp only [L, t]
    rw [Real.log_div hnorm hR.ne']
    ring
  have hL : IntegrableOn L B := by
    apply (integrableOn_const (C := Real.log R) hBtop).sub ht |>.congr
    filter_upwards [hLB] with x hx
    simpa using hx.symm
  have hL2 : IntegrableOn (fun x => L x ^ 2) B := by
    have hp : IntegrableOn
        (fun x => Real.log R ^ 2 - 2 * Real.log R * t x + t x ^ 2) B :=
      ((integrableOn_const (C := Real.log R ^ 2) hBtop).sub
        (ht.const_mul (2 * Real.log R))).add ht2
    apply hp.congr
    filter_upwards [hLB] with x hx
    rw [hx]
    ring
  have hw_bound : ∀ x : Vec 2, ‖w x‖ ≤ 1 := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (vecNormSq_nonneg _))]
    by_cases hx : x = 0
    · subst x; simp [vecNormSq, vecDot]
    · have hq : 0 < vecNormSq x :=
        lt_of_le_of_ne (vecNormSq_nonneg x) (Ne.symm (vecNormSq_eq_zero_iff.not.mpr hx))
      exact (div_le_one hq).mpr (sq_apply_le_vecNormSq x 0)
  have hw_meas : AEStronglyMeasurable w (volume.restrict B) :=
    (((measurable_pi_apply 0).pow_const 2).div continuous_vecNormSq.measurable).aestronglyMeasurable
  have hw : IntegrableOn w B := by
    exact MeasureTheory.Integrable.mono
      (integrableOn_const (C := (1 : ℝ)) hBtop) hw_meas
      (Filter.Eventually.of_forall fun x => by simpa using hw_bound x)
  have hwL : IntegrableOn (fun x => w x * L x) B :=
    hL.bdd_mul hw_meas (Filter.Eventually.of_forall hw_bound)
  have henergy (x : Vec 2) :
      vecNormSq (radialLogGradientField 0 x) = L x ^ 2 + 2 * (w x * L x) + w x := by
    by_cases hx : x = 0
    · subst x
      simp [radialLogGradientField, L, w, vecNormSq, vecDot]
      ring_nf
    · have hq : vecNormSq x ≠ 0 := vecNormSq_eq_zero_iff.not.mpr hx
      simp only [radialLogGradientField, vecNormSq, vecDot, Fin.sum_univ_two,
        basisVec_apply, L, w]
      have hqs : x 0 * x 0 + x 1 * x 1 ≠ 0 := by
        simpa [vecNormSq, vecDot, Fin.sum_univ_two] using hq
      have hqs2 : x 0 ^ 2 + x 1 ^ 2 ≠ 0 := by simpa [pow_two] using hqs
      simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false, ite_true, one_mul]
      field_simp [hqs2]
      ring
  have henergyInt : IntegrableOn
      (fun x => vecNormSq (radialLogGradientField 0 x)) B := by
    apply (hL2.add ((hwL.const_mul 2).add hw)).congr
    filter_upwards with x
    simp only [Pi.add_apply]
    rw [henergy]
    ring
  refine ⟨henergyInt, ?_⟩
  have havgt : integralAverage B t = (1 / 2 : ℝ) := by
    have hm := integralAverage_neg_log_vecEuclideanNorm_div_euclideanBall
      (d := 2) (by norm_num) hR (by norm_num : (0 : ℝ) < 1)
    dsimp [B, t]
    convert hm using 1 <;> norm_num [gamma_two]
  have havgt2 : integralAverage B (fun x => t x ^ 2) = (1 / 2 : ℝ) := by
    have hm := integralAverage_neg_log_vecEuclideanNorm_div_euclideanBall
      (d := 2) (by norm_num) hR (by norm_num : (0 : ℝ) < 2)
    dsimp [B, t]
    convert hm using 1 <;> norm_num [gamma_three]
  have havgConst (c : ℝ) : integralAverage B (fun _ => c) = c :=
    integralAverage_const_of_pos_of_ne_top hBpos hBtop c
  have havgL : integralAverage B L = Real.log R - 1 / 2 := by
    rw [integralAverage_congr_ae hLB,
      integralAverage_sub_of_integrable
        (integrableOn_const (C := Real.log R) hBtop) ht, havgConst, havgt]
  have hpolyAE : (fun x => L x ^ 2) =ᵐ[volume.restrict B]
      fun x => (Real.log R ^ 2 - 2 * Real.log R * t x) + t x ^ 2 := by
    filter_upwards [hLB] with x hx
    rw [hx]
    ring
  have havgL2 : integralAverage B (fun x => L x ^ 2) =
      Real.log R ^ 2 - Real.log R + 1 / 2 := by
    calc
      integralAverage B (fun x => L x ^ 2) =
          integralAverage B (fun x =>
            (Real.log R ^ 2 - 2 * Real.log R * t x) + t x ^ 2) :=
        integralAverage_congr_ae hpolyAE
      _ = integralAverage B (fun x => Real.log R ^ 2 - 2 * Real.log R * t x) +
          integralAverage B (fun x => t x ^ 2) :=
        integralAverage_add_of_integrable
          ((integrableOn_const (C := Real.log R ^ 2) hBtop).sub
            (ht.const_mul (2 * Real.log R))) ht2
      _ = (integralAverage B (fun _ => Real.log R ^ 2) -
          integralAverage B (fun x => 2 * Real.log R * t x)) +
          integralAverage B (fun x => t x ^ 2) := by
        rw [integralAverage_sub_of_integrable
          (integrableOn_const (C := Real.log R ^ 2) hBtop)
          (ht.const_mul (2 * Real.log R))]
      _ = Real.log R ^ 2 - Real.log R + 1 / 2 := by
        rw [havgConst, integralAverage_const_mul_of_integrable (f := t), havgt, havgt2]
        ring
  have havgwL := integralAverage_planar_coordinate_square_ratio_mul_radial hR
    (fun r => Real.log r) (by simpa [B, L] using hL)
  have havgw := integralAverage_planar_coordinate_square_ratio_mul_radial hR
    (fun _ => (1 : ℝ)) (integrableOn_const hBtop)
  have hsumInt : IntegrableOn (fun x => L x ^ 2 + 2 * (w x * L x)) B := by
    simpa only [Pi.add_apply] using! hL2.add (hwL.const_mul 2)
  have havgEnergy :
      integralAverage B (fun x => vecNormSq (radialLogGradientField 0 x)) =
        integralAverage B (fun x => L x ^ 2) +
          2 * integralAverage B (fun x => w x * L x) + integralAverage B w := by
    calc
      integralAverage B (fun x => vecNormSq (radialLogGradientField 0 x)) =
          integralAverage B (fun x => (L x ^ 2 + 2 * (w x * L x)) + w x) := by
            apply integralAverage_congr_ae
            filter_upwards with x
            exact henergy x
      _ = integralAverage B (fun x => L x ^ 2 + 2 * (w x * L x)) +
          integralAverage B w :=
        integralAverage_add_of_integrable hsumInt hw
      _ = (integralAverage B (fun x => L x ^ 2) +
          integralAverage B (fun x => 2 * (w x * L x))) + integralAverage B w := by
        rw [integralAverage_add_of_integrable hL2 (hwL.const_mul 2)]
      _ = integralAverage B (fun x => L x ^ 2) +
          2 * integralAverage B (fun x => w x * L x) + integralAverage B w := by
        rw [integralAverage_const_mul_of_integrable (f := fun x => w x * L x)]
  have hwLeq : integralAverage B (fun x => w x * L x) =
      (1 / 2 : ℝ) * integralAverage B L := by
    simpa only [B, L, w] using havgwL
  have hweq : integralAverage B w = (1 / 2 : ℝ) := by
    have h := havgw
    simpa only [B, w, mul_one, havgConst (1 : ℝ)] using h
  rw [havgEnergy, havgL2, hwLeq, havgL, hweq]
  ring


end
end PDE
