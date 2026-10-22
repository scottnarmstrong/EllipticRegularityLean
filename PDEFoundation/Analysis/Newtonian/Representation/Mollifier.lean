module

public import PDEFoundation.Analysis.Newtonian.Representation.Calculus
public import PDEFoundation.Analysis.RieszWeakTypeRadial
public import PDEFoundation.Analysis.HilbertDictionary

/-!
# The approximate identity `regDiv ε`

`regDiv 1` is a nonnegative integrable radial function of total mass one, and
`regDiv ε (ε v) = ε^(-d) regDiv 1 v`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace PDE

namespace NewtonRepresentation

noncomputable section

variable {d : ℕ}

/-- Radial profile of the mollifier: `r ^ (d-1) (r²+1)^(-d/2-1)`. -/
def radialProfile (d : ℕ) (r : ℝ) : ℝ :=
  r ^ (d - 1) * (r ^ 2 + 1) ^ (-((d : ℝ) / 2) - 1)

/-- Its primitive `r^d (r²+1)^(-d/2) / d`. -/
def radialPrimitive (d : ℕ) (r : ℝ) : ℝ :=
  r ^ d * (r ^ 2 + 1) ^ (-((d : ℝ) / 2)) / d

theorem hasDerivAt_radialPrimitive (hd : 0 < d) (r : ℝ) :
    HasDerivAt (radialPrimitive d) (radialProfile d r) r := by
  have hs : 0 < r ^ 2 + 1 := by positivity
  have h1 := hasDerivAt_pow d r
  have h2 : HasDerivAt (fun y : ℝ => y ^ 2 + 1) (2 * r) r := by
    simpa using (hasDerivAt_pow 2 r).add_const 1
  have h3 := h2.rpow_const (p := -((d : ℝ) / 2)) (Or.inl hs.ne')
  have h4 := (h1.mul h3).div_const (d : ℝ)
  unfold radialPrimitive
  refine h4.congr_deriv ?_
  unfold radialProfile
  have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hpow : r ^ d = r ^ (d - 1) * r := by
    rw [← pow_succ, Nat.sub_add_cancel hd]
  have hrp : (r ^ 2 + 1) ^ (-((d : ℝ) / 2)) = (r ^ 2 + 1) ^ (-((d : ℝ) / 2) - 1) * (r ^ 2 + 1) := by
    rw [← Real.rpow_add_one hs.ne']; congr 1; ring
  rw [hpow, hrp]
  field_simp
  ring

theorem radialProfile_nonneg (r : ℝ) (hr : 0 ≤ r) : 0 ≤ radialProfile d r := by
  unfold radialProfile
  exact mul_nonneg (pow_nonneg hr _) (Real.rpow_nonneg (by positivity) _)

theorem tendsto_radialPrimitive (hd : 0 < d) :
    Tendsto (radialPrimitive d) atTop (𝓝 (1 / (d : ℝ))) := by
  have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have key : ∀ r : ℝ, 0 < r → r ^ d * (r ^ 2 + 1) ^ (-((d : ℝ) / 2)) =
      (1 - 1 / (r ^ 2 + 1)) ^ ((d : ℝ) / 2) := by
    intro r hr
    have hs : 0 < r ^ 2 + 1 := by positivity
    have e1 : 1 - 1 / (r ^ 2 + 1) = r ^ 2 / (r ^ 2 + 1) := by field_simp; ring
    have e2 : r ^ d = (r ^ 2) ^ ((d : ℝ) / 2) := by
      rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le, ← Real.rpow_natCast r d]
      congr 1
      push_cast; ring
    rw [e1, Real.div_rpow (by positivity) hs.le, Real.rpow_neg hs.le, e2, div_eq_mul_inv]
    ring
  have hlim : Tendsto (fun r : ℝ => (1 - 1 / (r ^ 2 + 1)) ^ ((d : ℝ) / 2)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun r : ℝ => 1 / (r ^ 2 + 1)) atTop (𝓝 0) := by
      simp only [one_div]
      exact tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right _ _ (tendsto_pow_atTop (by norm_num)))
    have h1 : Tendsto (fun r : ℝ => 1 - 1 / (r ^ 2 + 1)) atTop (𝓝 1) := by
      simpa using h0.const_sub 1
    have := (Real.continuousAt_rpow_const 1 ((d : ℝ) / 2) (Or.inl one_ne_zero)).tendsto.comp h1
    simpa [Function.comp_def] using this
  have : Tendsto (fun r : ℝ => (1 - 1 / (r ^ 2 + 1)) ^ ((d : ℝ) / 2) / (d : ℝ)) atTop (𝓝 (1 / (d : ℝ))) :=
    by simpa using hlim.div_const (d : ℝ)
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  unfold radialPrimitive
  rw [key r hr]

theorem integral_radialProfile (hd : 0 < d) :
    ∫ r in Ioi (0 : ℝ), radialProfile d r = 1 / d := by
  have hder : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (radialPrimitive d) (radialProfile d x) x :=
    fun x _ => hasDerivAt_radialPrimitive hd x
  have hint : IntegrableOn (radialProfile d) (Ioi (0 : ℝ)) :=
    integrableOn_Ioi_deriv_of_nonneg' hder (fun x hx => radialProfile_nonneg x hx.out.le)
      (tendsto_radialPrimitive hd)
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hder hint (tendsto_radialPrimitive hd)]
  have : radialPrimitive d 0 = 0 := by
    simp [radialPrimitive, hd.ne']
  rw [this, sub_zero]

theorem integrableOn_radialProfile (hd : 0 < d) :
    IntegrableOn (radialProfile d) (Ioi (0 : ℝ)) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hasDerivAt_radialPrimitive hd x)
    (fun x hx => radialProfile_nonneg x hx.out.le) (tendsto_radialPrimitive hd)

theorem regDiv_one_eq (z : Vec d) :
    regDiv d 1 z = (d : ℝ) * newtonConst d * (vecEuclideanNorm z ^ 2 + 1) ^ (-((d : ℝ) / 2) - 1) := by
  unfold regDiv regCoef2
  rw [vecEuclideanNorm_sq]
  ring_nf

theorem integral_regDiv_one (hd : 0 < d) : ∫ z : Vec d, regDiv d 1 z = 1 := by
  have : NeZero d := ⟨hd.ne'⟩
  set g : HilbertVec d → ℝ := fun x =>
    (fun r : ℝ => (d : ℝ) * newtonConst d * (r ^ 2 + 1) ^ (-((d : ℝ) / 2) - 1)) ‖x‖ with hg
  have hcomp : ∀ z : Vec d, g (Internal.toHilbert z) = regDiv d 1 z := by
    intro z
    simp only [hg, Internal.toHilbert_apply, ← Vec.vecEuclideanNorm_eq_norm_toHilbertVec,
      regDiv_one_eq]
  have h1 : ∫ z : Vec d, regDiv d 1 z = ∫ x : HilbertVec d, g x := by
    rw [← Internal.measurePreserving_toHilbert.integral_comp
      (Internal.toHilbert : Vec d ≃L[ℝ] HilbertVec d).toHomeomorph.measurableEmbedding g]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => (hcomp z).symm)
  have hrank : Module.finrank ℝ (HilbertVec d) = d := by
    calc Module.finrank ℝ (HilbertVec d) = Module.finrank ℝ (Fin d → ℝ) :=
          (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).finrank_eq
      _ = d := by simp
  have h2 := integral_fun_norm_addHaar (volume : Measure (HilbertVec d))
    (fun r : ℝ => (d : ℝ) * newtonConst d * (r ^ 2 + 1) ^ (-((d : ℝ) / 2) - 1))
  rw [hrank] at h2
  rw [h1]
  refine h2.trans ?_
  have h3 : ∫ y in Ioi (0 : ℝ), y ^ (d - 1) •
      ((d : ℝ) * newtonConst d * (y ^ 2 + 1) ^ (-((d : ℝ) / 2) - 1)) =
      (d : ℝ) * newtonConst d * (1 / (d : ℝ)) := by
    rw [← integral_radialProfile hd, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [radialProfile, smul_eq_mul]
    ring
  rw [h3]
  simp only [Measure.real, nsmul_eq_mul, smul_eq_mul]
  rw [volume_ball_hilbert_eq_euclideanBall]
  have hB := volume_euclideanBall_toReal_pos (0 : Vec d) (R := 1) one_pos
  unfold newtonConst
  have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

theorem integrable_regDiv_one (hd : 0 < d) : Integrable (fun z : Vec d => regDiv d 1 z) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_regDiv_one hd]
  exact one_ne_zero

theorem regDiv_nonneg (ε : ℝ) (z : Vec d) : 0 ≤ regDiv d ε z := by
  unfold regDiv regCoef2
  have := vecNormSq_nonneg z
  have : 0 ≤ vecNormSq z + ε ^ 2 := by positivity
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    (mul_nonneg newtonConst_nonneg (Real.rpow_nonneg this _))

theorem regDiv_smul {ε : ℝ} (hε : 0 < ε) (v : Vec d) :
    regDiv d ε (ε • v) = (ε ^ d)⁻¹ * regDiv d 1 v := by
  have hq := vecNormSq_nonneg v
  have hs : 0 < vecNormSq v + 1 := by positivity
  have e1 : vecNormSq (ε • v) + ε ^ 2 = ε ^ 2 * (vecNormSq v + 1) := by
    rw [vecNormSq_smul]; ring
  have e2 : ε ^ 2 * (ε ^ 2) ^ (-((d : ℝ) / 2) - 1) = (ε ^ d)⁻¹ := by
    rw [mul_comm, ← Real.rpow_add_one (by positivity)]
    rw [show -((d : ℝ) / 2) - 1 + 1 = -((d : ℝ) / 2) by ring, Real.rpow_neg (by positivity),
      ← Real.rpow_natCast ε 2, ← Real.rpow_mul hε.le, ← Real.rpow_natCast ε d]
    congr 3
    push_cast; ring
  unfold regDiv regCoef2
  rw [e1, Real.mul_rpow (by positivity) hs.le, one_pow]
  calc (d : ℝ) * ε ^ 2 * (newtonConst d * ((ε ^ 2) ^ (-((d : ℝ) / 2) - 1) *
        (vecNormSq v + 1) ^ (-((d : ℝ) / 2) - 1)))
      = (d : ℝ) * (ε ^ 2 * (ε ^ 2) ^ (-((d : ℝ) / 2) - 1)) *
        (newtonConst d * (vecNormSq v + 1) ^ (-((d : ℝ) / 2) - 1)) := by ring
    _ = _ := by rw [e2]; ring

theorem integral_regDiv_conv {ε : ℝ} (hε : 0 < ε) (g : Vec d → ℝ) (x : Vec d) :
    ∫ y, regDiv d ε (x - y) * g y = ∫ v, regDiv d 1 v * g (x - ε • v) := by
  have ha : ∫ y, regDiv d ε (x - y) * g y = ∫ u, regDiv d ε u * g (x - u) := by
    rw [← integral_sub_left_eq_self (fun u => regDiv d ε u * g (x - u)) volume x]
    simp
  rw [ha]
  have hb := Measure.integral_comp_smul (volume : Measure (Vec d))
    (fun u => regDiv d ε u * g (x - u)) ε
  have hrank : Module.finrank ℝ (Vec d) = d := by simp
  rw [hrank, abs_of_pos (by positivity)] at hb
  have hεd : ε ^ d ≠ 0 := by positivity
  have hc : ∫ u, regDiv d ε u * g (x - u) = ε ^ d * ∫ v, regDiv d ε (ε • v) * g (x - ε • v) := by
    rw [hb, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hεd, one_mul]
  rw [hc, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [regDiv_smul hε]
  field_simp

theorem tendsto_integral_regDiv_conv (hd : 0 < d) {g : Vec d → ℝ} (hg : Continuous g) {C : ℝ}
    (hC : ∀ y, |g y| ≤ C) (x : Vec d) :
    Tendsto (fun ε : ℝ => ∫ y, regDiv d ε (x - y) * g y) (𝓝[>] 0) (𝓝 (g x)) := by
  have hint := integrable_regDiv_one hd
  have hlim : Tendsto (fun ε : ℝ => ∫ v, regDiv d 1 v * g (x - ε • v)) (𝓝[>] 0)
      (𝓝 (∫ v, regDiv d 1 v * g x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun v => C * regDiv d 1 v) ?_ ?_
      (hint.const_mul C) ?_
    · refine Filter.Eventually.of_forall fun ε => ?_
      have hc : Continuous (fun v : Vec d => g (x - ε • v)) :=
        hg.comp (by fun_prop)
      exact hint.aestronglyMeasurable.mul hc.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ε => Filter.Eventually.of_forall fun v => ?_
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (regDiv_nonneg _ _), mul_comm]
      exact mul_le_mul_of_nonneg_right (hC _) (regDiv_nonneg _ _)
    · refine Filter.Eventually.of_forall fun v => ?_
      have : Continuous (fun ε : ℝ => regDiv d 1 v * g (x - ε • v)) :=
        continuous_const.mul (hg.comp (by fun_prop))
      have h0 := this.tendsto 0
      simp only [zero_smul, sub_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
  rw [integral_mul_const, integral_regDiv_one hd, one_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_regDiv_conv hε g x).symm

end

end NewtonRepresentation

end PDE
