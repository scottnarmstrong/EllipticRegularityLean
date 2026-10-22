module

public import EllipticRegularity.Parabolic.Cauchy.Energy.Exhaustion
public import EllipticRegularity.Parabolic.WeakSlice.Product

public import Mathlib.Tactic.Ring

/-!
# Bounded smooth weights in the whole-space Cauchy energy identity

The exhaustion cutoff can be multiplied by a bounded smooth weight while
remaining an admissible compactly supported test. This is the starting point
for the weighted identity; subsequent limits remove the exhaustion cutoff.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Weights

open MeasureTheory Set Filter Topology

private theorem smoothWeightedSliceIntegral_tendsto {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u)
    (ξ : Vec d × ℝ → ℝ) (hξ : Continuous ξ)
    (B : ℝ) (_hB : 0 ≤ B) (hξbound : ∀ z, |ξ z| ≤ B)
    {t : ℝ} (ht : t ∈ Icc s T) :
    Tendsto (fun n : ℕ => ∫ x : Vec d,
      (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).toFun (x, t) ^ 2 *
        ξ (x, t) ^ 2 * u.toFun (x, t) ^ 2) atTop
      (𝓝 <| ∫ x : Vec d, ξ (x, t) ^ 2 * u.toFun (x, t) ^ 2) := by
  let F : ℕ → Vec d → ℝ := fun n x =>
    (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).toFun (x, t) ^ 2 *
      ξ (x, t) ^ 2 * u.toFun (x, t) ^ 2
  have hslice := PDE.Parabolic.Cauchy.Energy.cauchy_slice_square_integrable
    hsT ha f hf u hu ht
  have hxiSlice : Continuous (fun x : Vec d => ξ (x, t)) :=
    hξ.comp (continuous_id.prodMk continuous_const)
  have hmeas : ∀ n, AEStronglyMeasurable (F n) volume := by
    intro n
    have hη : Continuous (fun x : Vec d =>
        (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).toFun
          (x, t) ^ 2) :=
      (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).contDiff.continuous
        |>.comp (continuous_id.prodMk continuous_const) |>.pow 2
    exact (hη.aestronglyMeasurable.mul (hxiSlice.pow 2).aestronglyMeasurable).mul
      hslice.aestronglyMeasurable
  have hdomInt : Integrable (fun x : Vec d => B ^ 2 * u.toFun (x, t) ^ 2) volume :=
    hslice.const_mul _
  have hbound : ∀ n, ∀ᵐ x ∂volume, ‖F n x‖ ≤ B ^ 2 * u.toFun (x, t) ^ 2 := by
    intro n
    filter_upwards [] with x
    dsimp [F]
    have hη := PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff_nonneg_le_one
      s T ((n : ℝ) + 2) (by positivity) (x, t)
    have hηsq : (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).toFun
        (x, t) ^ 2 ≤ 1 := by
      dsimp [PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff]
      have hmul := mul_self_le_mul_self hη.1 hη.2
      simpa only [pow_two, one_mul, mul_one] using hmul
    have hξsq : ξ (x, t) ^ 2 ≤ B ^ 2 := by
      have hpow := pow_le_pow_left₀ (abs_nonneg (ξ (x, t)))
        (hξbound (x, t)) 2
      simpa only [sq_abs] using hpow
    have hηnn : 0 ≤ (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).toFun
        (x, t) ^ 2 := sq_nonneg _
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg hηnn (sq_nonneg _)) (sq_nonneg _))]
    have hξu : ξ (x, t) ^ 2 * u.toFun (x, t) ^ 2 ≤
        B ^ 2 * u.toFun (x, t) ^ 2 :=
      mul_le_mul_of_nonneg_right hξsq (sq_nonneg _)
    have hηξu :
        (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).toFun
            (x, t) ^ 2 * (ξ (x, t) ^ 2 * u.toFun (x, t) ^ 2) ≤
          B ^ 2 * u.toFun (x, t) ^ 2 := by
      calc
        _ ≤ 1 * (ξ (x, t) ^ 2 * u.toFun (x, t) ^ 2) :=
          mul_le_mul_of_nonneg_right hηsq
            (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        _ ≤ 1 * (B ^ 2 * u.toFun (x, t) ^ 2) :=
          mul_le_mul_of_nonneg_left hξu (by norm_num)
        _ = _ := by ring
    simpa [mul_assoc] using hηξu
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun n => F n x) atTop
      (𝓝 (ξ (x, t) ^ 2 * u.toFun (x, t) ^ 2)) := by
    filter_upwards [] with x
    apply tendsto_const_nhds.congr'
    filter_upwards [PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff_eventually_one
      s T x t] with n hn
    simp [F, hn]
  simpa only [F] using
    (tendsto_integral_of_dominated_convergence
      (fun x : Vec d => B ^ 2 * u.toFun (x, t) ^ 2) hmeas hdomInt hbound hlim)

private theorem parTimeDeriv_continuous_smooth {d : ℕ}
    {ξ : Vec d × ℝ → ℝ} (hξ : ContDiff ℝ 1 ξ) :
    Continuous (fun z => parTimeDeriv ξ z) := by
  unfold parTimeDeriv
  exact (hξ.continuous_fderiv (by norm_num)).clm_apply continuous_const

private theorem parSpaceGrad_continuous_smooth {d : ℕ}
    {ξ : Vec d × ℝ → ℝ} (hξ : ContDiff ℝ 1 ξ) :
    Continuous (fun z => parSpaceGrad ξ z) := by
  apply continuous_pi
  intro i
  unfold parSpaceGrad
  exact (hξ.continuous_fderiv (by norm_num)).clm_apply continuous_const

private theorem smoothWeightedTimeIntegral_tendsto {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (_hsT : s < T)
    (_ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (ξ : Vec d × ℝ → ℝ) (hξ : ContDiff ℝ 1 ξ)
    (B Bt : ℝ) (hB : 0 ≤ B) (_hBt : 0 ≤ Bt)
    (hξbound : ∀ z, |ξ z| ≤ B)
    (hξtbound : ∀ z, |parTimeDeriv ξ z| ≤ Bt)
    {t : ℝ} (_hst : s < t) (ht : t ∈ Icc s T) :
    Tendsto (fun n : ℕ =>
      ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).toFun z ^ 2 *
          u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z) atTop
      (𝓝 <| ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z) := by
  let Q : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s t
  let F : ℕ → Vec d × ℝ → ℝ := fun n z =>
    ((PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).toFun z ^ 2 *
      u.toFun z ^ 2) * (ξ z * parTimeDeriv ξ z)
  have hQsub : Q ⊆ (univ : Set (Vec d)) ×ˢ Icc s T := by
    intro z hz
    exact ⟨hz.1, ⟨hz.2.1.le, hz.2.2.trans ht.2⟩⟩
  have hQmeasure : volume.restrict Q ≤
      volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s T) :=
    Measure.restrict_mono hQsub le_rfl
  have huSq : Integrable (fun z : Vec d × ℝ => u.toFun z ^ 2)
      (volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s T)) := u.memL2.integrable_sq
  have huSqQ : Integrable (fun z : Vec d × ℝ => u.toFun z ^ 2)
      (volume.restrict Q) := huSq.mono_measure hQmeasure
  have hxiDtCont : Continuous (fun z => ξ z * parTimeDeriv ξ z) :=
    hξ.continuous.mul (parTimeDeriv_continuous_smooth hξ)
  have hmeas : ∀ n, AEStronglyMeasurable (F n) (volume.restrict Q) := by
    intro n
    have hη : Continuous (fun z : Vec d × ℝ =>
        (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).toFun z ^ 2) :=
      (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).contDiff.continuous.pow 2
    exact (hη.aestronglyMeasurable.mul huSqQ.aestronglyMeasurable).mul
      hxiDtCont.aestronglyMeasurable
  have hdomInt : Integrable
      (fun z : Vec d × ℝ => (B * Bt) * u.toFun z ^ 2)
      (volume.restrict Q) := huSqQ.const_mul _
  have hbound : ∀ n, ∀ᵐ z ∂(volume.restrict Q),
      ‖F n z‖ ≤ (B * Bt) * u.toFun z ^ 2 := by
    intro n
    filter_upwards [] with z
    dsimp [F]
    have hη := PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff_nonneg_le_one
      s T ((n : ℝ) + 2) (by positivity) z
    have hηsq : (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).toFun z ^ 2 ≤ 1 := by
      dsimp [PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff]
      have hmul := mul_self_le_mul_self hη.1 hη.2
      simpa only [pow_two, one_mul, mul_one] using hmul
    have hprod : |ξ z * parTimeDeriv ξ z| ≤ B * Bt := by
      calc
        |ξ z * parTimeDeriv ξ z| = |ξ z| * |parTimeDeriv ξ z| := abs_mul _ _
        _ ≤ B * Bt := mul_le_mul (hξbound z) (hξtbound z)
          (abs_nonneg _) hB
    have hu2 : 0 ≤ u.toFun z ^ 2 := sq_nonneg _
    have hη0 : 0 ≤ (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).toFun z ^ 2 :=
      sq_nonneg _
    rw [abs_mul, abs_of_nonneg (mul_nonneg hη0 hu2)]
    calc
      (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).toFun z ^ 2 *
          u.toFun z ^ 2 * |ξ z * parTimeDeriv ξ z| ≤
        1 * u.toFun z ^ 2 * (B * Bt) := by gcongr
      _ = (B * Bt) * u.toFun z ^ 2 := by ring
  have hlim : ∀ᵐ z ∂(volume.restrict Q), Tendsto (fun n => F n z) atTop
      (𝓝 (u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z)) := by
    filter_upwards [] with z
    apply tendsto_const_nhds.congr'
    filter_upwards [PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff_eventually_one
      s T z.1 z.2] with n hn
    simp [F, hn, mul_assoc]
  simpa [F, Q, mul_assoc] using tendsto_integral_of_dominated_convergence
    (fun z : Vec d × ℝ => (B * Bt) * u.toFun z ^ 2) hmeas hdomInt hbound hlim

private theorem smoothWeightedBulkIntegral_tendsto {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (ξ : Vec d × ℝ → ℝ) (hξ : ContDiff ℝ 1 ξ)
    (B Bg : ℝ) (hB : 0 ≤ B) (_hBg : 0 ≤ Bg)
    (hξbound : ∀ z, |ξ z| ≤ B)
    (hgradbound : ∀ z, vecEuclideanNorm (parSpaceGrad ξ z) ≤ Bg)
    {t : ℝ} (_hst : s < t) (ht : t ∈ Icc s T) :
    Tendsto (fun n : ℕ =>
      ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).toFun z ^ 2 *
          (ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
            2 * ξ z * u.toFun z *
              vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z))) atTop
      (𝓝 <| ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
          2 * ξ z * u.toFun z *
            vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z)) ∧
      (∀ n : ℕ, IntegrableOn
        (fun z => (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).toFun z ^ 2 *
          (ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
            2 * ξ z * u.toFun z *
              vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z)))
        ((univ : Set (Vec d)) ×ˢ Ioc s t)) ∧
      IntegrableOn
        (fun z => ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
          2 * ξ z * u.toFun z *
            vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z))
        ((univ : Set (Vec d)) ×ˢ Ioc s t) := by
  let Q : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s t
  let E : Vec d × ℝ → ℝ := PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u
  let J : Vec d × ℝ → ℝ := fun z =>
    vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z)
  let M : Vec d × ℝ → ℝ := PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u
  let F : ℕ → Vec d × ℝ → ℝ := fun n z =>
    (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).toFun z ^ 2 *
      (ξ z ^ 2 * E z + 2 * ξ z * u.toFun z * J z)
  have hQsub : Q ⊆ (univ : Set (Vec d)) ×ˢ Icc s T := by
    intro z hz
    exact ⟨hz.1, ⟨hz.2.1.le, hz.2.2.trans ht.2⟩⟩
  have hQmeasure : volume.restrict Q ≤
      volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s T) :=
    Measure.restrict_mono hQsub le_rfl
  have hEInt : IntegrableOn E Q := by
    dsimp [E, Q]
    exact PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity_integrable_Ioc ha u ht
  have hMInt : IntegrableOn M Q := by
    dsimp [M, Q]
    exact PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant_integrable_Ioc ha u ht
  have hDomInt : IntegrableOn (fun z => B ^ 2 * |E z| +
      (2 * B * Bg) * M z) Q := by
    exact (hEInt.norm.const_mul (B ^ 2)).add (hMInt.const_mul (2 * B * Bg))
  have hgradCont : Continuous (fun z => parSpaceGrad ξ z) :=
    parSpaceGrad_continuous_smooth hξ
  have hJMeas : AEStronglyMeasurable J (volume.restrict Q) := by
    change AEStronglyMeasurable (fun z : Vec d × ℝ =>
      ∑ i : Fin d, PDE.Parabolic.Energy.flux a u z i * parSpaceGrad ξ z i)
      (volume.restrict Q)
    have hsum := Finset.aestronglyMeasurable_sum Finset.univ fun i _ =>
      ((PDE.Parabolic.Energy.flux_memLp ha u i).mono_measure hQmeasure).aestronglyMeasurable.mul
        (((continuous_apply i).comp hgradCont).aestronglyMeasurable)
    convert hsum using 1; ext z; simp
  have hEAMeas : AEStronglyMeasurable E (volume.restrict Q) := hEInt.aestronglyMeasurable
  have hxi2Cont : Continuous (fun z => ξ z ^ 2) := hξ.continuous.pow 2
  have huAMeas : AEStronglyMeasurable u.toFun (volume.restrict Q) :=
    u.memL2.aestronglyMeasurable.mono_measure hQmeasure
  have hmeas : ∀ n, AEStronglyMeasurable (F n) (volume.restrict Q) := by
    intro n
    have hη : Continuous (fun z : Vec d × ℝ =>
        (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).toFun z ^ 2) :=
      (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).contDiff.continuous.pow 2
    have hinner : AEStronglyMeasurable
        (fun z => ξ z ^ 2 * E z + 2 * ξ z * u.toFun z * J z)
        (volume.restrict Q) := by
      have hcross : AEStronglyMeasurable
          (fun z => ξ z * u.toFun z * J z) (volume.restrict Q) :=
        (hξ.continuous.aestronglyMeasurable.mul huAMeas).mul hJMeas
      have hcross' : AEStronglyMeasurable
          (fun z => 2 * ξ z * u.toFun z * J z) (volume.restrict Q) := by
        convert hcross.const_mul 2 using 1; ext z; ring
      exact (hxi2Cont.aestronglyMeasurable.mul hEAMeas).add hcross'
    exact hη.aestronglyMeasurable.mul hinner
  have hlim : ∀ᵐ z ∂(volume.restrict Q), Tendsto (fun n => F n z) atTop
      (𝓝 (ξ z ^ 2 * E z + 2 * ξ z * u.toFun z * J z)) := by
    filter_upwards [] with z
    apply tendsto_const_nhds.congr'
    filter_upwards [PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff_eventually_one
      s T z.1 z.2] with n hn
    simp [F, hn]
  have hbound : ∀ n, ∀ᵐ z ∂(volume.restrict Q), ‖F n z‖ ≤
      B ^ 2 * |E z| + (2 * B * Bg) * M z := by
    intro n
    filter_upwards [] with z
    dsimp [F, E, J, M]
    have hη := PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff_nonneg_le_one
      s T ((n : ℝ) + 2) (by positivity) z
    have hηsq : (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).toFun z ^ 2 ≤ 1 := by
      dsimp [PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff]
      have hmul := mul_self_le_mul_self hη.1 hη.2
      simpa only [pow_two, one_mul, mul_one] using hmul
    have hEbound : |ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z| ≤
        B ^ 2 * |PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [sq_abs] using
          pow_le_pow_left₀ (abs_nonneg (ξ z)) (hξbound z) 2) (abs_nonneg _)
    let w := matVecMul (a z) (u.grad z)
    let p := parSpaceGrad ξ z
    have hdot : |vecDot w p| ≤
        (∑ i : Fin d, |w i|) * Bg := by
      calc
        |vecDot w p| ≤ vecEuclideanNorm w * vecEuclideanNorm p :=
          abs_vecDot_le_vecEuclideanNorm_mul w p
        _ ≤ (∑ i : Fin d, |w i|) * Bg := by
          exact mul_le_mul (vecEuclideanNorm_le_sum_abs w) (hgradbound z)
            (vecEuclideanNorm_nonneg p) (Finset.sum_nonneg fun i _ => abs_nonneg _)
    have hcross : |2 * ξ z * u.toFun z * vecDot w p| ≤
        (2 * B * Bg) * (|u.toFun z| * ∑ i : Fin d, |w i|) := by
      have hcoef : |2 * ξ z * u.toFun z| = 2 * |ξ z| * |u.toFun z| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
      have hfirst : 2 * |ξ z| * |u.toFun z| ≤ 2 * B * |u.toFun z| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hξbound z) (by norm_num)) (abs_nonneg _)
      calc
        |2 * ξ z * u.toFun z * vecDot w p| =
            (2 * |ξ z| * |u.toFun z|) * |vecDot w p| := by
              rw [abs_mul, hcoef]
        _ ≤ (2 * B * |u.toFun z|) * ((∑ i : Fin d, |w i|) * Bg) := by
          apply mul_le_mul
          · exact hfirst
          · exact hdot
          · exact abs_nonneg _
          · positivity
        _ = (2 * B * Bg) * (|u.toFun z| * ∑ i : Fin d, |w i|) := by ring
    have hinner : |ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
        2 * ξ z * u.toFun z * vecDot w p| ≤
        B ^ 2 * |PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z| +
          (2 * B * Bg) * (|u.toFun z| * ∑ i : Fin d, |w i|) := by
      calc
        _ ≤ |ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z| +
            |2 * ξ z * u.toFun z * vecDot w p| := abs_add_le _ _
        _ ≤ _ := add_le_add hEbound hcross
    have hη0 : 0 ≤ (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).toFun z ^ 2 :=
      sq_nonneg _
    rw [abs_mul, abs_of_nonneg hη0]
    calc
      (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).toFun z ^ 2 *
          |ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
            2 * ξ z * u.toFun z * vecDot w p| ≤
        1 * (B ^ 2 * |PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z| +
          (2 * B * Bg) * (|u.toFun z| * ∑ i : Fin d, |w i|)) := by
            exact mul_le_mul hηsq hinner (abs_nonneg _) (by positivity)
      _ = B ^ 2 * |PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z| +
          (2 * B * Bg) * (|u.toFun z| * ∑ i : Fin d, |w i|) := by ring
  have hFnInt : ∀ n, IntegrableOn (F n) Q := by
    intro n
    change Integrable (F n) (volume.restrict Q)
    apply hDomInt.mono' (hmeas n)
    filter_upwards [hbound n] with z hz
    simpa [F, E, J, M, PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant] using hz
  have hlimitMeas : AEStronglyMeasurable
      (fun z => ξ z ^ 2 * E z + 2 * ξ z * u.toFun z * J z)
      (volume.restrict Q) := by
    have hcross : AEStronglyMeasurable
        (fun z => 2 * ξ z * u.toFun z * J z) (volume.restrict Q) := by
      have hbase : AEStronglyMeasurable
          (fun z => ξ z * u.toFun z * J z) (volume.restrict Q) :=
        (hξ.continuous.aestronglyMeasurable.mono_measure hQmeasure).mul huAMeas |>.mul hJMeas
      convert hbase.const_mul 2 using 1; ext z; ring
    exact (hxi2Cont.aestronglyMeasurable.mono_measure hQmeasure).mul hEAMeas |>.add hcross
  have hlimitInt : IntegrableOn
      (fun z => ξ z ^ 2 * E z + 2 * ξ z * u.toFun z * J z) Q := by
    change Integrable (fun z => ξ z ^ 2 * E z + 2 * ξ z * u.toFun z * J z)
      (volume.restrict Q)
    apply hDomInt.mono' hlimitMeas
    filter_upwards [] with z
    let w := matVecMul (a z) (u.grad z)
    let p := parSpaceGrad ξ z
    have hEbound : |ξ z ^ 2 * E z| ≤ B ^ 2 * |E z| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [sq_abs] using
          pow_le_pow_left₀ (abs_nonneg (ξ z)) (hξbound z) 2) (abs_nonneg _)
    have hdot : |vecDot w p| ≤ (∑ i : Fin d, |w i|) * Bg := by
      calc
        |vecDot w p| ≤ vecEuclideanNorm w * vecEuclideanNorm p :=
          abs_vecDot_le_vecEuclideanNorm_mul w p
        _ ≤ (∑ i : Fin d, |w i|) * Bg :=
          mul_le_mul (vecEuclideanNorm_le_sum_abs w) (hgradbound z)
            (vecEuclideanNorm_nonneg p)
            (Finset.sum_nonneg fun i _ => abs_nonneg _)
    have hcross : |2 * ξ z * u.toFun z * vecDot w p| ≤
        (2 * B * Bg) * (|u.toFun z| * ∑ i : Fin d, |w i|) := by
      have hcoef : |2 * ξ z * u.toFun z| = 2 * |ξ z| * |u.toFun z| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
      have hfirst : 2 * |ξ z| * |u.toFun z| ≤ 2 * B * |u.toFun z| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hξbound z) (by norm_num)) (abs_nonneg _)
      calc
        |2 * ξ z * u.toFun z * vecDot w p| =
            (2 * |ξ z| * |u.toFun z|) * |vecDot w p| := by rw [abs_mul, hcoef]
        _ ≤ (2 * B * |u.toFun z|) * ((∑ i : Fin d, |w i|) * Bg) := by
          apply mul_le_mul
          · exact hfirst
          · exact hdot
          · exact abs_nonneg _
          · positivity
        _ = (2 * B * Bg) * (|u.toFun z| * ∑ i : Fin d, |w i|) := by ring
    have htotal : |ξ z ^ 2 * E z + 2 * ξ z * u.toFun z * vecDot w p| ≤
        B ^ 2 * |E z| + (2 * B * Bg) * (|u.toFun z| * ∑ i : Fin d, |w i|) := by
      calc
        _ ≤ |ξ z ^ 2 * E z| + |2 * ξ z * u.toFun z * vecDot w p| := abs_add_le _ _
        _ ≤ _ := add_le_add hEbound hcross
    simpa [E, J, M, PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant,
      PDE.Parabolic.Energy.flux, w, matVecMul,
      Real.norm_eq_abs] using htotal
  refine ⟨?_, ?_⟩
  · simpa [F, Q] using tendsto_integral_of_dominated_convergence
      (fun z : Vec d × ℝ => B ^ 2 * |E z| + (2 * B * Bg) * M z)
      hmeas hDomInt hbound hlim
  · refine ⟨?_, ?_⟩
    · intro n
      simpa [F, Q] using hFnInt n
    · simpa [E, J, M, Q] using hlimitInt

/-- Multiply the compact spatial exhaustion cutoff by a smooth, possibly
noncompact weight and retain the relative compact support required by
`ParCutoff`. -/
noncomputable def cauchySmoothWeightedCutoff {d : ℕ} (s T R : ℝ) (hR : 0 < R)
    (ξ : Vec d × ℝ → ℝ) (hξ : ContDiff ℝ 1 ξ) :
    ParCutoff (univ : Set (Vec d)) (Icc s T) := by
  let η := PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff (d := d) s T R hR
  refine ⟨fun z => η.toFun z * ξ z, η.contDiff.mul hξ, ?_⟩
  obtain ⟨Z, hZcompact, hZsubset, hηzero⟩ := η.compact_support
  refine ⟨Z, hZcompact, hZsubset, ?_⟩
  intro z hz hnot
  have hη : η.toFun z = 0 := hηzero z hz (fun hzZ => hnot hzZ)
  simp [hη]

/-- Product rule for the time derivative of smooth space-time weights. -/
private theorem parTimeDeriv_mul_smooth {d : ℕ} {ξ χ : Vec d × ℝ → ℝ}
    (hξ : ContDiff ℝ 1 ξ) (hχ : ContDiff ℝ 1 χ) (z : Vec d × ℝ) :
    parTimeDeriv (fun w => ξ w * χ w) z =
      parTimeDeriv ξ z * χ z + ξ z * parTimeDeriv χ z := by
  have hprod := ((hξ.differentiable (by norm_num) z).hasFDerivAt).mul
    ((hχ.differentiable (by norm_num) z).hasFDerivAt)
  change (fderiv ℝ (ξ * χ) z) (0, 1) = _
  rw [hprod.fderiv]
  simp only [add_apply, smul_apply, parTimeDeriv]
  ring

/-- Product rule for the spatial gradient of smooth space-time weights. -/
private theorem parSpaceGrad_mul_smooth {d : ℕ} {ξ χ : Vec d × ℝ → ℝ}
    (hξ : ContDiff ℝ 1 ξ) (hχ : ContDiff ℝ 1 χ) (z : Vec d × ℝ) :
    parSpaceGrad (fun w => ξ w * χ w) z =
      χ z • parSpaceGrad ξ z + ξ z • parSpaceGrad χ z := by
  ext i
  have hprod := ((hξ.differentiable (by norm_num) z).hasFDerivAt).mul
    ((hχ.differentiable (by norm_num) z).hasFDerivAt)
  change (fderiv ℝ (ξ * χ) z) (basisVec i, 0) = _
  rw [hprod.fderiv]
  simp only [add_apply, smul_apply, parSpaceGrad, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The compact-cutoff weighted energy identity, expanded into the bulk,
weight-gradient, and exhaustion-gradient terms. -/
theorem cauchySmoothWeighted_energy_identity {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u)
    (ξ : Vec d × ℝ → ℝ) (hξ : ContDiff ℝ 1 ξ)
    (R : ℝ) (hR : 0 < R) {t : ℝ} (ht : t ∈ Icc s T) (hst : s < t) :
    ((1 / 2 : ℝ) * ∫ x : Vec d,
        (PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff s T R hR).toFun (x, t) ^ 2 *
          ξ (x, t) ^ 2 * u.toFun (x, t) ^ 2) -
      (1 / 2 : ℝ) * ∫ x : Vec d,
        (PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff s T R hR).toFun (x, s) ^ 2 *
          ξ (x, s) ^ 2 * u.toFun (x, s) ^ 2 =
    (∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        (PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff s T R hR).toFun z ^ 2 *
          u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z) -
      ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        (PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff s T R hR).toFun z ^ 2 *
            (ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
              2 * ξ z * u.toFun z *
                vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z)) +
          ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyCutoffCrossFlux a u R hR z := by
  let η := PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff (d := d) s T R hR
  let φ := cauchySmoothWeightedCutoff s T R hR ξ hξ
  have hlocal := PDE.Parabolic.energy_identity d lam Lam univ isOpen_univ
    (Icc s T) Set.ordConnected_Icc a ha u hu.1 φ
  obtain ⟨_, _, hslab⟩ := hlocal
  obtain ⟨htime, hflux, hid⟩ := hslab s t ⟨le_rfl, hsT.le⟩ ht hst
  have htimePoint (z : Vec d × ℝ) :
      u.toFun z ^ 2 * φ.toFun z * parTimeDeriv φ.toFun z =
        η.toFun z ^ 2 * u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z := by
    dsimp [φ, cauchySmoothWeightedCutoff]
    rw [parTimeDeriv_mul_smooth η.contDiff hξ]
    have hηt := PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff_timeDeriv_eq_zero
      s T R hR z.1 z.2
    rw [hηt]
    ring
  have htimeInt :
      (∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        u.toFun z ^ 2 * φ.toFun z * parTimeDeriv φ.toFun z) =
      ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        η.toFun z ^ 2 * u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z := by
    apply integral_congr_ae
    exact ae_of_all _ htimePoint
  have hfluxPoint (z : Vec d × ℝ) :
      vecDot (matVecMul (a z) (u.grad z))
          (φ.toFun z ^ 2 • u.grad z +
            (2 * φ.toFun z * u.toFun z) • parSpaceGrad φ.toFun z) =
        η.toFun z ^ 2 *
            (ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
              2 * ξ z * u.toFun z *
                vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z)) +
          ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyCutoffCrossFlux a u R hR z := by
    dsimp [φ, cauchySmoothWeightedCutoff]
    rw [parSpaceGrad_mul_smooth η.contDiff hξ]
    simp only [PDE.ParabCaccioppoli.vecDot_add_right',
      PDE.ParabCaccioppoli.vecDot_smul_right']
    rw [vecDot_comm (matVecMul (a z) (u.grad z)) (u.grad z)]
    dsimp [PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity,
      PDE.Parabolic.Cauchy.Energy.cauchyCutoffCrossFlux]
    ring
  have hfluxInt :
      (∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        vecDot (matVecMul (a z) (u.grad z))
          (φ.toFun z ^ 2 • u.grad z +
            (2 * φ.toFun z * u.toFun z) • parSpaceGrad φ.toFun z)) =
      ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        η.toFun z ^ 2 *
            (ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
              2 * ξ z * u.toFun z *
                vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z)) +
          ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyCutoffCrossFlux a u R hR z := by
    apply integral_congr_ae
    exact ae_of_all _ hfluxPoint
  have hendpoint :
      (∫ x : Vec d, φ.toFun (x, t) ^ 2 * u.toFun (x, t) ^ 2) =
        ∫ x : Vec d, η.toFun (x, t) ^ 2 * ξ (x, t) ^ 2 * u.toFun (x, t) ^ 2 := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp [φ, cauchySmoothWeightedCutoff]
      ring
  have hendpoint0 :
      (∫ x : Vec d, φ.toFun (x, s) ^ 2 * u.toFun (x, s) ^ 2) =
        ∫ x : Vec d, η.toFun (x, s) ^ 2 * ξ (x, s) ^ 2 * u.toFun (x, s) ^ 2 := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp [φ, cauchySmoothWeightedCutoff]
      ring
  rw [htimeInt, hfluxInt] at hid
  simp only [setIntegral_univ] at hid
  rw [hendpoint, hendpoint0] at hid
  exact hid

/-- Pointwise estimate for the spatial exhaustion error in the energy
identity. -/
private theorem cauchyCutoffCrossFlux_norm_le {d : ℕ} {a : ParCoeffField d}
    {s T : ℝ} (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (R : ℝ) (hR : 0 < R) (z : Vec d × ℝ) :
    ‖PDE.Parabolic.Cauchy.Energy.cauchyCutoffCrossFlux a u R hR z‖ ≤
      (64 / R) * PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u z := by
  let η := (PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff s T R hR).toFun z
  let p := parSpaceGrad (PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff s T R hR).toFun z
  let F := PDE.Parabolic.Energy.flux a u z
  have hη := PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff_nonneg_le_one s T R hR z
  have hηabs : |η| ≤ 1 := abs_le.mpr ⟨by dsimp [η]; linarith [hη.1], by
    dsimp [η]; linarith [hη.2]⟩
  have hp : vecEuclideanNorm p ≤ 32 / R :=
    PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff_spatialGrad_bound s T R hR z.1 z.2
  have hF : vecEuclideanNorm F ≤ ∑ i : Fin d, |F i| := vecEuclideanNorm_le_sum_abs F
  have hpn : 0 ≤ vecEuclideanNorm p := vecEuclideanNorm_nonneg p
  have hFn : 0 ≤ vecEuclideanNorm F := vecEuclideanNorm_nonneg F
  have hdot := abs_vecDot_le_vecEuclideanNorm_mul F p
  change ‖(2 * η * u.toFun z) * vecDot F p‖ ≤
    (64 / R) * (|u.toFun z| * ∑ i : Fin d, |F i|)
  simp only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
  calc
    2 * |η| * |u.toFun z| * |vecDot F p| ≤
        2 * 1 * |u.toFun z| * (vecEuclideanNorm F * vecEuclideanNorm p) := by
          gcongr
    _ ≤ 2 * 1 * |u.toFun z| *
        ((∑ i : Fin d, |F i|) * (32 / R)) := by
          have hsum : 0 ≤ ∑ i : Fin d, |F i| := Finset.sum_nonneg fun i _ => abs_nonneg _
          have hRnonneg : 0 ≤ (32 : ℝ) / R := by positivity
          gcongr
    _ = (64 / R) * (|u.toFun z| * ∑ i : Fin d, |F i|) := by ring

/-- The weighted exhaustion-gradient term vanishes for bounded smooth
weights, so the compact-cutoff identity passes to the whole space. -/
private theorem smoothWeightedCrossCutoff_integral_tendsto {d : ℕ}
    {lam Lam : ℝ} {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsParabolicWeakSolution a univ (Icc s T) u)
    (ξ : Vec d × ℝ → ℝ) (hξ : Continuous ξ)
    (B : ℝ) (_hB : 0 ≤ B) (hξbound : ∀ z, |ξ z| ≤ B)
    {t : ℝ} (ht : t ∈ Icc s T) (hst : s < t) :
    Tendsto (fun n : ℕ =>
      ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyCutoffCrossFlux a u
          ((n : ℝ) + 2) (by positivity) z) atTop (𝓝 0) ∧
      (∀ n : ℕ, IntegrableOn
        (fun z => ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyCutoffCrossFlux a u
          ((n : ℝ) + 2) (by positivity) z) ((univ : Set (Vec d)) ×ˢ Ioc s t)) := by
  let Q : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s t
  let M : Vec d × ℝ → ℝ := PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u
  have hM : IntegrableOn M Q := by
    dsimp [M, Q]
    exact PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant_integrable_Ioc ha u ht
  have hMnn : ∀ z, 0 ≤ M z := by
    intro z
    dsimp [M, PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant]
    positivity
  have hξsqbound : ∀ z, ‖ξ z ^ 2‖ ≤ B ^ 2 := by
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using
      pow_le_pow_left₀ (abs_nonneg (ξ z)) (hξbound z) 2
  have hxi2cont : Continuous (fun z => ξ z ^ 2) := hξ.pow 2
  have hcross : ∀ n : ℕ, IntegrableOn
      (fun z => ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyCutoffCrossFlux a u
        ((n : ℝ) + 2) (by positivity) z) Q := by
    intro n
    have hc := PDE.Parabolic.Cauchy.Energy.cauchy_cutoff_cross_integrable
      hsT ha u hu ((n : ℝ) + 2) (by positivity) ht hst
    have hq : IntegrableOn
        (PDE.Parabolic.Cauchy.Energy.cauchyCutoffCrossFlux a u
          ((n : ℝ) + 2) (by positivity)) Q := by
      simpa [Q] using hc
    have hξ2meas : AEStronglyMeasurable (fun z => ξ z ^ 2) (volume.restrict Q) :=
      hxi2cont.aestronglyMeasurable.mono_measure Measure.restrict_le_self
    have hmul := hq.bdd_mul hξ2meas
      (c := B ^ 2) (Filter.Eventually.of_forall fun z => hξsqbound z)
    change Integrable (fun z => ξ z ^ 2 *
      PDE.Parabolic.Cauchy.Energy.cauchyCutoffCrossFlux a u
        ((n : ℝ) + 2) (by positivity) z) (volume.restrict Q)
    simpa [mul_comm] using hmul
  have hdom (n : ℕ) : IntegrableOn
      (fun z => B ^ 2 * (64 / ((n : ℝ) + 2)) * M z) Q := by
    change Integrable (fun z => (B ^ 2 * (64 / ((n : ℝ) + 2))) * M z)
      (volume.restrict Q)
    exact hM.const_mul _
  have hnormbound (n : ℕ) :
      ∫ z in Q, ‖ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyCutoffCrossFlux a u
          ((n : ℝ) + 2) (by positivity) z‖ ≤
        B ^ 2 * (64 / ((n : ℝ) + 2)) * ∫ z in Q, M z := by
    have hbound : ∀ z, ‖ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyCutoffCrossFlux
        a u ((n : ℝ) + 2) (by positivity) z‖ ≤
          B ^ 2 * (64 / ((n : ℝ) + 2)) * M z := by
      intro z
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
      have hξsq : ξ z ^ 2 ≤ B ^ 2 := by
        simpa only [sq_abs] using
          pow_le_pow_left₀ (abs_nonneg (ξ z)) (hξbound z) 2
      have hpt := cauchyCutoffCrossFlux_norm_le (a := a) u
        ((n : ℝ) + 2) (by positivity) z
      calc
        ξ z ^ 2 * |PDE.Parabolic.Cauchy.Energy.cauchyCutoffCrossFlux a u
            ((n : ℝ) + 2) (by positivity) z| ≤
          B ^ 2 * ‖PDE.Parabolic.Cauchy.Energy.cauchyCutoffCrossFlux a u
            ((n : ℝ) + 2) (by positivity) z‖ := by
              rw [Real.norm_eq_abs]
              exact mul_le_mul_of_nonneg_right hξsq (abs_nonneg _)
        _ ≤ B ^ 2 * ((64 / ((n : ℝ) + 2)) * M z) :=
          mul_le_mul_of_nonneg_left hpt (sq_nonneg B)
        _ = B ^ 2 * (64 / ((n : ℝ) + 2)) * M z := by ring
    have hmono := integral_mono ((hcross n).norm) (hdom n) hbound
    calc
      ∫ z in Q, ‖ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyCutoffCrossFlux a u
          ((n : ℝ) + 2) (by positivity) z‖ ≤
        ∫ z in Q, B ^ 2 * (64 / ((n : ℝ) + 2)) * M z := hmono
      _ = B ^ 2 * (64 / ((n : ℝ) + 2)) * ∫ z in Q, M z := by
        rw [integral_const_mul]
  have hnorm : ∀ n : ℕ,
      ‖∫ z in Q, ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyCutoffCrossFlux a u
          ((n : ℝ) + 2) (by positivity) z‖ ≤
        B ^ 2 * (64 / ((n : ℝ) + 2)) * ∫ z in Q, M z := by
    intro n
    calc
      ‖∫ z in Q, ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyCutoffCrossFlux a u
          ((n : ℝ) + 2) (by positivity) z‖ ≤
        ∫ z in Q, ‖ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyCutoffCrossFlux a u
          ((n : ℝ) + 2) (by positivity) z‖ :=
            norm_integral_le_integral_norm (μ := volume.restrict Q)
              (fun z => ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyCutoffCrossFlux a u
                ((n : ℝ) + 2) (by positivity) z)
      _ ≤ B ^ 2 * (64 / ((n : ℝ) + 2)) * ∫ z in Q, M z := hnormbound n
  have hscale : Tendsto (fun n : ℕ => B ^ 2 * (64 / ((n : ℝ) + 2)) *
      ∫ z in Q, M z) atTop (𝓝 0) := by
    have hn : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
    have hinv := tendsto_inv_atTop_zero.comp hn
    have hscale' := hinv.const_mul (B ^ 2 * 64 * ∫ z in Q, M z)
    convert hscale' using 1
    · ext n
      simp only [Function.comp_apply]
      ring_nf
    · simp
  have hnormzero : Tendsto (fun n : ℕ =>
      ‖∫ z in Q, ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyCutoffCrossFlux a u
        ((n : ℝ) + 2) (by positivity) z‖) atTop (𝓝 0) := by
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => hnorm n) hscale
  have hactual : Tendsto (fun n : ℕ =>
      ∫ z in Q, ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyCutoffCrossFlux a u
        ((n : ℝ) + 2) (by positivity) z) atTop (𝓝 0) := by
    apply (tendsto_iff_norm_sub_tendsto_zero).2
    simpa using hnormzero
  refine ⟨?_, ?_⟩
  · simpa [Q] using hactual
  · exact hcross

/-- Whole-space weighted energy identity for bounded smooth weights. The
spatial exhaustion error is removed using the flux majorant. -/
theorem cauchySmoothWeighted_energy_identity_global {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u)
    (ξ : Vec d × ℝ → ℝ) (hξ : ContDiff ℝ 1 ξ)
    (B Bt Bg : ℝ) (hB : 0 ≤ B) (hBt : 0 ≤ Bt) (hBg : 0 ≤ Bg)
    (hξbound : ∀ z, |ξ z| ≤ B)
    (hξtbound : ∀ z, |parTimeDeriv ξ z| ≤ Bt)
    (hgradbound : ∀ z, vecEuclideanNorm (parSpaceGrad ξ z) ≤ Bg)
    {t : ℝ} (ht : t ∈ Icc s T) (hst : s < t) :
    ((1 / 2 : ℝ) * ∫ x : Vec d, ξ (x, t) ^ 2 * u.toFun (x, t) ^ 2) -
        (1 / 2 : ℝ) * ∫ x : Vec d, ξ (x, s) ^ 2 * u.toFun (x, s) ^ 2 =
      (∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z) -
      ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
          2 * ξ z * u.toFun z *
            vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z) := by
  let Q : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s t
  have htT : t ∈ Icc s T := ht
  have ht0 : (s : ℝ) ∈ Icc s T := ⟨le_rfl, hsT.le⟩
  have hleftT : Tendsto (fun n : ℕ =>
      (1 / 2 : ℝ) * ∫ x : Vec d,
        (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).toFun (x, t) ^ 2 *
          ξ (x, t) ^ 2 * u.toFun (x, t) ^ 2) atTop
      (𝓝 ((1 / 2 : ℝ) * ∫ x : Vec d, ξ (x, t) ^ 2 * u.toFun (x, t) ^ 2)) := by
    exact (smoothWeightedSliceIntegral_tendsto hsT ha f hf u hu ξ hξ.continuous B hB
      hξbound htT).const_mul (1 / 2)
  have hleftS : Tendsto (fun n : ℕ =>
      (1 / 2 : ℝ) * ∫ x : Vec d,
        (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).toFun (x, s) ^ 2 *
          ξ (x, s) ^ 2 * u.toFun (x, s) ^ 2) atTop
      (𝓝 ((1 / 2 : ℝ) * ∫ x : Vec d, ξ (x, s) ^ 2 * u.toFun (x, s) ^ 2)) := by
    exact (smoothWeightedSliceIntegral_tendsto hsT ha f hf u hu ξ hξ.continuous B hB
      hξbound ht0).const_mul (1 / 2)
  have htime := smoothWeightedTimeIntegral_tendsto hsT ha u ξ hξ B Bt hB hBt
    hξbound hξtbound hst ht
  obtain ⟨hbulk, ⟨hbulkInt, hbulkLimitInt⟩⟩ :=
    smoothWeightedBulkIntegral_tendsto ha u ξ hξ B Bg hB hBg
    hξbound hgradbound hst ht
  obtain ⟨hcross, hcrossInt⟩ := smoothWeightedCrossCutoff_integral_tendsto hsT ha u hu.1 ξ
    hξ.continuous B hB hξbound ht hst
  let L : ℕ → ℝ := fun n =>
    ((1 / 2 : ℝ) * (∫ x : Vec d,
      (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).toFun (x, t) ^ 2 *
        ξ (x, t) ^ 2 * u.toFun (x, t) ^ 2)) -
    ((1 / 2 : ℝ) * (∫ x : Vec d,
      (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).toFun (x, s) ^ 2 *
        ξ (x, s) ^ 2 * u.toFun (x, s) ^ 2))
  let Bulk : ℕ → Vec d × ℝ → ℝ := fun n z =>
    (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).toFun z ^ 2 *
      (ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
        2 * ξ z * u.toFun z *
          vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z))
  let Cross : ℕ → Vec d × ℝ → ℝ := fun n z =>
    ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyCutoffCrossFlux a u
      ((n : ℝ) + 2) (by positivity) z
  let R : ℕ → ℝ := fun n =>
    (∫ z in Q, (PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff s T n).toFun z ^ 2 *
      u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z) -
    ((∫ z in Q, Bulk n z) + (∫ z in Q, Cross n z))
  have hL : Tendsto L atTop (𝓝 <|
      ((1 / 2 : ℝ) * (∫ x : Vec d, ξ (x, t) ^ 2 * u.toFun (x, t) ^ 2)) -
        ((1 / 2 : ℝ) * (∫ x : Vec d, ξ (x, s) ^ 2 * u.toFun (x, s) ^ 2))) := by
    simpa [L] using hleftT.sub hleftS
  have hR : Tendsto R atTop (𝓝 <|
      (∫ z in Q, u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z) -
        (∫ z in Q, ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
          2 * ξ z * u.toFun z *
            vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z))) := by
    have hsum := hbulk.add hcross
    have hdiff := htime.sub hsum
    simpa [R, Bulk, Cross, Q, sub_eq_add_neg, add_assoc] using hdiff
  have heq : ∀ n, L n = R n := by
    intro n
    have hcut := cauchySmoothWeighted_energy_identity hsT ha f u hu ξ hξ
      ((n : ℝ) + 2) (by positivity) ht hst
    have hadd := integral_add (hbulkInt n) (hcrossInt n)
    dsimp [L, R, Bulk, Cross, Q]
    rw [← hadd]
    simpa [PDE.Parabolic.Cauchy.Energy.cauchyExhaustionCutoff,
      cauchySmoothWeightedCutoff] using hcut
  have hlimL : Tendsto L atTop (𝓝 <|
      ((1 / 2 : ℝ) * (∫ x : Vec d, ξ (x, t) ^ 2 * u.toFun (x, t) ^ 2)) -
        ((1 / 2 : ℝ) * (∫ x : Vec d, ξ (x, s) ^ 2 * u.toFun (x, s) ^ 2))) := hL
  have hlimR : Tendsto R atTop (𝓝 <|
      (∫ z in Q, u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z) -
        (∫ z in Q, ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
          2 * ξ z * u.toFun z *
            vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z))) := hR
  have hsame := hlimL.congr' (Filter.Eventually.of_forall fun n => heq n)
  have hvalue := tendsto_nhds_unique hsame hlimR
  simpa [Q, sub_eq_add_neg, add_assoc] using hvalue

/-- Integrating a pointwise weighted energy inequality retains its
dissipation term on the whole space. -/
theorem cauchySmoothWeighted_energy_dissipation {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u)
    (ξ : Vec d × ℝ → ℝ) (hξ : ContDiff ℝ 1 ξ)
    (B Bt Bg : ℝ) (hB : 0 ≤ B) (hBt : 0 ≤ Bt) (hBg : 0 ≤ Bg)
    (hξbound : ∀ z, |ξ z| ≤ B)
    (hξtbound : ∀ z, |parTimeDeriv ξ z| ≤ Bt)
    (hgradbound : ∀ z, vecEuclideanNorm (parSpaceGrad ξ z) ≤ Bg)
    {t : ℝ} (ht : t ∈ Icc s T) (hst : s < t)
    (loss : Vec d × ℝ → ℝ)
    (hloss : IntegrableOn loss ((univ : Set (Vec d)) ×ˢ Ioc s t))
    (hdensity : ∀ᵐ z ∂(volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s t)),
      u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z ≤
        ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
          2 * ξ z * u.toFun z *
            vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z) - loss z) :
    (∫ x : Vec d, ξ (x, t) ^ 2 * u.toFun (x, t) ^ 2) +
        2 * ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t, loss z ≤
      ∫ x : Vec d, ξ (x, s) ^ 2 * f x ^ 2 := by
  let Q : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s t
  have hQsub : Q ⊆ (univ : Set (Vec d)) ×ˢ Icc s T := by
    intro z hz
    exact ⟨hz.1, ⟨hz.2.1.le, hz.2.2.trans ht.2⟩⟩
  have hQmeasure : volume.restrict Q ≤
      volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s T) :=
    Measure.restrict_mono hQsub le_rfl
  have huSqQ : Integrable (fun z : Vec d × ℝ => u.toFun z ^ 2)
      (volume.restrict Q) := u.memL2.integrable_sq |>.mono_measure hQmeasure
  have hcoefCont : Continuous (fun z => ξ z * parTimeDeriv ξ z) :=
    hξ.continuous.mul (parTimeDeriv_continuous_smooth hξ)
  have hcoefMeas : AEStronglyMeasurable (fun z => ξ z * parTimeDeriv ξ z)
      (volume.restrict Q) :=
    hcoefCont.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  have hcoefBound : ∀ᵐ z ∂(volume.restrict Q),
      ‖ξ z * parTimeDeriv ξ z‖ ≤ B * Bt := by
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hξbound z) (hξtbound z) (abs_nonneg _) hB
  have htimeInt : IntegrableOn
      (fun z => u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z) Q := by
    change Integrable
      (fun z => (u.toFun z ^ 2 * ξ z) * parTimeDeriv ξ z) (volume.restrict Q)
    have hmul := huSqQ.mul_bdd hcoefMeas (c := B * Bt) hcoefBound
    simpa [mul_assoc] using hmul
  obtain ⟨_, ⟨_, hbulkInt⟩⟩ :=
    smoothWeightedBulkIntegral_tendsto ha u ξ hξ B Bg hB hBg
      hξbound hgradbound hst ht
  have hdenInt : IntegrableOn
      (fun z => u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z -
        (ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
          2 * ξ z * u.toFun z *
            vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z))) Q :=
    htimeInt.sub hbulkInt
  have hdenLossInt : IntegrableOn
      (fun z => u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z -
        (ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
          2 * ξ z * u.toFun z *
            vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z)) + loss z) Q :=
    hdenInt.add hloss
  have hdennonpos : ∫ z in Q,
      u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z -
        (ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
          2 * ξ z * u.toFun z *
            vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z)) + loss z ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [hdensity] with z hz
    have hz' : u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z -
        (ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
          2 * ξ z * u.toFun z *
            vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z) - loss z) ≤ 0 :=
      sub_nonpos.mpr hz
    convert hz' using 1; ring
  have hsubInt :
      (∫ z in Q, u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z) -
        (∫ z in Q, ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
          2 * ξ z * u.toFun z *
            vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z)) =
        ∫ z in Q,
          u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z -
            (ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
              2 * ξ z * u.toFun z *
                vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z)) := by
    exact (integral_sub htimeInt hbulkInt).symm
  have hsubLossInt :
      (∫ z in Q, u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z) -
        (∫ z in Q, ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
          2 * ξ z * u.toFun z *
            vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z)) +
          ∫ z in Q, loss z =
        ∫ z in Q,
          (u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z -
          (ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
            2 * ξ z * u.toFun z *
              vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z))) + loss z := by
    calc
      _ = (∫ z in Q, u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z -
          (ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
            2 * ξ z * u.toFun z *
              vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z))) +
            ∫ z in Q, loss z := by
              rw [← integral_sub htimeInt hbulkInt]
      _ = ∫ z in Q,
          (u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z -
            (ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
              2 * ξ z * u.toFun z *
                vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z))) + loss z :=
            (integral_add hdenInt hloss).symm
  have hid := cauchySmoothWeighted_energy_identity_global hsT ha f hf u hu ξ hξ
    B Bt Bg hB hBt hBg hξbound hξtbound hgradbound ht hst
  have hinit : ∀ᵐ x : Vec d, u.toFun (x, s) = f x := hu.2
  have hslice : ∫ x : Vec d, ξ (x, s) ^ 2 * u.toFun (x, s) ^ 2 =
      ∫ x : Vec d, ξ (x, s) ^ 2 * f x ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hinit] with x hx
    rw [hx]
  have hhalf :
      (((1 / 2 : ℝ) * ∫ x : Vec d, ξ (x, t) ^ 2 * u.toFun (x, t) ^ 2) -
        (1 / 2 : ℝ) * ∫ x : Vec d, ξ (x, s) ^ 2 * f x ^ 2) +
          ∫ z in Q, loss z ≤ 0 := by
    have hbase :
        ((1 / 2 : ℝ) * ∫ x : Vec d, ξ (x, t) ^ 2 * u.toFun (x, t) ^ 2) -
          (1 / 2 : ℝ) * ∫ x : Vec d, ξ (x, s) ^ 2 * f x ^ 2 =
        (∫ z in Q, u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z) -
          ∫ z in Q, ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
            2 * ξ z * u.toFun z *
              vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z) := by
      have hs := congrArg (fun v : ℝ =>
        ((1 / 2 : ℝ) * ∫ x : Vec d, ξ (x, t) ^ 2 * u.toFun (x, t) ^ 2) -
          (1 / 2 : ℝ) * v) hslice
      linarith [hid, hs]
    calc
      _ = (∫ z in Q, u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z) -
          (∫ z in Q, ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
            2 * ξ z * u.toFun z *
              vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z)) +
            ∫ z in Q, loss z := by
                simpa only [sub_eq_add_neg, add_assoc] using
                  congrArg (fun v : ℝ => v + ∫ z in Q, loss z) hbase
      _ = ∫ z in Q,
          (u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z -
            (ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
              2 * ξ z * u.toFun z *
                vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z))) + loss z :=
          hsubLossInt
      _ ≤ 0 := hdennonpos
  linarith

/-- If the weighted energy density is nonpositive almost everywhere, the
whole-space weighted square integral is nonincreasing. -/
theorem cauchySmoothWeighted_energy_le {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u)
    (ξ : Vec d × ℝ → ℝ) (hξ : ContDiff ℝ 1 ξ)
    (B Bt Bg : ℝ) (hB : 0 ≤ B) (hBt : 0 ≤ Bt) (hBg : 0 ≤ Bg)
    (hξbound : ∀ z, |ξ z| ≤ B)
    (hξtbound : ∀ z, |parTimeDeriv ξ z| ≤ Bt)
    (hgradbound : ∀ z, vecEuclideanNorm (parSpaceGrad ξ z) ≤ Bg)
    {t : ℝ} (ht : t ∈ Icc s T) (hst : s < t)
    (hdensity : ∀ᵐ z ∂(volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s t)),
      u.toFun z ^ 2 * ξ z * parTimeDeriv ξ z ≤
        ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
          2 * ξ z * u.toFun z *
            vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ξ z)) :
    ∫ x : Vec d, ξ (x, t) ^ 2 * u.toFun (x, t) ^ 2 ≤
      ∫ x : Vec d, ξ (x, s) ^ 2 * f x ^ 2 := by
  have hmain := cauchySmoothWeighted_energy_dissipation hsT ha f hf u hu ξ hξ
    B Bt Bg hB hBt hBg hξbound hξtbound hgradbound ht hst (fun _ => 0)
    (show IntegrableOn (fun _ : Vec d × ℝ => (0 : ℝ))
      ((univ : Set (Vec d)) ×ˢ Ioc s t) from integrableOn_zero)
    (by simpa using hdensity)
  simpa using hmain

end PDE.Parabolic.Cauchy.Weights
