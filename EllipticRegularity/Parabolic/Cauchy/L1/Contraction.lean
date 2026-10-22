module

public import EllipticRegularity.Parabolic.Cauchy.L1.CauchyL1

@[expose] public section

namespace PDE.Parabolic.Cauchy.L1

open MeasureTheory Set Filter Topology

/-- Whole-space `L¹` contraction, proved from smooth convex entropy cutoffs. -/
private theorem cauchyL1_slice_lintegral_bound {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) {t : ℝ} (ht : t ∈ Icc s T) :
    ∫⁻ x : Vec d, ‖u.toFun (x, t)‖ₑ ≤ ENNReal.ofReal (∫ x : Vec d, |f x|) := by
  let δn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let Rn : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ 2
  let G : ℕ → Vec d → ℝ := fun n x =>
    (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff (Rn n) (by positivity)).toFun x *
      cauchyAbsEntropy (δn n) (u.toFun (x, t))
  let A : ℝ := ∫ x : Vec d, |f x|
  let M : ℝ := ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s T,
      PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u z
  let B : ℕ → ENNReal := fun n => ENNReal.ofReal (A + (512 / ((n : ℝ) + 1)) * M)
  have hGint : ∀ n, Integrable (G n) volume := by
    intro n
    let R : ℝ := Rn n
    have hR : 0 < R := by dsimp [R, Rn]; positivity
    let K : Set (Vec d) := euclideanClosedBall 0 (2 * R)
    have hKcompact : IsCompact K := isCompact_euclideanClosedBall 0 (by positivity)
    have hKmeas : MeasurableSet K := measurableSet_euclideanClosedBall 0 (2 * R)
    have hKfinite : IsFiniteMeasure (volume.restrict K) := ⟨by
      rw [Measure.restrict_apply_univ]
      exact hKcompact.measure_lt_top⟩
    let ξ : Vec d → ℝ := (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).toFun
    have hξmeas : AEStronglyMeasurable ξ (volume.restrict K) :=
      (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).smooth.continuous.aestronglyMeasurable
    have hξbound : ∀ᵐ x ∂(volume.restrict K), ‖ξ x‖ ≤ 1 := by
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [
        (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).nonneg x],
        (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).le_one x⟩
    have hδ : 0 < δn n := by dsimp [δn]; positivity
    have hzero : cauchyAbsEntropy (δn n) 0 = 0 := cauchyAbsEntropy_zero _
    obtain ⟨C, hLip⟩ := cauchyAbsEntropy_lipschitz hδ
    have hFmem : MemLp (fun x : Vec d => cauchyAbsEntropy (δn n) (u.toFun (x, t)))
        2 (volume.restrict K) :=
      hLip.comp_memLp hzero (u.sliceL2loc t ht K hKcompact (subset_univ _))
    have hGon : IntegrableOn (G n) K := by
      dsimp [G, R, Rn, ξ]
      exact (hFmem.integrable one_le_two).bdd_mul hξmeas (c := 1) hξbound |>.congr
        (Eventually.of_forall fun _ => rfl)
    have hGind : Integrable (K.indicator (G n)) volume := hGon.integrable_indicator hKmeas
    have hGeq : G n = K.indicator (G n) := by
      funext x
      by_cases hx : x ∈ K
      · simp [hx]
      · have hx' : x ∉ euclideanClosedBall 0 (2 * R) := by simpa [K] using hx
        have hz := PDE.Parabolic.Cauchy.L1.cauchySpatialCutoff_zero_outside_closedBall R hR hx'
        simp [G, R, Rn, hx, hz]
    rw [hGeq]
    exact hGind
  have hGnonneg : ∀ n, 0 ≤ᵐ[volume] G n := by
    intro n
    filter_upwards [] with x
    apply mul_nonneg
    · exact (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff (Rn n) (by positivity)).nonneg x
    · exact cauchyAbsEntropy_nonneg (by dsimp [δn]; positivity) _
  have hGintEq (n : ℕ) : ∫ x : Vec d, G n x =
      PDE.Parabolic.Cauchy.L1.cauchyAbsMoment (δn n) (Rn n) (by positivity) u t := by
    let R : ℝ := Rn n
    let K : Set (Vec d) := euclideanClosedBall 0 (2 * R)
    have hKmeas : MeasurableSet K := measurableSet_euclideanClosedBall 0 (2 * R)
    have hGeq : G n = K.indicator (G n) := by
      funext x
      by_cases hx : x ∈ K
      · simp [hx]
      · have hx' : x ∉ euclideanClosedBall 0 (2 * R) := by simpa [K] using hx
        have hz := PDE.Parabolic.Cauchy.L1.cauchySpatialCutoff_zero_outside_closedBall
          R (by dsimp [R, Rn]; positivity) hx'
        simp [G, R, Rn, hx, hz]
    rw [hGeq, integral_indicator hKmeas]
    rfl
  have hbound (n : ℕ) : ∫⁻ x : Vec d, ‖G n x‖ₑ ≤ B n := by
    have hnonneg := hGnonneg n
    have hnormEq : (fun x : Vec d => ‖G n x‖ₑ) =ᵐ[volume]
        fun x => ENNReal.ofReal (G n x) := by
      filter_upwards [hnonneg] with x hx
      simp [Real.enorm_eq_ofReal hx]
    rw [lintegral_congr_ae hnormEq,
      ← ofReal_integral_eq_lintegral_ofReal (hGint n) hnonneg]
    have hδ : 0 < δn n := by dsimp [δn]; positivity
    have hR : 0 < Rn n := by dsimp [Rn]; positivity
    have hmoment := PDE.Parabolic.Cauchy.L1.cauchyAbsMoment_upper_bound
      hsT ha f hf2 hf1 u hu (δn n) (Rn n) hδ hR ht
    have hcoef : 512 / (δn n * Rn n) = 512 / ((n : ℝ) + 1) := by
      dsimp [δn, Rn]
      field_simp
    have hmoment' : ∫ x : Vec d, G n x ≤ A +
        (512 / ((n : ℝ) + 1)) * M := by
      rw [hGintEq]
      simpa [A, M, hcoef] using hmoment
    exact ENNReal.ofReal_le_ofReal (by simpa [B] using hmoment')
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    apply setIntegral_nonneg_of_ae_restrict
    filter_upwards [] with z
    apply mul_nonneg (abs_nonneg _)
    exact Finset.sum_nonneg fun i _ => abs_nonneg _
  have hAn : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg_of_ae (ae_of_all _ fun x => abs_nonneg (f x))
  have hBn : Tendsto B atTop (𝓝 (ENNReal.ofReal A)) := by
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hden
    have herr : Tendsto (fun n : ℕ => (512 / ((n : ℝ) + 1)) * M) atTop (𝓝 0) := by
      have hrew : (fun n : ℕ => (512 / ((n : ℝ) + 1)) * M) =
          (fun n : ℕ => (512 : ℝ) * (((n : ℝ) + 1)⁻¹) * M) := by
        funext n
        field_simp
      rw [hrew]
      simpa [mul_assoc, mul_left_comm, mul_comm] using hinv.const_mul (512 * M)
    have hreal : Tendsto (fun n : ℕ => A + (512 / ((n : ℝ) + 1)) * M)
        atTop (𝓝 A) := by
      have hconst : Tendsto (fun _ : ℕ => A) atTop (𝓝 A) := tendsto_const_nhds
      simpa using hconst.add herr
    change Tendsto (fun n : ℕ => ENNReal.ofReal (A +
      (512 / ((n : ℝ) + 1)) * M)) atTop (𝓝 (ENNReal.ofReal A))
    exact ENNReal.tendsto_ofReal hreal
  have hliminfBound : liminf (fun n => ∫⁻ x : Vec d, ‖G n x‖ₑ) atTop ≤
      ENNReal.ofReal A := by
    calc
      liminf (fun n => ∫⁻ x : Vec d, ‖G n x‖ₑ) atTop ≤ liminf B atTop :=
        liminf_le_liminf (Filter.Eventually.of_forall fun n => hbound n)
      _ = ENNReal.ofReal A := hBn.liminf_eq
  have hGtoU : ∀ x : Vec d,
      Tendsto (fun n : ℕ => G n x) atTop (𝓝 (|u.toFun (x, t)|)) := by
    intro x
    have hcut : ∀ᶠ n : ℕ in atTop,
        (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff (Rn n) (by positivity)).toFun x = 1 := by
      obtain ⟨N, hN⟩ := exists_nat_gt (vecEuclideanNorm x)
      filter_upwards [eventually_ge_atTop N] with n hn
      have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hbase : vecEuclideanNorm x < (n : ℝ) + 1 := by linarith
      have hsq : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
      have hball : x ∈ euclideanBall 0 (Rn n) := by
        apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
        rw [sub_zero]
        exact lt_of_lt_of_le hbase hsq
      exact (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff (Rn n)
        (by positivity)).eq_one_on_inner x hball
    have hGevent : ∀ᶠ n : ℕ in atTop,
        G n x = cauchyAbsEntropy (δn n) (u.toFun (x, t)) := by
      filter_upwards [hcut] with n hn
      simp [G, hn]
    have hEnt := cauchyAbsEntropy_tendsto_abs (u.toFun (x, t))
    exact hEnt.congr' (hGevent.mono fun _ h => h.symm)
  have hnormTendsto (x : Vec d) :
      Tendsto (fun n : ℕ => ‖G n x‖ₑ) atTop (𝓝 ‖u.toFun (x, t)‖ₑ) := by
    have habs : Tendsto (fun n : ℕ => |G n x|) atTop (𝓝 |u.toFun (x, t)|) := by
      have hcomp := continuous_abs.continuousAt.tendsto.comp (hGtoU x)
      change Tendsto (fun n : ℕ => abs (G n x)) atTop
        (𝓝 (abs (abs (u.toFun (x, t))))) at hcomp
      simpa only [abs_abs] using hcomp
    have hreal := ENNReal.tendsto_ofReal habs
    have hsource : (fun n : ℕ => ‖G n x‖ₑ) =
        fun n => ENNReal.ofReal |G n x| := by
      funext n
      exact Real.enorm_eq_ofReal_abs _
    have htarget : ‖u.toFun (x, t)‖ₑ = ENNReal.ofReal |u.toFun (x, t)| :=
      Real.enorm_eq_ofReal_abs _
    rw [hsource, htarget]
    exact hreal
  have hliminfPoint (x : Vec d) :
      liminf (fun n : ℕ => ‖G n x‖ₑ) atTop = ‖u.toFun (x, t)‖ₑ :=
    (hnormTendsto x).liminf_eq
  have hFatou : ∫⁻ x : Vec d, ‖u.toFun (x, t)‖ₑ ≤
      liminf (fun n => ∫⁻ x : Vec d, ‖G n x‖ₑ) atTop := by
    calc
      _ = ∫⁻ x : Vec d, liminf (fun n : ℕ => ‖G n x‖ₑ) atTop := by
        apply lintegral_congr
        intro x
        exact (hliminfPoint x).symm
      _ ≤ liminf (fun n => ∫⁻ x : Vec d, ‖G n x‖ₑ) atTop :=
        lintegral_liminf_le' (fun n =>
          ((hGint n).aestronglyMeasurable.aemeasurable).enorm)
  exact hFatou.trans hliminfBound

theorem cauchyL1Contraction (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d)
    (s T : ℝ) (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) (t : ℝ) (ht : t ∈ Icc s T) :
    Integrable (parSlice u.toFun t) volume ∧
      eLpNorm (parSlice u.toFun t) 1 volume ≤ eLpNorm f 1 volume := by
  have hmeas := PDE.Parabolic.Cauchy.L1.cauchyL1_slice_aestronglyMeasurable u ht
  have hnormBound := cauchyL1_slice_lintegral_bound hsT ha f hf1 hf2 u hu ht
  have hfinite : ∫⁻ x : Vec d, ‖parSlice u.toFun t x‖ₑ < ⊤ := by
    calc
      _ ≤ ENNReal.ofReal (∫ x : Vec d, |f x|) := by simpa only [parSlice] using hnormBound
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hint : Integrable (parSlice u.toFun t) volume :=
    ⟨hmeas, (hasFiniteIntegral_iff_enorm).2 hfinite⟩
  have hfNorm : eLpNorm f 1 volume = ENNReal.ofReal (∫ x : Vec d, |f x|) := by
    rw [eLpNorm_one_eq_lintegral_enorm hf1.aestronglyMeasurable]
    rw [lintegral_congr_ae]
    · rw [← ofReal_integral_eq_lintegral_ofReal hf1.norm
        (ae_of_all _ fun x : Vec d => abs_nonneg (f x))]
      congr 1
    · filter_upwards [] with x
      simp [Real.enorm_eq_ofReal_abs]
  refine ⟨hint, ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm hmeas]
  exact hnormBound.trans_eq hfNorm.symm

end PDE.Parabolic.Cauchy.L1
