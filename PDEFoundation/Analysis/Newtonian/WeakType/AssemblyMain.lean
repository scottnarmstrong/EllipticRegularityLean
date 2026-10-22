module

public import PDEFoundation.Analysis.Newtonian.WeakType.AssemblyFinite
public import PDEFoundation.Analysis.Newtonian.WeakType.AssemblyLimit

/-!
# The weak-type estimate for `∇ u_F` given Calderón–Zygmund stopping cubes

For `F` smooth with compact support vanishing off the root box `I`, and stopping cubes `S` at
height `λ`, `|{|∇ u_F| > λ}| ≤ C(d, A) ‖F‖₁ / λ` where `A` is a Hölder constant of `∇E`.
-/

@[expose] public section

open BoxIntegral MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE.NewtonWeakType

noncomputable section

variable {d : ℕ} {I : Box (Fin d)} {F : Vec d → Vec d} {lam : ℝ}

theorem exists_vecNormSq_le {F : Vec d → Vec d} (hF : VBdd F) : ∃ M2 : ℝ, ∀ x, vecNormSq (F x) ≤ M2 := by
  choose C hC using fun i => (hF i).bdd
  refine ⟨∑ i, C i ^ 2, fun x => ?_⟩
  rw [vecNormSq_eq_sum_sq]
  exact Finset.sum_le_sum fun i _ => by
    have := hC i x
    nlinarith [abs_nonneg (F x i), sq_abs (F x i)]

theorem czDilateConst_ne_top (d : ℕ) : czDilateConst d ≠ ⊤ := by
  unfold czDilateConst
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (volume_euclideanBall_ne_top _ zero_le_one)

theorem lintegral_root_eq (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    (hFsupp : ∀ x, x ∉ (I : Set (Vec d)) → F x = 0) :
    ∫⁻ x in (I : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (F x)) =
      ENNReal.ofReal (∫ x, vecEuclideanNorm (F x)) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_vecEuclideanNorm_comp hF.continuous hFc)
    (Filter.Eventually.of_forall fun _ => vecEuclideanNorm_nonneg _)]
  refine setLIntegral_eq_of_support_subset ?_
  intro x hx
  by_contra hxI
  apply hx
  simp [hFsupp x hxI, vecEuclideanNorm, vecNormSq, vecDot]

theorem eventually_sqrt_mul_le (d : ℕ) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ a in 𝓝[>] (0 : ℝ), Real.sqrt d * a ≤ r := by
  have hpos : 0 < r / (Real.sqrt d + 1) := by positivity
  filter_upwards [Ioc_mem_nhdsGT hpos] with a ha
  have h1 : a ≤ r / (Real.sqrt d + 1) := ha.2
  rw [le_div_iff₀ (by positivity)] at h1
  nlinarith [Real.sqrt_nonneg d, ha.1]

theorem volume_gradient_gt_le_of_stopping (hd : 0 < d) {A : ℝ} (hA : 0 ≤ A)
    (hK : KernelHolder d newtonKernelJacobian A) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hFsupp : ∀ x, x ∉ (I : Set (Vec d)) → F x = 0)
    (S : CZStopping I F lam) :
    volume {x | lam < vecEuclideanNorm (classicalGradient (newtonPotential F) x)} ≤
      ENNReal.ofReal ((4 * 2 ^ d + 2 ^ d * (czDilateConst d).toReal +
        4 * (hormanderConst d * A * d)) * (∫ x, vecEuclideanNorm (F x)) / lam) := by
  have hlam := S.lam_pos
  have hv := vbdd_of_smooth hF hFc
  have hFi : ∀ i, Continuous fun x => F x i := fun i => (contDiff_pi.mp hF i).continuous
  have hFI : ∀ i, IntegrableOn (fun x => F x i) (I : Set (Vec d)) := fun i =>
    ((hFi i).integrable_of_hasCompactSupport (hasCompactSupport_apply hFc i)).integrableOn
  obtain ⟨M2, hM2⟩ := exists_vecNormSq_le hv
  have hM20 : 0 ≤ M2 := (vecNormSq_nonneg (F 0)).trans (hM2 0)
  set m : ℝ := ∫ x, vecEuclideanNorm (F x) with hm
  have hm0 : 0 ≤ m := integral_nonneg fun _ => vecEuclideanNorm_nonneg _
  have hL := lintegral_root_eq (I := I) hF hFc hFsupp
  rw [← hm] at hL
  have htot : ∑' k, volume (S.cube k : Set (Vec d)) ≠ ⊤ := by
    intro htop
    have h := S.tsum_volume_le
    rw [htop, hL, ENNReal.mul_top (by simpa using hlam)] at h
    exact ENNReal.ofReal_ne_top (top_le_iff.mp h)
  have htail := ENNReal.tendsto_tsum_compl_atTop_zero htot
  have hCd : czDilateConst d = ENNReal.ofReal (czDilateConst d).toReal :=
    (ENNReal.ofReal_toReal (czDilateConst_ne_top d)).symm
  set H : ℝ := hormanderConst d * A * d with hH
  have hH0 : 0 ≤ H := mul_nonneg (mul_nonneg (hormanderConst_nonneg d) hA) (Nat.cast_nonneg d)
  set Cd : ℝ := (czDilateConst d).toReal with hCdd
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set Kc : ℝ := (lam / 2)⁻¹ ^ 2 * (M2 + 1) with hKc
  have hKc0 : 0 < Kc := by positivity
  have hδ : 0 < (ε : ℝ) / Kc := by positivity
  obtain ⟨s, hs⟩ := (htail.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hδ))).exists
  have htailfin : (∑' k : {k // k ∉ s}, volume (S.cube k : Set (Vec d))) ≠ ⊤ :=
    ne_top_of_lt hs
  have htailr : (∑' k : {k // k ∉ s}, volume (S.cube k : Set (Vec d))).toReal < (ε : ℝ) / Kc :=
    (ENNReal.toReal_lt_of_lt_ofReal hs)
  have hlint := lintegral_vecNormSq_czTrunc_le (S := S) hF.continuous.measurable hFI hFsupp hM2 s
  rw [hL] at hlint
  set tl : ℝ≥0∞ := ∑' k : {k // k ∉ s}, volume (S.cube k : Set (Vec d)) with htl
  have hUne : ENNReal.ofReal (2 ^ d * lam) * ENNReal.ofReal m + ENNReal.ofReal M2 * tl ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top htailfin⟩
  have hmeasq : AEStronglyMeasurable (fun x => vecNormSq (czTrunc S s x)) volume := by
    simp_rw [vecNormSq_eq_sum_sq]
    exact (Finset.measurable_sum _ fun i _ => ((vbdd_czTrunc S hv s i).meas).pow_const 2).aestronglyMeasurable
  have hint : ∫ x, vecNormSq (czTrunc S s x) ≤ 2 ^ d * lam * m + M2 * tl.toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => vecNormSq_nonneg _)
      hmeasq]
    refine (ENNReal.toReal_mono hUne hlint).trans (le_of_eq ?_)
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top htailfin), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hm0, ENNReal.toReal_ofReal hM20]
  have hsa : ∀ᶠ a in 𝓝[>] (0 : ℝ), ∀ k ∈ s, Real.sqrt d * a ≤ czRadius S k :=
    (Filter.eventually_all_finset s).mpr fun k _ => eventually_sqrt_mul_le d (czRadius_pos S hd k)
  have hbd : ∀ᶠ a in 𝓝[>] (0 : ℝ), volume {x | lam < vecEuclideanNorm
      (classicalGradient (newtonPotential (mollVec a F)) x)} ≤
      ENNReal.ofReal ((lam / 2)⁻¹ ^ 2 * ∫ x, vecNormSq (czTrunc S s x)) +
        (volume (czExceptional S) +
          ENNReal.ofReal (lam / 2)⁻¹ * (ENNReal.ofReal H * (2 * ENNReal.ofReal m))) := by
    filter_upwards [self_mem_nhdsWithin, hsa] with a ha hsa'
    have := volume_gradient_mollVec_gt_le hd hA hK hv hFI s ha hsa'
    rwa [hL] at this
  have hlim := volume_gt_le_of_tendsto (Φ := fun a x => vecEuclideanNorm
      (classicalGradient (newtonPotential (mollVec a F)) x))
    (Φ₀ := fun x => vecEuclideanNorm (classicalGradient (newtonPotential F) x))
    (fun x => tendsto_vecEuclideanNorm_gradient_mollVec hd hF hFc x) hbd
  refine hlim.trans ?_
  -- arithmetic
  have hE := volume_czExceptional_le (S := S) hd
  rw [hL, hCd] at hE
  have h1 : (lam / 2)⁻¹ ^ 2 * ∫ x, vecNormSq (czTrunc S s x) ≤
      4 * 2 ^ d * m / lam + ε := by
    have hc : 0 ≤ (lam / 2)⁻¹ ^ 2 := by positivity
    have hM : M2 * tl.toReal ≤ (M2 + 1) * ((ε : ℝ) / Kc) :=
      mul_le_mul (by linarith) htailr.le ENNReal.toReal_nonneg (by linarith)
    calc (lam / 2)⁻¹ ^ 2 * ∫ x, vecNormSq (czTrunc S s x)
        ≤ (lam / 2)⁻¹ ^ 2 * (2 ^ d * lam * m + M2 * tl.toReal) :=
          mul_le_mul_of_nonneg_left hint hc
      _ ≤ (lam / 2)⁻¹ ^ 2 * (2 ^ d * lam * m) + (lam / 2)⁻¹ ^ 2 * ((M2 + 1) * ((ε : ℝ) / Kc)) := by
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hM) hc
      _ = 4 * 2 ^ d * m / lam + ε := by
          have : (lam / 2)⁻¹ ^ 2 * ((M2 + 1) * ((ε : ℝ) / Kc)) = ε := by
            rw [hKc]; field_simp
          rw [this]
          field_simp
          ring
  have h2 : volume (czExceptional S) ≤ ENNReal.ofReal (2 ^ d * Cd * m / lam) := by
    refine hE.trans (le_of_eq ?_)
    have hCd0 : 0 ≤ Cd := ENNReal.toReal_nonneg
    rw [← ENNReal.ofReal_mul hCd0, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have h3 : ENNReal.ofReal (lam / 2)⁻¹ * (ENNReal.ofReal H * (2 * ENNReal.ofReal m)) =
      ENNReal.ofReal (4 * H * m / lam) := by
    have : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    rw [this, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul hH0,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
    ring
  calc ENNReal.ofReal ((lam / 2)⁻¹ ^ 2 * ∫ x, vecNormSq (czTrunc S s x)) +
        (volume (czExceptional S) +
          ENNReal.ofReal (lam / 2)⁻¹ * (ENNReal.ofReal H * (2 * ENNReal.ofReal m)))
      ≤ ENNReal.ofReal (4 * 2 ^ d * m / lam + ε) +
        (ENNReal.ofReal (2 ^ d * Cd * m / lam) + ENNReal.ofReal (4 * H * m / lam)) := by
        rw [h3]
        exact add_le_add (ENNReal.ofReal_le_ofReal h1) (add_le_add h2 le_rfl)
    _ = ENNReal.ofReal (4 * 2 ^ d * m / lam + ε + (2 ^ d * Cd * m / lam + 4 * H * m / lam)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ = ENNReal.ofReal ((4 * 2 ^ d + 2 ^ d * Cd + 4 * H) * m / lam + ε) := by
        congr 1; ring
    _ ≤ ENNReal.ofReal ((4 * 2 ^ d + 2 ^ d * Cd + 4 * H) * m / lam) + ε := by
        refine (ENNReal.ofReal_add_le).trans ?_
        rw [ENNReal.ofReal_coe_nnreal]

end

end PDE.NewtonWeakType
