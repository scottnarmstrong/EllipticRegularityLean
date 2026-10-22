module

public import EllipticRegularity.Ch4.GreenDecay.DecayDGNFull
public import EllipticRegularity.Ch4.GreenDecay.Average
public import PDEFoundation.PDE.DGNM.Scaling
public import HarmonicStatements.Pointwise
public import PDEFoundation.PDE.HarmonicWeylRepresentative

/-!
# Interior Lipschitz estimate for weakly harmonic functions on convex sets

If `u ∈ H¹(E)` is weakly harmonic and `D ⊆ E` is convex with `B_σ(y) ⊆ E` for every `y ∈ D`, then `u` has a
smooth representative `g = harmonicMollify u (σ/4)` on `D` with
`|g y - g y'| ≤ K₀ σ⁻¹ M |y - y'|`, where `M` bounds the normalized `L²` deviations of `u` on the balls
`B_σ(y)`, `y ∈ D` (proof of Corollary 4.37, Step 2, with the canonical Weyl representative
replacing the gluing of local representatives).
-/

@[expose] public section

open scoped ENNReal Convolution

namespace PDE.Ch4GreenDecay

open MeasureTheory PDE

noncomputable section

variable {d : ℕ}

/-- The harmonic mollification at a point only sees the values of `u` in the `δ`-ball. -/
theorem harmonicMollify_restrict_eq {U U' : Set (Vec d)} (hUU' : U' ⊆ U) (u : H1Function U)
    (hU' : IsOpen U') {δ : ℝ} (hδ : 0 < δ) {x : Vec d} (hx : euclideanBall x δ ⊆ U') :
    harmonicMollify (u.restrict hU' hUU') δ x = harmonicMollify u δ x := by
  unfold harmonicMollify
  rw [convolution_def, convolution_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ tsupport (harmonicKernelScaled (d := d) δ)
  · have hball : x - t ∈ euclideanBall x δ := by
      have := harmonicKernelScaled_tsupport_subset (d := d) hδ ht
      rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hδ] at this ⊢
      have h : x - t - x = -t := by abel
      rw [h, vecEuclideanNorm_neg]
      simpa using this
    have h1 : x - t ∈ U' := hx hball
    have h2 : x - t ∈ U := hUU' h1
    simp only [ContinuousLinearMap.lsmul_apply]
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
    rfl
  · have : harmonicKernelScaled (d := d) δ t = 0 := image_eq_zero_of_notMem_tsupport ht
    simp [this]

/-- **The mollification is a representative near `y₀`.** -/
theorem harmonicMollify_ae_eq_ball (hd : 0 < d) {E : Set (Vec d)} (hE : IsOpen E)
    (u : H1Function E)
    (hsol : IsWeakDivergenceFormSolutionOn (fun _ : Vec d => (1 : Mat d)) E u 0 0)
    {σ : ℝ} (hσ : 0 < σ) {y₀ : Vec d} (hball : euclideanBall y₀ σ ⊆ E) :
    harmonicMollify u (σ / 4) =ᵐ[volumeOn (euclideanBall y₀ (σ / 2))] u.toFun := by
  have hsol' := DGNM.solutionOn_restrict hsol hE (isOpen_euclideanBall y₀ σ) hball
  obtain ⟨v, -, -, hvae, hvmol⟩ :=
    exists_harmonicWeylRepresentative hd hσ (u.restrict (isOpen_euclideanBall y₀ σ) hball) hsol'
  have hsub : euclideanBall y₀ (σ / 2) ⊆ euclideanBall y₀ σ :=
    euclideanBall_mono (by positivity) (by linarith)
  have h1 : ∀ᵐ y ∂volumeOn (euclideanBall y₀ (σ / 2)), v y = u.toFun y :=
    ae_restrict_of_ae_restrict_of_subset hsub hvae
  have hmem : ∀ᵐ y ∂volumeOn (euclideanBall y₀ (σ / 2)), y ∈ euclideanBall y₀ (σ / 2) :=
    (ae_restrict_iff' (measurableSet_euclideanBall _ _)).2
      (Filter.Eventually.of_forall fun y hy => hy)
  filter_upwards [h1, hmem] with y hy hym
  have hy2 : vecEuclideanNorm (y - y₀) < σ / 2 :=
    (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hym
  have hyσ : y ∈ euclideanBall y₀ σ := hsub hym
  have hδ : 0 < σ / 4 := by positivity
  have hv := hvmol y hyσ (σ / 4) hδ (by linarith)
  have hloc : euclideanBall y (σ / 4) ⊆ euclideanBall y₀ σ := by
    intro z hz
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hσ]
    have hz' := (mem_euclideanBall_iff_vecEuclideanNorm_lt hδ).1 hz
    have : z - y₀ = (z - y) + (y - y₀) := by abel
    rw [this]
    exact lt_of_le_of_lt (vecEuclideanNorm_add_le _ _) (by linarith)
  rw [← hy, hv]
  exact (harmonicMollify_restrict_eq hball u (isOpen_euclideanBall y₀ σ) hδ hloc).symm

/-- Scaling of the normalized `L²` deviation under the blow-up. -/
theorem integralAverage_blowUp_sq {E : Set (Vec d)} (u : H1Function E) {σ : ℝ} (hσ : 0 < σ)
    {y₀ : Vec d} (hball : euclideanBall y₀ σ ⊆ E) (c : ℝ) :
    integralAverage (euclideanBall (0 : Vec d) 1)
        (fun x => ((DGNM.blowUp u y₀ hσ hball).toFun x - c) ^ 2) =
      integralAverage (euclideanBall y₀ σ) (fun x => (u.toFun x - c) ^ 2) := by
  have h1 := DGNM.setIntegral_comp_affineScale_ball y₀ hσ 1 (fun x => (u.toFun x - c) ^ 2)
  rw [mul_one] at h1
  have hω := volume_euclideanBall_toReal_pos (0 : Vec d) (by norm_num : (0 : ℝ) < 1)
  have hvol := volume_euclideanBall_toReal_eq_unit_mul_of_pos y₀ hσ
  unfold integralAverage
  have e1 : (∫ x in euclideanBall (0 : Vec d) 1, ((DGNM.blowUp u y₀ hσ hball).toFun x - c) ^ 2) =
      ∫ y in euclideanBall (0 : Vec d) 1, (fun x => (u.toFun x - c) ^ 2) (σ • y + y₀) := rfl
  rw [e1, h1, hvol]
  have hσd : 0 < σ ^ d := pow_pos hσ d
  field_simp

/-- **Gradient bound at the centre** for the harmonic mollification. -/
theorem harmonicMollify_gradient_bound (hd : 0 < d) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ {E : Set (Vec d)}, IsOpen E → ∀ (u : H1Function E),
      IsWeakDivergenceFormSolutionOn (fun _ : Vec d => (1 : Mat d)) E u 0 0 →
      ∀ {σ : ℝ}, 0 < σ → ∀ {y₀ : Vec d}, euclideanBall y₀ σ ⊆ E → ∀ (c : ℝ),
        Real.sqrt (∑ i : Fin d, (fderiv ℝ (harmonicMollify u (σ / 4)) y₀ (basisVec i)) ^ 2) ≤
          C₁ / σ * Real.sqrt (integralAverage (euclideanBall y₀ σ)
            (fun x => (u.toFun x - c) ^ 2)) := by
  obtain ⟨C₁, hC₁, hanch⟩ := exists_harmonic_pointwise_derivative_bound d hd
  refine ⟨C₁, hC₁, ?_⟩
  intro E hE u hsol σ hσ y₀ hball c
  have hδ : 0 < σ / 4 := by positivity
  have hsolũ : IsWeakDivergenceFormSolutionOn (fun _ : Vec d => (1 : Mat d))
      (euclideanBall (0 : Vec d) 1) (DGNM.blowUp u y₀ hσ hball) 0 0 :=
    DGNM.solutionOn_blowUp hE hsol y₀ hσ hball
  obtain ⟨v', hvan, hvae, hbound⟩ := hanch 1 one_pos (DGNM.blowUp u y₀ hσ hball) hsolũ
  have hb1 := hbound 1 le_rfl
  -- the smooth global representative
  set g := harmonicMollify u (σ / 4) with hg
  have hgsm : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_harmonicMollify hE u hδ
  have hgdiff : Differentiable ℝ g := hgsm.differentiable (by simp)
  -- `v'` agrees with `g ∘ (σ • · + y₀)` near the origin
  have hloc := harmonicMollify_ae_eq_ball hd hE u hsol hσ hball
  have hσ2 : σ * (1 / 2) = σ / 2 := by ring
  have hae1 : ∀ᵐ y ∂volumeOn (euclideanBall (0 : Vec d) (1 / 2)),
      g (σ • y + y₀) = u.toFun (σ • y + y₀) := by
    have key := (DGNM.ae_comp_affineScale_ball_iff y₀ hσ (1 / 2)
      (P := fun x => g x = u.toFun x)).2
    rw [hσ2] at key
    exact key hloc
  have hhalf : euclideanBall (0 : Vec d) (1 / 2) ⊆ euclideanBall (0 : Vec d) 1 :=
    euclideanBall_mono (by norm_num) (by norm_num)
  have hae2 : ∀ᵐ y ∂volumeOn (euclideanBall (0 : Vec d) (1 / 2)),
      v' y = g (σ • y + y₀) := by
    have h1 := ae_restrict_of_ae_restrict_of_subset hhalf hvae
    filter_upwards [h1, hae1] with y hy1 hy2
    rw [hy1, hy2]
    rfl
  have hcont : ContinuousOn v' (euclideanBall (0 : Vec d) (1 / 2)) :=
    (hvan.continuousOn).mono hhalf
  have hcont2 : ContinuousOn (fun y : Vec d => g (σ • y + y₀)) (euclideanBall (0 : Vec d) (1 / 2)) :=
    (hgsm.continuous.comp (by fun_prop)).continuousOn
  have heqOn : Set.EqOn v' (fun y : Vec d => g (σ • y + y₀)) (euclideanBall (0 : Vec d) (1 / 2)) :=
    Measure.eqOn_open_of_ae_eq hae2 (isOpen_euclideanBall 0 (1 / 2)) hcont hcont2
  have hev : v' =ᶠ[nhds (0 : Vec d)] fun y : Vec d => g (σ • y + y₀) :=
    Filter.eventually_of_mem ((isOpen_euclideanBall 0 (1 / 2)).mem_nhds
      (center_mem_euclideanBall 0 (by norm_num))) heqOn
  have hfd : fderiv ℝ v' 0 = fderiv ℝ (fun y : Vec d => g (σ • y + y₀)) 0 := hev.fderiv_eq
  -- chain rule
  have haff : HasFDerivAt (fun y : Vec d => σ • y + y₀)
      (σ • ContinuousLinearMap.id ℝ (Vec d)) (0 : Vec d) :=
    ((hasFDerivAt_id (0 : Vec d)).const_smul σ).add_const y₀
  have hgat : HasFDerivAt g (fderiv ℝ g y₀) (σ • (0 : Vec d) + y₀) := by
    rw [smul_zero, zero_add]
    exact (hgdiff y₀).hasFDerivAt
  have hcomp := hgat.comp (0 : Vec d) haff
  have hchain : ∀ i : Fin d, fderiv ℝ v' 0 (basisVec i) = σ * fderiv ℝ g y₀ (basisVec i) := by
    intro i
    have hf' : fderiv ℝ (fun y : Vec d => g (σ • y + y₀)) 0 =
        (fderiv ℝ g y₀).comp (σ • ContinuousLinearMap.id ℝ (Vec d)) := hcomp.fderiv
    rw [hfd, hf']
    simp
  -- the sum over multi-indices of length one
  have hsum : (∑ ι : Fin 1 → Fin d,
      ((iteratedFDeriv ℝ 1 v' 0) fun k => Pi.single (ι k) (1 : ℝ)) ^ 2) =
      ∑ i : Fin d, (fderiv ℝ v' 0 (basisVec i)) ^ 2 := by
    refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin d)) _ _ fun ι => ?_
    rw [iteratedFDeriv_one_apply]
    rfl
  rw [hsum] at hb1
  have hsq : (∑ i : Fin d, (fderiv ℝ v' 0 (basisVec i)) ^ 2) =
      σ ^ 2 * ∑ i : Fin d, (fderiv ℝ g y₀ (basisVec i)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hchain i]; ring
  have hsqrt : Real.sqrt (∑ i : Fin d, (fderiv ℝ v' 0 (basisVec i)) ^ 2) =
      σ * Real.sqrt (∑ i : Fin d, (fderiv ℝ g y₀ (basisVec i)) ^ 2) := by
    rw [hsq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hσ.le]
  rw [hsqrt] at hb1
  -- the right-hand side
  have hωpos : 0 < (volume (euclideanBall (0 : Vec d) 1)).toReal :=
    volume_euclideanBall_toReal_pos 0 one_pos
  have hmin := integral_sq_sub_average_le hωpos (volume_euclideanBall_ne_top 0 zero_le_one)
    (DGNM.blowUp u y₀ hσ hball).memL2 c
  have hmin' : integralAverage (euclideanBall (0 : Vec d) 1)
      (fun x => ((DGNM.blowUp u y₀ hσ hball).toFun x -
        integralAverage (euclideanBall (0 : Vec d) 1) (DGNM.blowUp u y₀ hσ hball).toFun) ^ 2) ≤
      integralAverage (euclideanBall (0 : Vec d) 1)
        (fun x => ((DGNM.blowUp u y₀ hσ hball).toFun x - c) ^ 2) := by
    unfold integralAverage
    exact mul_le_mul_of_nonneg_left hmin (inv_nonneg.2 ENNReal.toReal_nonneg)
  have hscale := integralAverage_blowUp_sq u hσ hball c
  have hfinal : σ * Real.sqrt (∑ i : Fin d, (fderiv ℝ g y₀ (basisVec i)) ^ 2) ≤
      C₁ * Real.sqrt (integralAverage (euclideanBall y₀ σ) (fun x => (u.toFun x - c) ^ 2)) := by
    refine hb1.trans ?_
    rw [← hscale]
    simp only [Nat.cast_one, mul_one, div_one, pow_one]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmin') hC₁.le
  rw [div_mul_eq_mul_div, le_div_iff₀ hσ]
  linarith

/-- The mollification is an a.e. representative on an open set `D` all of whose points have a
`σ`-ball in the domain. -/
theorem harmonicMollify_ae_eq_open (hd : 0 < d) {E : Set (Vec d)} (hE : IsOpen E)
    (u : H1Function E)
    (hsol : IsWeakDivergenceFormSolutionOn (fun _ : Vec d => (1 : Mat d)) E u 0 0)
    {σ : ℝ} (hσ : 0 < σ) {D : Set (Vec d)} (hD : IsOpen D)
    (hDE : ∀ y ∈ D, euclideanBall y σ ⊆ E) :
    harmonicMollify u (σ / 4) =ᵐ[volumeOn D] u.toFun := by
  show ∀ᵐ y ∂(volume.restrict D), harmonicMollify u (σ / 4) y = u.toFun y
  rw [ae_restrict_iff' hD.measurableSet, ae_iff]
  have hset : {y : Vec d | ¬(y ∈ D → harmonicMollify u (σ / 4) y = u.toFun y)} =
      D ∩ {y | ¬ harmonicMollify u (σ / 4) y = u.toFun y} := by
    ext y; simp [Set.mem_inter_iff]
  rw [hset]
  refine measure_null_of_locally_null _ fun y₀ hy₀ => ?_
  have hloc := harmonicMollify_ae_eq_ball hd hE u hsol hσ (hDE y₀ hy₀.1)
  have hloc' : ∀ᵐ y ∂(volume.restrict (euclideanBall y₀ (σ / 2))),
      harmonicMollify u (σ / 4) y = u.toFun y := hloc
  rw [ae_restrict_iff' (measurableSet_euclideanBall _ _), ae_iff] at hloc'
  refine ⟨euclideanBall y₀ (σ / 2) ∩ {y | ¬ harmonicMollify u (σ / 4) y = u.toFun y}, ?_, ?_⟩
  · refine mem_nhdsWithin.2 ⟨euclideanBall y₀ (σ / 2), isOpen_euclideanBall _ _,
      center_mem_euclideanBall _ (by positivity), ?_⟩
    intro y hy
    exact ⟨hy.1, hy.2.2⟩
  · refine measure_mono_null ?_ hloc'
    intro y hy
    exact fun h => hy.2 (h hy.1)

/-- **Interior Lipschitz estimate for weakly harmonic functions on an open convex set.** -/
theorem harmonic_lipschitz (hd : 0 < d) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ {E : Set (Vec d)}, IsOpen E → ∀ (u : H1Function E),
      IsWeakDivergenceFormSolutionOn (fun _ : Vec d => (1 : Mat d)) E u 0 0 →
      ∀ {σ : ℝ}, 0 < σ → ∀ {D : Set (Vec d)}, IsOpen D → Convex ℝ D →
      (∀ y ∈ D, euclideanBall y σ ⊆ E) → ∀ {c M : ℝ},
      (∀ y ∈ D, Real.sqrt (integralAverage (euclideanBall y σ)
          (fun x => (u.toFun x - c) ^ 2)) ≤ M) →
      ∃ g : Vec d → ℝ, g =ᵐ[volumeOn D] u.toFun ∧
        ∀ y ∈ D, ∀ y' ∈ D, |g y - g y'| ≤ K₀ * σ⁻¹ * M * vecEuclideanNorm (y - y') := by
  obtain ⟨C₁, hC₁, hgrad⟩ := harmonicMollify_gradient_bound hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  refine ⟨C₁ * Real.sqrt d, by positivity, ?_⟩
  intro E hE u hsol σ hσ D hD hDconv hDE c M hM
  have hδ : 0 < σ / 4 := by positivity
  refine ⟨harmonicMollify u (σ / 4), harmonicMollify_ae_eq_open hd hE u hsol hσ hD hDE, ?_⟩
  intro y hy y' hy'
  set g := harmonicMollify u (σ / 4) with hg
  have hgsm : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_harmonicMollify hE u hδ
  have hgdiff : Differentiable ℝ g := hgsm.differentiable (by simp)
  have hM0 : 0 ≤ M := (Real.sqrt_nonneg _).trans (hM y hy)
  have hbound : ∀ z ∈ D, ‖fderiv ℝ g z‖ ≤ C₁ * Real.sqrt d * σ⁻¹ * M := by
    intro z hz
    have hgb := hgrad hE u hsol hσ (hDE z hz) c
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    set L := fderiv ℝ g z with hL
    have hv : v = ∑ i : Fin d, v i • basisVec i := by
      ext j
      simp [basisVec, Finset.sum_apply, Pi.single_apply]
    have hLv : L v = ∑ i : Fin d, v i * L (basisVec i) := by
      conv_lhs => rw [hv]
      simp [map_sum]
    have h1 : |L v| ≤ ‖v‖ * ∑ i : Fin d, |L (basisVec i)| := by
      rw [hLv, Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using norm_le_pi_norm v i)
        (abs_nonneg _)
    have h2 : (∑ i : Fin d, |L (basisVec i)|) ≤
        Real.sqrt d * Real.sqrt (∑ i : Fin d, (L (basisVec i)) ^ 2) := by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d))
        (fun _ => (1 : ℝ)) (fun i => |L (basisVec i)|)
      simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, sq_abs] at hcs
      rw [← Real.sqrt_mul hdR.le]
      exact Real.le_sqrt_of_sq_le hcs
    have h3 : Real.sqrt (∑ i : Fin d, (L (basisVec i)) ^ 2) ≤ C₁ * σ⁻¹ * M := by
      calc _ ≤ C₁ / σ * Real.sqrt (integralAverage (euclideanBall z σ)
            (fun x => (u.toFun x - c) ^ 2)) := hgb
        _ ≤ C₁ / σ * M := mul_le_mul_of_nonneg_left (hM z hz) (by positivity)
        _ = C₁ * σ⁻¹ * M := by rw [div_eq_mul_inv]
    calc ‖L v‖ = |L v| := Real.norm_eq_abs _
      _ ≤ ‖v‖ * (Real.sqrt d * (C₁ * σ⁻¹ * M)) := by
          refine h1.trans (mul_le_mul_of_nonneg_left (h2.trans ?_) (norm_nonneg _))
          exact mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
      _ = C₁ * Real.sqrt d * σ⁻¹ * M * ‖v‖ := by ring
  have hmv := hDconv.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hgdiff z) hbound hy' hy
  calc |g y - g y'| = ‖g y - g y'‖ := (Real.norm_eq_abs _).symm
    _ ≤ C₁ * Real.sqrt d * σ⁻¹ * M * ‖y - y'‖ := hmv
    _ ≤ C₁ * Real.sqrt d * σ⁻¹ * M * vecEuclideanNorm (y - y') :=
        mul_le_mul_of_nonneg_left (norm_le_vecEuclideanNorm _) (by positivity)

end

end PDE.Ch4GreenDecay
