module

public import EllipticRegularity.Parabolic.Cauchy.Duality.MassWeightedEnergy

/-! # Flux bounds from the weighted energy estimate -/

@[expose] public section

namespace PDE.Parabolic.Duality

open MeasureTheory Set Filter Topology PDE PDE.Parabolic

/-- A point outside the radius-`R` ball is at least `R-S` from the radius-`S`
ball. -/
theorem cauchyMass_distanceFromClosedBall_lower {d : ℕ} {S : ℝ}
    (hS : 0 ≤ S) (x : Vec d) :
    vecEuclideanNorm x - S ≤
      PDE.Parabolic.Cauchy.Weights.euclideanSetDistance
        (euclideanClosedBall (0 : Vec d) S) x := by
  let K : Set (Vec d) := euclideanClosedBall 0 S
  have hK : K.Nonempty := by
    refine ⟨0, ?_⟩
    change (0 : Vec d) ∈ euclideanClosedBall 0 S
    rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le hS]
    simpa [vecEuclideanNorm, vecNormSq, vecDot] using hS
  change vecEuclideanNorm x - S ≤
    sInf (Set.range fun y : K => vecEuclideanNorm (x - (y : Vec d)))
  have hrange : (Set.range fun y : K =>
      vecEuclideanNorm (x - (y : Vec d))).Nonempty := by
    rcases hK with ⟨y, hy⟩
    exact ⟨vecEuclideanNorm (x - y), ⟨⟨y, hy⟩, rfl⟩⟩
  apply le_csInf hrange
  rintro _ ⟨⟨y, hy⟩, rfl⟩
  change y ∈ euclideanClosedBall 0 S at hy
  have hy' : vecEuclideanNorm y ≤ S := by
    rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le hS] at hy
    simpa using hy
  have htri : vecEuclideanNorm x ≤
      vecEuclideanNorm (x - y) + vecEuclideanNorm y := by
    calc
      vecEuclideanNorm x = vecEuclideanNorm ((x - y) + y) := by
        congr 1
        abel
      _ ≤ vecEuclideanNorm (x - y) + vecEuclideanNorm y :=
        vecEuclideanNorm_add_le _ _
  linarith

/-- On a distant annulus, mollification of the capped distance remains close
enough to the cap to retain exponential decay. -/
theorem cauchyMass_mollified_distance_lower_outside {d : ℕ} {S R : ℝ}
    (hS : 0 ≤ S) (hR : 0 ≤ R) {x : Vec d} (hx : R ≤ vecEuclideanNorm x - S)
    (n : ℕ) :
    R - Real.sqrt d * PDE.unitConvexApproxScale n ≤
      PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify
        (euclideanClosedBall (0 : Vec d) S) R n x := by
  have hK : (euclideanClosedBall (0 : Vec d) S).Nonempty := by
    refine ⟨0, ?_⟩
    rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le hS]
    simpa [vecEuclideanNorm, vecNormSq, vecDot] using hS
  have hdist := cauchyMass_distanceFromClosedBall_lower hS x
  have hcap : PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance
      (euclideanClosedBall (0 : Vec d) S) R x = R := by
    rw [PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance,
      min_eq_left (le_trans hx hdist)]
  obtain ⟨_, _, _, herr⟩ :=
    PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify_properties hK hR n
  have he := herr x
  rw [hcap] at he
  have hlow : R - Real.sqrt d * PDE.unitConvexApproxScale n ≤
      PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify
        (euclideanClosedBall (0 : Vec d) S) R n x := by
    have := (abs_le.mp he).1
    linarith
  exact hlow

/-- Sending the cap to infinity while refining the mollifier recovers the
uncapped distance pointwise. -/
theorem cauchyMass_truncatedDistanceMollify_diagonal_tendsto {d : ℕ}
    {K : Set (Vec d)} (hK : K.Nonempty) (x : Vec d) :
    Tendsto (fun n : ℕ =>
      PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify K (n : ℝ) n x)
      atTop (𝓝 (PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K x)) := by
  let D : ℝ := PDE.Parabolic.Cauchy.Weights.euclideanSetDistance K x
  have hD : 0 ≤ D := PDE.Parabolic.Cauchy.Weights.euclideanSetDistance_nonneg hK x
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hcapEventually : (fun n : ℕ => min (n : ℝ) D) =ᶠ[atTop] fun _ => D := by
    filter_upwards [hn.eventually_gt_atTop D] with n hnD
    simp [min_eq_right hnD.le]
  have hcap : Tendsto (fun n : ℕ => min (n : ℝ) D) atTop (𝓝 D) :=
    tendsto_const_nhds.congr' hcapEventually.symm
  have hscale : Tendsto (fun n : ℕ => Real.sqrt d * PDE.unitConvexApproxScale n)
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul PDE.tendsto_unitConvexApproxScale_zero)
  have hcapError : Tendsto (fun n : ℕ => |min (n : ℝ) D - D|)
      atTop (𝓝 0) := by
    have heq : (fun n : ℕ => |min (n : ℝ) D - D|) =ᶠ[atTop] fun _ => (0 : ℝ) := by
      filter_upwards [hcapEventually] with n hn
      simp [hn]
    exact tendsto_const_nhds.congr' heq.symm
  have herr (n : ℕ) : |PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify
      K (n : ℝ) n x - min (n : ℝ) D| ≤
        Real.sqrt d * PDE.unitConvexApproxScale n := by
    simpa [D, PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance] using
      PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify_properties hK
        (show 0 ≤ (n : ℝ) by positivity) n |>.2.2.2 x
  have hsum : Tendsto (fun n : ℕ =>
      Real.sqrt d * PDE.unitConvexApproxScale n + |min (n : ℝ) D - D|)
      atTop (𝓝 0) := by
    simpa using hscale.add hcapError
  have herror : Tendsto (fun n : ℕ =>
      |PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify K (n : ℝ) n x - D|)
      atTop (𝓝 0) := by
    exact squeeze_zero (fun n => abs_nonneg _) (fun n => by
      calc
        |PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify K (n : ℝ) n x - D| ≤
            |PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify K (n : ℝ) n x -
              min (n : ℝ) D| + |min (n : ℝ) D - D| := abs_sub_le _ _ _
        _ ≤ Real.sqrt d * PDE.unitConvexApproxScale n + |min (n : ℝ) D - D| :=
          add_le_add (herr n) le_rfl) hsum
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.norm_eq_abs, sub_zero, D] using herror

/-- The Euclidean magnitude of the coefficient flux belongs to `L²` on the
whole Cauchy slab. -/
theorem cauchyMass_flux_magnitude_memLp {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T)) :
    MemLp (fun z : Vec d × ℝ =>
      vecEuclideanNorm (matVecMul (a z) (u.grad z))) 2
      (volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s T)) := by
  classical
  let Q : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s T
  let μ : Measure (Vec d × ℝ) := volume.restrict Q
  have hQsub : Q ⊆ (univ : Set (Vec d)) ×ˢ Icc s T :=
    prod_mono subset_rfl Ioc_subset_Icc_self
  have hvec : MemLp
      (fun z : Vec d × ℝ => (matVecMul (a z) (u.grad z)).toHilbertVec) 2 μ := by
    rw [MeasureTheory.memLp_piLp_iff]
    intro i
    have hi := (PDE.Parabolic.Energy.flux_memLp ha u i).mono_measure
      (Measure.restrict_mono hQsub le_rfl)
    simpa [PDE.Parabolic.Energy.flux, Vec.toHilbertVec_apply,
      matVecMul] using hi
  have hnorm := hvec.norm_rpow_div (1 : ENNReal)
  have hnorm' : MemLp (fun z : Vec d × ℝ =>
      ‖(matVecMul (a z) (u.grad z)).toHilbertVec‖) 2 μ := by
    simpa using hnorm
  have hEq : (fun z : Vec d × ℝ =>
      vecEuclideanNorm (matVecMul (a z) (u.grad z))) =ᵐ[μ]
      fun z => ‖(matVecMul (a z) (u.grad z)).toHilbertVec‖ :=
    ae_of_all _ fun z => Vec.vecEuclideanNorm_eq_norm_toHilbertVec _
  have hmag : MemLp (fun z : Vec d × ℝ =>
      vecEuclideanNorm (matVecMul (a z) (u.grad z))) 2 μ :=
    (memLp_congr_ae hEq).mpr hnorm'
  simpa [μ, Q] using hmag

/-- For compactly supported initial data, the smoothed capped exponential
weight has a uniform weighted energy bound. -/
theorem cauchyMass_smooth_weighted_energy_bound {d : ℕ}
    {lam Lam ε R : ℝ} {a : ParCoeffField d} {s T : ℝ}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) {K : Set (Vec d)} (hK : K.Nonempty)
    (hfK : ∀ x ∉ K, f x = 0) (hR : 0 ≤ R) (hε : 0 ≤ ε) (n : ℕ) :
    ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s T,
      cauchyMassSmoothExponentialWeight K s R Lam ε n z ^ 2 *
        PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z ≤
      Real.exp (2 * ε * Real.sqrt d) * ∫ x : Vec d, f x ^ 2 := by
  classical
  let ξ : Vec d × ℝ → ℝ := cauchyMassSmoothExponentialWeight K s R Lam ε n
  have hLam : 0 ≤ Lam := (cauchyMass_Lam_pos hsT ha).le
  have hξcd : ContDiff ℝ 1 ξ := by
    dsimp [ξ]
    exact cauchyMassSmoothExponentialWeight_contDiff hK hR n
  have hξbound (z : Vec d × ℝ) :
      |ξ z| ≤ Real.exp (ε * R + 2 * Lam * ε ^ 2) := by
    exact cauchyMassSmoothExponentialWeight_bound hK hR hLam hε n z
  have hfSq : Integrable (fun x : Vec d => f x ^ 2) volume := hf.integrable_sq
  have hξsmeas : AEStronglyMeasurable (fun x : Vec d => ξ (x, s) ^ 2) volume := by
    exact (hξcd.continuous.comp (continuous_id.prodMk continuous_const)).pow 2 |>.aestronglyMeasurable
  have hξsbound : ∀ᵐ x ∂volume,
      ‖ξ (x, s) ^ 2‖ ≤ Real.exp (ε * R + 2 * Lam * ε ^ 2) ^ 2 := by
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rcases abs_le.mp (hξbound (x, s)) with ⟨hlo, hhi⟩
    nlinarith [sq_nonneg
      (Real.exp (ε * R + 2 * Lam * ε ^ 2) - ξ (x, s)),
      sq_nonneg (Real.exp (ε * R + 2 * Lam * ε ^ 2) + ξ (x, s))]
  have hintegrable : Integrable (fun x : Vec d => ξ (x, s) ^ 2 * f x ^ 2) volume := by
    exact (hfSq.bdd_mul hξsmeas
      (c := Real.exp (ε * R + 2 * Lam * ε ^ 2) ^ 2) hξsbound).congr
        (ae_of_all _ fun _ => rfl)
  have hsmall (x : Vec d) (hx : x ∈ K) :
      PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify K R n x ≤
        Real.sqrt d * PDE.unitConvexApproxScale n :=
    PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify_le_of_mem hK hR n hx
  have hinitialPoint (x : Vec d) : ξ (x, s) ^ 2 * f x ^ 2 ≤
      Real.exp (2 * ε * Real.sqrt d) * f x ^ 2 := by
    by_cases hx : x ∈ K
    · have hξeq : ξ (x, s) = Real.exp
        (ε * PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify K R n x) := by
        simp [ξ, cauchyMassSmoothExponentialWeight, cauchyMassTimeDamping,
          cauchyMassTimePrimitive, cauchyMassSpatialExponential]
      have hscale := PDE.unitConvexApproxScale_le_one n
      have hρ := hsmall x hx
      have hρ' : PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify
          K R n x ≤ Real.sqrt d := by
        calc
          _ ≤ Real.sqrt d * PDE.unitConvexApproxScale n := hρ
          _ ≤ Real.sqrt d * 1 := mul_le_mul_of_nonneg_left hscale
            (Real.sqrt_nonneg _)
          _ = Real.sqrt d := by ring
      have hsq : Real.exp
          (ε * PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify K R n x) ^ 2 ≤
          Real.exp (2 * ε * Real.sqrt d) := by
        rw [← Real.exp_nat_mul]
        have hmul := mul_le_mul_of_nonneg_left hρ' hε
        have hmul2 :
            (ε * PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify K R n x) * 2 ≤
              (ε * Real.sqrt d) * 2 :=
          mul_le_mul_of_nonneg_right hmul (by norm_num)
        apply Real.exp_le_exp.mpr
        calc
          2 * (ε * PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify K R n x) =
              (ε * PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify K R n x) * 2 := by ring
          _ ≤ (ε * Real.sqrt d) * 2 := hmul2
          _ = 2 * ε * Real.sqrt d := by ring
      rw [hξeq]
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    · rw [hfK x hx]
      simp
  have hinitial : ∫ x : Vec d, ξ (x, s) ^ 2 * f x ^ 2 ≤
      Real.exp (2 * ε * Real.sqrt d) * ∫ x : Vec d, f x ^ 2 := by
    calc
      _ ≤ ∫ x : Vec d, Real.exp (2 * ε * Real.sqrt d) * f x ^ 2 :=
        integral_mono_ae hintegrable (hfSq.const_mul _)
          (ae_of_all _ hinitialPoint)
      _ = _ := by rw [integral_const_mul]
  have hDiss := cauchyMassSmoothWeighted_energy_dissipation hsT ha f hf u hu
    hK hR hε n ⟨hsT.le, le_rfl⟩ hsT
  have hDiss' :
      (∫ x : Vec d, ξ (x, T) ^ 2 * u.toFun (x, T) ^ 2) +
        ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s T,
          ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z ≤
        ∫ x : Vec d, ξ (x, s) ^ 2 * f x ^ 2 := by
    change (∫ x : Vec d, ξ (x, T) ^ 2 * u.toFun (x, T) ^ 2) +
      2 * ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s T,
        (1 / 2 : ℝ) * ξ z ^ 2 *
          PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z ≤
      ∫ x : Vec d, ξ (x, s) ^ 2 * f x ^ 2 at hDiss
    have hscale : 2 * ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s T,
        (1 / 2 : ℝ) * ξ z ^ 2 *
          PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z =
        ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s T,
          ξ z ^ 2 * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z := by
      rw [show (fun z : Vec d × ℝ => (1 / 2 : ℝ) * ξ z ^ 2 *
          PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z) =
        fun z => (1 / 2 : ℝ) * (ξ z ^ 2 *
          PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z) by
            funext z; ring, integral_const_mul]
      ring
    rw [hscale] at hDiss
    exact hDiss
  have hEndpoint : 0 ≤ ∫ x : Vec d, ξ (x, T) ^ 2 * u.toFun (x, T) ^ 2 := by
    apply integral_nonneg_of_ae
    exact ae_of_all _ fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have henergy := hDiss'.trans hinitial
  linarith

/-- The smooth capped exponential weight controls the corresponding weighted
flux in `L²`. -/
theorem cauchyMass_smooth_weighted_flux_bound {d : ℕ}
    {lam Lam ε R : ℝ} {a : ParCoeffField d} {s T : ℝ}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) {K : Set (Vec d)} (hK : K.Nonempty)
    (hfK : ∀ x ∉ K, f x = 0) (hR : 0 ≤ R) (hε : 0 ≤ ε) (n : ℕ) :
    ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s T,
      (cauchyMassSmoothExponentialWeight K s R Lam ε n z *
        vecEuclideanNorm (matVecMul (a z) (u.grad z))) ^ 2 ≤
      Lam * Real.exp (2 * ε * Real.sqrt d) * ∫ x : Vec d, f x ^ 2 := by
  classical
  let Q : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s T
  let μ : Measure (Vec d × ℝ) := volume.restrict Q
  let ξ : Vec d × ℝ → ℝ := cauchyMassSmoothExponentialWeight K s R Lam ε n
  let N : Vec d × ℝ → ℝ := fun z =>
    vecEuclideanNorm (matVecMul (a z) (u.grad z))
  let q : Vec d × ℝ → ℝ := PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u
  have hQsub : Q ⊆ (univ : Set (Vec d)) ×ˢ Icc s T :=
    prod_mono subset_rfl Ioc_subset_Icc_self
  have hLam : 0 ≤ Lam := (cauchyMass_Lam_pos hsT ha).le
  have hξcd : ContDiff ℝ 1 ξ := by
    dsimp [ξ]
    exact cauchyMassSmoothExponentialWeight_contDiff hK hR n
  have hB : 0 ≤ Real.exp (ε * R + 2 * Lam * ε ^ 2) := by positivity
  have hξbound : ∀ z, |ξ z| ≤ Real.exp (ε * R + 2 * Lam * ε ^ 2) := by
    intro z
    exact cauchyMassSmoothExponentialWeight_bound
      (s := s) (Lam := Lam) (ε := ε) hK hR hLam hε n z
  have hξmeas : AEStronglyMeasurable (fun z : Vec d × ℝ => ξ z ^ 2) μ :=
    (hξcd.continuous.pow 2).aestronglyMeasurable
  have hξsqBound : ∀ᵐ z ∂μ,
      ‖ξ z ^ 2‖ ≤ Real.exp (ε * R + 2 * Lam * ε ^ 2) ^ 2 := by
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rcases abs_le.mp (hξbound z) with ⟨hlo, hhi⟩
    nlinarith [sq_nonneg
      (Real.exp (ε * R + 2 * Lam * ε ^ 2) - ξ z),
      sq_nonneg (Real.exp (ε * R + 2 * Lam * ε ^ 2) + ξ z)]
  have hN : MemLp N 2 μ := by
    simpa [N, μ, Q] using cauchyMass_flux_magnitude_memLp ha u
  have hweightedSqInt : Integrable (fun z => (ξ z * N z) ^ 2) μ := by
    have hmul := hN.integrable_sq.bdd_mul hξmeas
      (c := Real.exp (ε * R + 2 * Lam * ε ^ 2) ^ 2) hξsqBound
    exact hmul.congr (ae_of_all _ fun z => by dsimp; ring)
  have hweightedMeas : AEStronglyMeasurable (fun z => ξ z * N z) μ :=
    hξcd.continuous.aestronglyMeasurable.mul hN.aestronglyMeasurable
  have hweighted : MemLp (fun z => ξ z * N z) 2 μ :=
    (memLp_two_iff_integrable_sq hweightedMeas).2 hweightedSqInt
  have hqint : Integrable q μ := by
    have hqclosed := PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity_integrable ha u
    change Integrable q
      (volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s T)) at hqclosed
    exact hqclosed.mono_measure (Measure.restrict_mono hQsub le_rfl)
  have hqweightedInt : Integrable (fun z => ξ z ^ 2 * q z) μ := by
    have hmul := hqint.bdd_mul hξmeas
      (c := Real.exp (ε * R + 2 * Lam * ε ^ 2) ^ 2) hξsqBound
    exact hmul.congr (ae_of_all _ fun z => by ring)
  have hEll : ∀ᵐ z ∂μ, IsEllipticMatrix lam Lam (a z) :=
    ha.elliptic.filter_mono (ae_mono (Measure.restrict_mono hQsub le_rfl))
  have hpoint : ∀ᵐ z ∂μ, (ξ z * N z) ^ 2 ≤ Lam * (ξ z ^ 2 * q z) := by
    filter_upwards [hEll] with z hz
    have hmatrix := vecNormSq_matVecMul_le_mul_vecDot_of_isEllipticMatrix
      hz (u.grad z)
    dsimp [N, q, PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity]
    calc
      (ξ z * vecEuclideanNorm (matVecMul (a z) (u.grad z))) ^ 2 =
          ξ z ^ 2 * vecNormSq (matVecMul (a z) (u.grad z)) := by
            rw [mul_pow, vecEuclideanNorm_sq]
      _ ≤ ξ z ^ 2 * (Lam * vecDot (u.grad z) (matVecMul (a z) (u.grad z))) :=
        mul_le_mul_of_nonneg_left hmatrix (sq_nonneg _)
      _ = Lam * (ξ z ^ 2 * vecDot (u.grad z) (matVecMul (a z) (u.grad z))) := by ring
  have hmono : ∫ z, (ξ z * N z) ^ 2 ∂μ ≤
      ∫ z, Lam * (ξ z ^ 2 * q z) ∂μ :=
    integral_mono_ae hweightedSqInt (hqweightedInt.const_mul Lam)
      (hpoint.mono fun z hz => by simpa only [mul_assoc] using hz)
  have hscale : ∫ z, Lam * (ξ z ^ 2 * q z) ∂μ =
      Lam * ∫ z, ξ z ^ 2 * q z ∂μ := integral_const_mul _ _
  have henergy := cauchyMass_smooth_weighted_energy_bound hsT ha f hf u hu
    hK hfK hR hε n
  have hfinal : ∫ z, ξ z ^ 2 * q z ∂μ ≤
      Real.exp (2 * ε * Real.sqrt d) * ∫ x : Vec d, f x ^ 2 := by
    simpa [μ, Q, ξ, q, mul_comm] using henergy
  have hmain : ∫ z, (ξ z * N z) ^ 2 ∂μ ≤
      Lam * (Real.exp (2 * ε * Real.sqrt d) * ∫ x : Vec d, f x ^ 2) := by
    calc
      _ ≤ ∫ z, Lam * (ξ z ^ 2 * q z) ∂μ := hmono
      _ = Lam * ∫ z, ξ z ^ 2 * q z ∂μ := hscale
      _ ≤ Lam * (Real.exp (2 * ε * Real.sqrt d) * ∫ x : Vec d, f x ^ 2) :=
        mul_le_mul_of_nonneg_left hfinal hLam
  simpa [μ, Q, ξ, N, mul_assoc] using hmain

end PDE.Parabolic.Duality
