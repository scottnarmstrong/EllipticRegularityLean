module

public import EllipticRegularity.Parabolic.Cauchy.Weights.SmoothEnergy
public import EllipticRegularity.Parabolic.Cauchy.Weights.MatrixDensity
public import EllipticRegularity.Parabolic.Cauchy.Weights.TruncatedDistance
public import EllipticRegularity.Parabolic.Chain.Calculus
public import EllipticRegularity.Parabolic.WeakSlice.Product

public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith

/-! # Smooth truncated exponential weights for the mass argument -/

@[expose] public section

namespace PDE.Parabolic.Duality

open MeasureTheory Set Filter Topology PDE PDE.Parabolic

private theorem cauchyMass_matVecMul_smul {d : ℕ} (A : Mat d) (r : ℝ)
    (v : Vec d) :
    matVecMul A (r • v) = r • matVecMul A v := by
  ext i
  simp only [matVecMul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem cauchyMass_vecDot_smul_left {d : ℕ} (r : ℝ) (v w : Vec d) :
    vecDot (r • v) w = r * vecDot v w := by
  rw [vecDot_comm, PDE.Parabolic.WeakSlice.vecDot_smul_right', vecDot_comm]

/-- Half of the principal energy absorbs the mixed weight flux with the
coefficient needed for the exponential time damping. -/
theorem cauchyMass_half_cross_term_bound {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (u : ℝ) (v p : Vec d) :
    -(1 / 2 : ℝ) * vecDot v (matVecMul A v) -
        2 * u * vecDot (matVecMul A v) p ≤
      2 * Lam * vecNormSq p * u ^ 2 := by
  let c : ℝ := Real.sqrt 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hc2 : c ^ 2 = 2 := by dsimp [c]; exact Real.sq_sqrt (by norm_num)
  have hci : c⁻¹ * c = 1 := inv_mul_cancel₀ hc.ne'
  have hci2 : (c⁻¹) ^ 2 = 1 / 2 := by
    rw [inv_pow, hc2]
    norm_num
  let Q := vecDot v (matVecMul A v)
  let F := vecDot (matVecMul A v) p
  have hbase := PDE.Parabolic.Cauchy.Weights.weightedEnergy_cross_term_bound
    hA (c * u) (c⁻¹ • v) p
  have hmv := cauchyMass_matVecMul_smul A c⁻¹ v
  have hq : vecDot (c⁻¹ • v) (matVecMul A (c⁻¹ • v)) =
      (1 / 2 : ℝ) * Q := by
    rw [hmv, PDE.Parabolic.WeakSlice.vecDot_smul_right',
      cauchyMass_vecDot_smul_left]
    calc
      c⁻¹ * (c⁻¹ * vecDot v (matVecMul A v)) =
          (c⁻¹) ^ 2 * vecDot v (matVecMul A v) := by ring
      _ = (1 / 2 : ℝ) * Q := by rw [hci2]
  have hf : vecDot (matVecMul A (c⁻¹ • v)) p = c⁻¹ * F := by
    rw [hmv, cauchyMass_vecDot_smul_left]
  have hcross : (c * u) * (c⁻¹ * F) = u * F := by
    calc
      (c * u) * (c⁻¹ * F) = u * F * (c * c⁻¹) := by ring
      _ = u * F := by rw [mul_inv_cancel₀ hc.ne']; ring
  rw [hq, hf] at hbase
  have hquad : (c * u) ^ 2 = 2 * u ^ 2 := by nlinarith [hc2]
  rw [hquad] at hbase
  dsimp [Q, F] at hbase ⊢
  have hcross' : 2 * (c * u) * (c⁻¹ * vecDot (matVecMul A v) p) =
      2 * u * vecDot (matVecMul A v) p := by
    calc
      2 * (c * u) * (c⁻¹ * vecDot (matVecMul A v) p) =
          2 * ((c * u) * (c⁻¹ * F)) := by dsimp [F]; ring
      _ = 2 * (u * F) := by rw [hcross]
      _ = 2 * u * vecDot (matVecMul A v) p := by dsimp [F]; ring
  nlinarith [hbase, hcross']

/-- A smooth time primitive which agrees with `t - s` for `t ≥ s` and stays
nonpositive only by a bounded amount before the initial time. -/
noncomputable def cauchyMassTimePrimitive (s t : ℝ) : ℝ :=
  (t - s) * Real.smoothTransition (t - s + 1)

theorem cauchyMassTimePrimitive_contDiff (s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (cauchyMassTimePrimitive s) := by
  unfold cauchyMassTimePrimitive
  fun_prop

theorem cauchyMassTimePrimitive_eq_sub {s t : ℝ} (hst : s ≤ t) :
    cauchyMassTimePrimitive s t = t - s := by
  unfold cauchyMassTimePrimitive
  have harg : 1 ≤ t - s + 1 := by linarith
  rw [Real.smoothTransition.one_of_one_le harg, mul_one]

theorem deriv_cauchyMassTimePrimitive {s t : ℝ} :
    deriv (cauchyMassTimePrimitive s) t =
      Real.smoothTransition (t - s + 1) +
        (t - s) * deriv Real.smoothTransition (t - s + 1) := by
  let f : ℝ → ℝ := fun r => r - s
  let g : ℝ → ℝ := fun r => r - s + 1
  have hf : HasDerivAt f 1 t := by
    simpa [f] using (hasDerivAt_id t).sub_const s
  have hg : HasDerivAt g 1 t := by
    change HasDerivAt (fun r => f r + 1) 1 t
    simpa only [hasDerivAt_add_const_iff] using hf
  have hst' : HasDerivAt PDE.smoothTransitionProfile
      (deriv PDE.smoothTransitionProfile (t - s + 1)) (t - s + 1) :=
    (PDE.smoothTransitionProfile.smooth.differentiable (by norm_num) _).hasDerivAt
  have hst : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (t - s + 1)) (t - s + 1) := by
    simpa only [PDE.smoothTransitionProfile] using hst'
  have hcomp := hst.comp t hg
  have hprod := hf.mul hcomp
  have hfun : cauchyMassTimePrimitive s = f * (Real.smoothTransition ∘ g) := by
    funext r
    rfl
  rw [hfun]
  change deriv (f * (Real.smoothTransition ∘ g)) t = _
  rw [hprod.deriv]
  simp [f, g]

private theorem deriv_smoothTransition_eq_zero_of_lt_zero {x : ℝ} (hx : x < 0) :
    deriv Real.smoothTransition x = 0 := by
  have hev : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact Real.smoothTransition.zero_of_nonpos hy.le
  rw [hev.deriv_eq]
  simp

private theorem deriv_smoothTransition_eq_zero_of_one_lt {x : ℝ} (hx : 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  have hev : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact Real.smoothTransition.one_of_one_le hy.le
  rw [hev.deriv_eq]
  simp

theorem cauchyMassTimePrimitive_lower_bound (s t : ℝ) :
    -1 ≤ cauchyMassTimePrimitive s t := by
  unfold cauchyMassTimePrimitive
  by_cases hleft : t - s + 1 ≤ 0
  · rw [Real.smoothTransition.zero_of_nonpos hleft]
    simp
  · have harg : 0 < t - s + 1 := lt_of_not_ge hleft
    have hnonneg := Real.smoothTransition.nonneg (t - s + 1)
    have hle := Real.smoothTransition.le_one (t - s + 1)
    by_cases hts : t < s
    · have hfactor : -1 ≤ t - s := by linarith
      have hmul : (t - s) * Real.smoothTransition (t - s + 1) ≥
          (t - s) * 1 := by
        exact mul_le_mul_of_nonpos_left hle (by linarith)
      linarith
    · have hfactor : 0 ≤ t - s := by linarith
      exact le_trans (by norm_num : (-1 : ℝ) ≤ 0)
        (mul_nonneg hfactor hnonneg)

theorem deriv_cauchyMassTimePrimitive_abs_le_nine (s t : ℝ) :
    |deriv (cauchyMassTimePrimitive s) t| ≤ 9 := by
  rw [deriv_cauchyMassTimePrimitive]
  have htrans : 0 ≤ Real.smoothTransition (t - s + 1) ∧
      Real.smoothTransition (t - s + 1) ≤ 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hderiv : |deriv Real.smoothTransition (t - s + 1)| ≤ 8 := by
    simpa only [PDE.smoothTransitionProfile] using
      PDE.smoothTransitionProfile.abs_deriv_le_eight (t - s + 1)
  by_cases hleft : t - s + 1 < 0
  · rw [deriv_smoothTransition_eq_zero_of_lt_zero hleft,
      Real.smoothTransition.zero_of_nonpos hleft.le]
    simp
  · by_cases hright : 1 < t - s + 1
    · rw [deriv_smoothTransition_eq_zero_of_one_lt hright,
        Real.smoothTransition.one_of_one_le hright.le]
      simp
    · have harg0 : 0 ≤ t - s + 1 := le_of_not_gt hleft
      have harg1 : t - s + 1 ≤ 1 := le_of_not_gt hright
      have htslo : -1 ≤ t - s := by linarith
      have htshi : t - s ≤ 0 := by linarith
      rw [abs_le]
      constructor
      · have hterm : |(t - s) * deriv Real.smoothTransition (t - s + 1)| ≤ 8 := by
          rw [abs_mul]
          calc
            |t - s| * |deriv Real.smoothTransition (t - s + 1)| ≤ 1 * 8 :=
              mul_le_mul (by rw [abs_of_nonpos htshi]; linarith) hderiv
                (abs_nonneg _) (by norm_num)
            _ = 8 := by norm_num
        linarith [neg_le_of_abs_le hterm]
      · have hterm : |(t - s) * deriv Real.smoothTransition (t - s + 1)| ≤ 8 := by
          rw [abs_mul]
          calc
            |t - s| * |deriv Real.smoothTransition (t - s + 1)| ≤ 1 * 8 :=
              mul_le_mul (by rw [abs_of_nonpos htshi]; linarith) hderiv
                (abs_nonneg _) (by norm_num)
            _ = 8 := by norm_num
        linarith [le_abs_self ((t - s) * deriv Real.smoothTransition (t - s + 1))]

/-- A smooth spatial exponential built from a mollified capped distance. -/
noncomputable def cauchyMassSpatialExponential {d : ℕ} (K : Set (Vec d))
    (R ε : ℝ) (n : ℕ) (x : Vec d) : ℝ :=
  Real.exp (ε *
    PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify K R n x)

/-- The time damping which cancels the exponential-weight flux term. -/
noncomputable def cauchyMassTimeDamping (s Lam ε t : ℝ) : ℝ :=
  Real.exp (-(2 * Lam * ε ^ 2) * cauchyMassTimePrimitive s t)

/-- The smooth bounded spacetime exponential weight used for a capped distance. -/
noncomputable def cauchyMassSmoothExponentialWeight {d : ℕ} (K : Set (Vec d))
    (s R Lam ε : ℝ) (n : ℕ) (z : Vec d × ℝ) : ℝ :=
  cauchyMassTimeDamping s Lam ε z.2 *
    cauchyMassSpatialExponential K R ε n z.1

theorem cauchyMassSpatialExponential_contDiff {d : ℕ} {K : Set (Vec d)}
    (hK : K.Nonempty) {R ε : ℝ} (hR : 0 ≤ R) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (cauchyMassSpatialExponential K R ε n) := by
  unfold cauchyMassSpatialExponential
  exact Real.contDiff_exp.comp
    ((contDiff_const.mul
      (PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify_properties hK hR n).1))

theorem cauchyMassSpatialExponential_bounds {d : ℕ} {K : Set (Vec d)}
    (hK : K.Nonempty) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 ≤ ε) (n : ℕ)
    (x : Vec d) :
    1 ≤ cauchyMassSpatialExponential K R ε n x ∧
      cauchyMassSpatialExponential K R ε n x ≤ Real.exp (ε * R) := by
  unfold cauchyMassSpatialExponential
  have hρ := PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify_properties hK hR n
  have hρ0 := (hρ.2.1 x).1
  have hρR := (hρ.2.1 x).2
  constructor
  · rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    positivity
  · apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hρR hε

theorem cauchyMassTimeDamping_contDiff (s Lam ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (cauchyMassTimeDamping s Lam ε) := by
  unfold cauchyMassTimeDamping
  exact Real.contDiff_exp.comp (contDiff_const.mul
    (cauchyMassTimePrimitive_contDiff s))

theorem cauchyMassTimeDamping_upper_bound {s Lam ε t : ℝ}
    (hLam : 0 ≤ Lam) :
    cauchyMassTimeDamping s Lam ε t ≤ Real.exp (2 * Lam * ε ^ 2) := by
  unfold cauchyMassTimeDamping
  apply Real.exp_le_exp.mpr
  have hprim := cauchyMassTimePrimitive_lower_bound s t
  have hC : 0 ≤ 2 * Lam * ε ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonpos_left hprim (neg_nonpos.mpr hC)
  convert hmul using 1
  ring_nf

theorem deriv_cauchyMassTimeDamping (s Lam ε t : ℝ) :
    deriv (cauchyMassTimeDamping s Lam ε) t =
      -(2 * Lam * ε ^ 2) * deriv (cauchyMassTimePrimitive s) t *
        cauchyMassTimeDamping s Lam ε t := by
  let c : ℝ := 2 * Lam * ε ^ 2
  have hp : HasDerivAt (cauchyMassTimePrimitive s)
      (deriv (cauchyMassTimePrimitive s) t) t :=
    ((cauchyMassTimePrimitive_contDiff s).differentiable (by norm_num) t).hasDerivAt
  have hlin : HasDerivAt (fun r : ℝ => -c * cauchyMassTimePrimitive s r)
      (-c * deriv (cauchyMassTimePrimitive s) t) t := hp.const_mul (-c)
  have hexp := (Real.hasDerivAt_exp (-c * cauchyMassTimePrimitive s t)).comp t hlin
  have hfun : cauchyMassTimeDamping s Lam ε =
      fun r => Real.exp (-c * cauchyMassTimePrimitive s r) := by
    funext r
    rfl
  rw [hfun]
  change deriv (Real.exp ∘ fun r => -c * cauchyMassTimePrimitive s r) t = _
  simpa [c, mul_assoc, mul_left_comm, mul_comm] using hexp.deriv

theorem deriv_cauchyMassTimePrimitive_of_lt {s t : ℝ} (hst : s < t) :
    deriv (cauchyMassTimePrimitive s) t = 1 := by
  have hev : cauchyMassTimePrimitive s =ᶠ[𝓝 t] fun r => r - s := by
    filter_upwards [Ioi_mem_nhds hst] with r hr
    exact cauchyMassTimePrimitive_eq_sub hr.le
  rw [hev.deriv_eq]
  simp

theorem cauchyMassSmoothExponentialWeight_contDiff {d : ℕ}
    {K : Set (Vec d)} (hK : K.Nonempty) {s R Lam ε : ℝ}
    (hR : 0 ≤ R) (n : ℕ) :
    ContDiff ℝ 1 (cauchyMassSmoothExponentialWeight K s R Lam ε n) := by
  unfold cauchyMassSmoothExponentialWeight
  apply PDE.Parabolic.WeakSlice.contDiff_prod
  · exact (cauchyMassTimeDamping_contDiff s Lam ε).of_le (by norm_num)
  · exact (cauchyMassSpatialExponential_contDiff hK hR n).of_le
      (m := (1 : ℕ∞)) (by norm_num)

theorem cauchyMassSmoothExponentialWeight_bound {d : ℕ}
    {K : Set (Vec d)} (hK : K.Nonempty) {s R Lam ε : ℝ}
    (hR : 0 ≤ R) (hLam : 0 ≤ Lam) (hε : 0 ≤ ε) (n : ℕ) (z : Vec d × ℝ) :
    |cauchyMassSmoothExponentialWeight K s R Lam ε n z| ≤
      Real.exp (ε * R + 2 * Lam * ε ^ 2) := by
  unfold cauchyMassSmoothExponentialWeight cauchyMassTimeDamping
    cauchyMassSpatialExponential
  rw [abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
  have hs := (cauchyMassSpatialExponential_bounds hK hR hε n z.1).2
  have ht := cauchyMassTimeDamping_upper_bound (s := s) (Lam := Lam)
    (ε := ε) (t := z.2) hLam
  calc
    Real.exp (-(2 * Lam * ε ^ 2) * cauchyMassTimePrimitive s z.2) *
        Real.exp (ε * PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify K R n z.1) ≤
      Real.exp (2 * Lam * ε ^ 2) * Real.exp (ε * R) :=
        mul_le_mul ht hs (Real.exp_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (ε * R + 2 * Lam * ε ^ 2) := by rw [← Real.exp_add]; ring_nf

theorem cauchyMassSmoothExponentialWeight_timeDeriv {d : ℕ}
    {K : Set (Vec d)} (hK : K.Nonempty) {s R Lam ε : ℝ}
    (hR : 0 ≤ R) (n : ℕ) {z : Vec d × ℝ} (hst : s < z.2) :
    parTimeDeriv (cauchyMassSmoothExponentialWeight K s R Lam ε n) z =
      -(2 * Lam * ε ^ 2) *
        cauchyMassSmoothExponentialWeight K s R Lam ε n z := by
  unfold cauchyMassSmoothExponentialWeight
  have hθ : ContDiff ℝ 1 (cauchyMassTimeDamping s Lam ε) :=
    (cauchyMassTimeDamping_contDiff s Lam ε).of_le (m := (1 : ℕ∞)) (by norm_num)
  have hζ : ContDiff ℝ 1 (cauchyMassSpatialExponential K R ε n) :=
    (cauchyMassSpatialExponential_contDiff hK hR n).of_le
      (m := (1 : ℕ∞)) (by norm_num)
  rw [PDE.Parabolic.WeakSlice.parTimeDeriv_prod hθ hζ z,
    deriv_cauchyMassTimeDamping, deriv_cauchyMassTimePrimitive_of_lt hst]
  ring

theorem cauchyMassSmoothExponentialWeight_timeDeriv_eq {d : ℕ}
    {K : Set (Vec d)} (hK : K.Nonempty) {s R Lam ε : ℝ}
    (hR : 0 ≤ R) (n : ℕ) (z : Vec d × ℝ) :
    parTimeDeriv (cauchyMassSmoothExponentialWeight K s R Lam ε n) z =
      -(2 * Lam * ε ^ 2) * deriv (cauchyMassTimePrimitive s) z.2 *
        cauchyMassSmoothExponentialWeight K s R Lam ε n z := by
  unfold cauchyMassSmoothExponentialWeight
  have hθ : ContDiff ℝ 1 (cauchyMassTimeDamping s Lam ε) :=
    (cauchyMassTimeDamping_contDiff s Lam ε).of_le (m := (1 : ℕ∞)) (by norm_num)
  have hζ : ContDiff ℝ 1 (cauchyMassSpatialExponential K R ε n) :=
    (cauchyMassSpatialExponential_contDiff hK hR n).of_le
      (m := (1 : ℕ∞)) (by norm_num)
  rw [PDE.Parabolic.WeakSlice.parTimeDeriv_prod hθ hζ z,
    deriv_cauchyMassTimeDamping]
  ring

theorem cauchyMassSpatialExponential_gradient_bound {d : ℕ}
    {K : Set (Vec d)} (hK : K.Nonempty) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 ≤ ε) (n : ℕ) (x : Vec d) :
    vecEuclideanNorm (spaceGradC1 (cauchyMassSpatialExponential K R ε n) x) ≤
      ε * cauchyMassSpatialExponential K R ε n x := by
  let ρ := PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify K R n
  let F : ℝ → ℝ := fun y => Real.exp (ε * y)
  change vecEuclideanNorm (classicalGradient (F ∘ ρ) x) ≤ ε * F (ρ x)
  have hρcd : ContDiff ℝ 1 ρ := by
    exact (PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify_properties
      hK hR n).1.of_le (by norm_num)
  have hFcd : ContDiff ℝ 1 F := by
    dsimp [F]
    fun_prop
  have hderivF (y : ℝ) : deriv F y = ε * Real.exp (ε * y) := by
    have hlin : HasDerivAt (fun r : ℝ => ε * r) ε y := by
      simpa using (hasDerivAt_id y).const_mul ε
    have hexp := (Real.hasDerivAt_exp (ε * y)).comp y hlin
    have hF' : HasDerivAt F (ε * Real.exp (ε * y)) y := by
      change HasDerivAt (fun r => Real.exp (ε * r))
        (ε * Real.exp (ε * y)) y
      exact hexp.congr_deriv (by ring)
    exact hF'.deriv
  have hgrad : classicalGradient (F ∘ ρ) x =
      (ε * Real.exp (ε * ρ x)) • classicalGradient ρ x := by
    ext i
    rw [classicalGradient_apply,
      PDE.Parabolic.Chain.vecFDeriv_comp hFcd hρcd x (basisVec i)]
    rw [hderivF]
    simp [classicalGradient_apply]
  have hρgrad : vecEuclideanNorm (classicalGradient ρ x) ≤ 1 :=
    (PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify_properties
      hK hR n).2.2.1 x
  have hnorm : vecEuclideanNorm (classicalGradient (F ∘ ρ) x) ≤
      ε * Real.exp (ε * ρ x) := by
    rw [hgrad, vecEuclideanNorm_smul, abs_of_nonneg (by positivity)]
    calc
      ε * Real.exp (ε * ρ x) * vecEuclideanNorm (classicalGradient ρ x) ≤
          ε * Real.exp (ε * ρ x) * 1 :=
        mul_le_mul_of_nonneg_left hρgrad (by positivity)
      _ = ε * Real.exp (ε * ρ x) := by ring
  simpa [F, cauchyMassSpatialExponential, ρ] using hnorm

theorem cauchyMassSmoothExponentialWeight_gradient_bound {d : ℕ}
    {K : Set (Vec d)} (hK : K.Nonempty) {s R Lam ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 ≤ ε) (n : ℕ) (z : Vec d × ℝ) :
    vecEuclideanNorm
      (parSpaceGrad (cauchyMassSmoothExponentialWeight K s R Lam ε n) z) ≤
        ε * cauchyMassSmoothExponentialWeight K s R Lam ε n z := by
  unfold cauchyMassSmoothExponentialWeight
  change vecEuclideanNorm (parSpaceGrad
      (fun w : Vec d × ℝ => cauchyMassTimeDamping s Lam ε w.2 *
        cauchyMassSpatialExponential K R ε n w.1) z) ≤
      ε * (cauchyMassTimeDamping s Lam ε z.2 *
        cauchyMassSpatialExponential K R ε n z.1)
  have hθ : ContDiff ℝ 1 (cauchyMassTimeDamping s Lam ε) :=
    (cauchyMassTimeDamping_contDiff s Lam ε).of_le (m := (1 : ℕ∞)) (by norm_num)
  have hζ : ContDiff ℝ 1 (cauchyMassSpatialExponential K R ε n) :=
    (cauchyMassSpatialExponential_contDiff hK hR n).of_le
      (m := (1 : ℕ∞)) (by norm_num)
  rw [PDE.Parabolic.WeakSlice.parSpaceGrad_prod hθ hζ z]
  rw [vecEuclideanNorm_smul]
  have htimepos : 0 < cauchyMassTimeDamping s Lam ε z.2 := by
    unfold cauchyMassTimeDamping
    exact Real.exp_pos _
  rw [abs_of_pos htimepos]
  have hsp := cauchyMassSpatialExponential_gradient_bound hK hR hε n z.1
  calc
    cauchyMassTimeDamping s Lam ε z.2 *
        vecEuclideanNorm (spaceGradC1 (cauchyMassSpatialExponential K R ε n) z.1) ≤
      cauchyMassTimeDamping s Lam ε z.2 *
        (ε * cauchyMassSpatialExponential K R ε n z.1) :=
          mul_le_mul_of_nonneg_left hsp htimepos.le
    _ = ε * (cauchyMassTimeDamping s Lam ε z.2 *
        cauchyMassSpatialExponential K R ε n z.1) := by ring

end PDE.Parabolic.Duality
