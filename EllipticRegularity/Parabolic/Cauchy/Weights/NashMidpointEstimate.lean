module

public import EllipticRegularity.Parabolic.Cauchy.Weights.NashWeightedL2
public import EllipticRegularity.Parabolic.Cauchy.Weights.NashGeometry
public import EllipticRegularity.Parabolic.Cauchy.Weights.WeightedDuality
public import EllipticRegularity.Parabolic.Cauchy.Weights.Rate
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Midpoint assembly for the Nash--Aronson estimate

This file combines the two weighted endpoint estimates with the support
geometry and the duality identity. The evolution interface is supplied as
ordinary solution data, so all remaining steps are pure estimates.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Weights

open MeasureTheory Set

variable {d : ℕ}

private theorem sqrt_product_le_of_square_bounds {x y C B D : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hC : 0 ≤ C) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hxB : x ≤ C * B ^ 2) (hyD : y ≤ C * D ^ 2) :
    Real.sqrt x * Real.sqrt y ≤ C * B * D := by
  have hxy : x * y ≤ (C * B * D) ^ 2 := by
    calc
      x * y ≤ (C * B ^ 2) * y := mul_le_mul_of_nonneg_right hxB hy
      _ ≤ (C * B ^ 2) * (C * D ^ 2) :=
        mul_le_mul_of_nonneg_left hyD (mul_nonneg hC (sq_nonneg B))
      _ = (C * B * D) ^ 2 := by ring
  calc
    Real.sqrt x * Real.sqrt y = Real.sqrt (x * y) := (Real.sqrt_mul hx y).symm
    _ ≤ Real.sqrt ((C * B * D) ^ 2) := Real.sqrt_le_sqrt hxy
    _ = C * B * D := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hC hB) hD)]

private theorem weighted_profile_moment_eq {A H R : ℝ} {K : Set (Vec d)}
    (hA : 0 < A) (hH : 0 < H) (_hK : K.Nonempty) (_hR : 0 ≤ R)
    (v : Vec d → ℝ) :
    (∫ x : Vec d,
      |Real.exp (truncatedEuclideanSetDistance K R x ^ 2 / (4 * A * H)) * v x| ^ (2 : ℝ)) =
      ∫ x : Vec d,
        Real.exp (truncatedEuclideanSetDistance K R x ^ 2 / (2 * A * H)) * v x ^ 2 := by
  apply integral_congr_ae
  filter_upwards [] with x
  let q : ℝ := truncatedEuclideanSetDistance K R x ^ 2 / (4 * A * H)
  have hq : 2 * q = truncatedEuclideanSetDistance K R x ^ 2 / (2 * A * H) := by
    dsimp [q]
    field_simp [ne_of_gt hA, ne_of_gt hH]
    ring
  calc
    |Real.exp q * v x| ^ (2 : ℝ) = (Real.exp q * v x) ^ 2 := by
      rw [Real.rpow_two, sq_abs]
    _ = Real.exp (2 * q) * v x ^ 2 := by
      have hexp : Real.exp q ^ 2 = Real.exp (2 * q) := by
        rw [show 2 * q = q + q by ring, Real.exp_add]
        ring
      rw [mul_pow, hexp]
    _ = Real.exp (truncatedEuclideanSetDistance K R x ^ 2 / (2 * A * H)) * v x ^ 2 := by
      rw [hq]

/-- Fixed-weight off-diagonal estimate from the two weighted endpoint
estimates. `pairing` is the adjoint midpoint identity; PDE existence and
duality are isolated from this analytic assembly. -/
theorem cauchy_nash_midpoint_offDiagonal_fixed_weight
    {Lam s H A r Bf Bg : ℝ}
    (hd : 0 < d) (hLam : 1 ≤ Lam) (hH : 0 < H) (hA : Lam < A)
    (hr : 0 ≤ r) (hBf : 0 < Bf) (hBg : 0 < Bg)
    {Kf Kg : Set (Vec d)} (hKf : Kf.Nonempty) (hKg : Kg.Nonempty)
    (hsep : ∀ x ∈ Kf, ∀ y ∈ Kg, r ^ 2 ≤ euclideanSqDist x y)
    {a b : ParCoeffField d}
    (ha : IsParabolicCoeff 1 Lam a univ (Icc s (s + H)))
    (hb : IsParabolicCoeff 1 Lam b univ (Icc (s + H) ((s + H) + H)))
    (f g : Vec d → ℝ) (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (hg1 : Integrable g volume) (hg2 : MemLp g 2 volume)
    (hL1f : ∫ x : Vec d, |f x| ≤ Bf) (hL1g : ∫ x : Vec d, |g x| ≤ Bg)
    (hfsupp : ∀ᵐ x : Vec d ∂volume, x ∉ Kf → f x = 0)
    (hgsupp : ∀ᵐ x : Vec d ∂volume, x ∉ Kg → g x = 0)
    {u : ParH1Function (univ : Set (Vec d)) (Icc s (s + H))}
    (hu : IsCauchySolution a s (s + H) f u)
    {w : ParH1Function (univ : Set (Vec d)) (Icc (s + H) ((s + H) + H))}
    (hw : IsCauchySolution b (s + H) ((s + H) + H) g w)
    {q qEnd : Vec d → ℝ} (hq : Integrable (fun x => q x * qEnd x))
    (hpair : ∫ x, q x * qEnd x =
      ∫ x, u.toFun (x, s + H) * w.toFun (x, (s + H) + H)) :
    Integrable (fun x => q x * qEnd x) ∧
    |∫ x, q x * qEnd x| ≤
      nashWeightedL2Constant d *
        Real.exp ((((d : ℝ) + 2) / 2) / (1 - Lam / A)) *
        H ^ (-(d : ℝ) / 2) * Real.exp (-r ^ 2 / (8 * A * H)) * Bf * Bg := by
  let ρf : Vec d → ℝ := truncatedEuclideanSetDistance Kf r
  let ρg : Vec d → ℝ := truncatedEuclideanSetDistance Kg r
  let F : Vec d → ℝ := fun x =>
    Real.exp (ρf x ^ 2 / (4 * A * H)) * u.toFun (x, s + H)
  let G : Vec d → ℝ := fun x =>
    Real.exp (ρg x ^ 2 / (4 * A * H)) * w.toFun (x, (s + H) + H)
  have hR : 0 ≤ r := hr
  have hρf : ∀ x, 0 ≤ ρf x := fun x => truncatedEuclideanSetDistance_nonneg hKf hr x
  have hρg : ∀ x, 0 ≤ ρg x := fun x => truncatedEuclideanSetDistance_nonneg hKg hr x
  have hρsep : ∀ x, r ≤ ρf x + ρg x := by
    intro x
    exact truncatedEuclideanSetDistance_sum_ge_of_separated hKf hKg hr le_rfl hsep x
  have hUweighted := cauchy_nash_truncated_weighted_l2 hKf hd hH hLam hA hBf
    ha hf1 hf2 hL1f hfsupp (u := u) hu (R := r) hr
  have hWweighted := cauchy_nash_truncated_weighted_l2 hKg hd hH hLam hA hBg
    hb hg1 hg2 hL1g hgsupp (u := w) hw (R := r) hr
  have hApos : 0 < A := by linarith [hLam]
  let M : ℝ := nashWeightedL2Constant d *
    Real.exp ((((d : ℝ) + 2) / 2) / (1 - Lam / A)) * H ^ (-(d : ℝ) / 2)
  have hM : 0 < M := by
    dsimp [M]
    positivity [nashWeightedL2Constant_pos hd]
  have hUbound : ∫ x : Vec d, Real.exp (ρf x ^ 2 / (2 * A * H)) *
      u.toFun (x, s + H) ^ 2 ≤ M * Bf ^ 2 := by
    simpa [M, ρf, mul_assoc] using hUweighted
  have hWbound : ∫ x : Vec d, Real.exp (ρg x ^ 2 / (2 * A * H)) *
      w.toFun (x, (s + H) + H) ^ 2 ≤ M * Bg ^ 2 := by
    simpa [M, ρg, mul_assoc] using hWweighted
  have hFmem : MemLp F 2 volume := by
    dsimp [F, ρf]
    exact cauchy_nash_truncated_weighted_slice_memLp
      (s := s) (T := s + H) (t := s + H) (A := A) (H := H) (R := r) (Lam := Lam)
      (by linarith) hApos hH hr ⟨by linarith, le_rfl⟩ ha hf2 u hu Kf hKf
  have hGmem : MemLp G 2 volume := by
    dsimp [G, ρg]
    exact cauchy_nash_truncated_weighted_slice_memLp
      (s := s + H) (T := (s + H) + H) (t := (s + H) + H) (A := A) (H := H) (R := r) (Lam := Lam)
      (by linarith) hApos hH hr ⟨by linarith, le_rfl⟩ hb hg2 w hw Kg hKg
  have hUslice : MemLp (fun x : Vec d => u.toFun (x, s + H)) 2 volume :=
    cauchy_slice_memLp_of_solution (by linarith) ⟨by linarith, le_rfl⟩ ha hf2 u hu
  have hWslice : MemLp (fun x : Vec d => w.toFun (x, (s + H) + H)) 2 volume :=
    cauchy_slice_memLp_of_solution (by linarith) ⟨by linarith, le_rfl⟩ hb hg2 w hw
  have hbilin := weighted_bilinear_offDiagonal hApos hH hr
    (fun x => u.toFun (x, s + H)) (fun x => w.toFun (x, (s + H) + H)) ρf ρg
    hρf hρg hρsep hUslice hWslice
    (by
      simpa [F, G, ρf, ρg] using hFmem)
    (by
      simpa [F, G, ρf, ρg] using hGmem)
  have hFmoment : ∫ x : Vec d, |F x| ^ (2 : ℝ) =
      ∫ x : Vec d, Real.exp (ρf x ^ 2 / (2 * A * H)) * u.toFun (x, s + H) ^ 2 := by
    simpa [F, ρf] using weighted_profile_moment_eq hApos hH hKf hr
      (fun x => u.toFun (x, s + H))
  have hGmoment : ∫ x : Vec d, |G x| ^ (2 : ℝ) =
      ∫ x : Vec d, Real.exp (ρg x ^ 2 / (2 * A * H)) * w.toFun (x, (s + H) + H) ^ 2 := by
    simpa [G, ρg] using weighted_profile_moment_eq hApos hH hKg hr
      (fun x => w.toFun (x, (s + H) + H))
  have hI1 : 0 ≤ ∫ x : Vec d, |F x| ^ (2 : ℝ) := by
    apply integral_nonneg_of_ae
    exact ae_of_all _ fun x => Real.rpow_nonneg (abs_nonneg _) _
  have hI2 : 0 ≤ ∫ x : Vec d, |G x| ^ (2 : ℝ) := by
    apply integral_nonneg_of_ae
    exact ae_of_all _ fun x => Real.rpow_nonneg (abs_nonneg _) _
  have hroots :
      (∫ x : Vec d, |F x| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∫ x : Vec d, |G x| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤ M * Bf * Bg := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    rw [hFmoment, hGmoment]
    exact sqrt_product_le_of_square_bounds (by
      apply integral_nonneg_of_ae
      exact ae_of_all _ fun x => mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)) (by
      apply integral_nonneg_of_ae
      exact ae_of_all _ fun x => mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))
      hM.le hBf.le hBg.le (by simpa [hFmoment] using hUbound)
      (by simpa [hGmoment] using hWbound)
  have hbound : |∫ x, q x * qEnd x| ≤
      nashWeightedL2Constant d *
        Real.exp ((((d : ℝ) + 2) / 2) / (1 - Lam / A)) *
        H ^ (-(d : ℝ) / 2) * Real.exp (-r ^ 2 / (8 * A * H)) * Bf * Bg := by
    calc
    |∫ x, q x * qEnd x| =
        |∫ x, u.toFun (x, s + H) * w.toFun (x, (s + H) + H)| := by rw [hpair]
    _ ≤ Real.exp (-r ^ 2 / (8 * A * H)) *
        (∫ x, |F x| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∫ x, |G x| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
      convert hbilin using 1
    _ ≤ Real.exp (-r ^ 2 / (8 * A * H)) * (M * Bf * Bg) := by
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left hroots (Real.exp_nonneg (-r ^ 2 / (8 * A * H)))
    _ = nashWeightedL2Constant d *
        Real.exp ((((d : ℝ) + 2) / 2) / (1 - Lam / A)) *
        H ^ (-(d : ℝ) / 2) * Real.exp (-r ^ 2 / (8 * A * H)) * Bf * Bg := by
      dsimp [M]
      ring
  exact ⟨hq, hbound⟩

/-- The exact coefficient optimization, including the low-separation range,
for the midpoint Gaussian weights. -/
theorem nash_midpoint_weight_rate {d : ℕ} {Lam H r : ℝ}
    (hLam : 0 < Lam) (hH : 0 < H) (hr : 0 ≤ r) :
    ∃ A, Lam < A ∧
      Real.exp ((((d : ℝ) + 2) / 2) / (1 - Lam / A)) *
          Real.exp (-r ^ 2 / (8 * A * H)) ≤
        Real.exp (-r ^ 2 / (8 * Lam * H) +
          Real.sqrt (((d : ℝ) + 2) / 2) * r / Real.sqrt (Lam * (2 * H)) +
          2 * (((d : ℝ) + 2) / 2)) := by
  let κ : ℝ := ((d : ℝ) + 2) / 2
  let X : ℝ := r ^ 2 / (8 * H)
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hX : 0 ≤ X := by dsimp [X]; positivity
  obtain ⟨A, hA, hopt⟩ := nashGaussianWeight_rate_with_lowRange_constant
    hLam hκ hX
  have hApos : 0 < A := lt_trans hLam hA
  have hδ : 0 < 1 - Lam / A := by
    have hratio : Lam / A < 1 := (div_lt_one₀ (by linarith)).2 hA
    linarith
  have hfrac : κ / (1 - Lam / A) = κ * A / (A - Lam) := by
    have hden : 1 - Lam / A = (A - Lam) / A := by
      rw [← div_self (ne_of_gt hApos), sub_div]
    rw [hden]
    field_simp [ne_of_gt hApos, ne_of_gt (show A - Lam > 0 by linarith)]
  have hspace : X / A = r ^ 2 / (8 * A * H) := by
    dsimp [X]
    field_simp [ne_of_gt hApos, ne_of_gt hH]
  have hXdiv : X / Lam = r ^ 2 / (8 * Lam * H) := by
    dsimp [X]
    field_simp [ne_of_gt hLam, ne_of_gt hH]
  let D : ℝ := Lam * (2 * H)
  have hD : 0 < D := by dsimp [D]; positivity
  have hroot : 2 * Real.sqrt (κ * X / Lam) =
      Real.sqrt κ * r / Real.sqrt D := by
    have hleftNonneg : 0 ≤ 2 * Real.sqrt (κ * X / Lam) := by positivity
    have hrightNonneg : 0 ≤ Real.sqrt κ * r / Real.sqrt D := by
      exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hr) (Real.sqrt_nonneg _)
    have hleftSq : (2 * Real.sqrt (κ * X / Lam)) ^ 2 =
        (Real.sqrt κ * r / Real.sqrt D) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg (mul_nonneg hκ.le hX) hLam.le)]
      norm_num
      rw [div_pow, mul_pow, Real.sq_sqrt hD.le, Real.sq_sqrt hκ.le]
      dsimp [D, X]
      field_simp [ne_of_gt hLam, ne_of_gt hH]
      ring
    exact (sq_eq_sq₀ hleftNonneg hrightNonneg).1 hleftSq
  have hrate : κ / (1 - Lam / A) - r ^ 2 / (8 * A * H) ≤
      -r ^ 2 / (8 * Lam * H) +
        Real.sqrt κ * r / Real.sqrt (Lam * (2 * H)) + 2 * κ := by
    calc
      κ / (1 - Lam / A) - r ^ 2 / (8 * A * H) =
          -X / A + κ * A / (A - Lam) := by rw [hfrac, ← hspace]; ring
      _ ≤ -X / Lam + 2 * Real.sqrt (κ * X / Lam) + 2 * κ := hopt
      _ = -r ^ 2 / (8 * Lam * H) +
          Real.sqrt κ * r / Real.sqrt (Lam * (2 * H)) + 2 * κ := by
        rw [neg_div, hXdiv, hroot]
        ring
  refine ⟨A, hA, ?_⟩
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simpa only [κ, sub_eq_add_neg, neg_div] using hrate

/-- The dimension-only multiplicative constant after optimizing the Gaussian
weight parameter. -/
noncomputable def nashMidpointConstant (d : ℕ) : ℝ :=
  nashWeightedL2Constant d * 2 ^ ((d : ℝ) / 2) *
    Real.exp (2 * (((d : ℝ) + 2) / 2))

theorem nashMidpointConstant_pos {d : ℕ} (hd : 0 < d) :
    0 < nashMidpointConstant d := by
  unfold nashMidpointConstant
  positivity [nashWeightedL2Constant_pos hd]

/-- Optimized midpoint estimate with the exact Nash--Aronson exponent and a
dimension-only prefactor. -/
theorem cauchy_nash_midpoint_offDiagonal
    {Lam s H r Bf Bg : ℝ}
    (hd : 0 < d) (hLam : 1 ≤ Lam) (hH : 0 < H)
    (hr : 0 ≤ r) (hBf : 0 < Bf) (hBg : 0 < Bg)
    {Kf Kg : Set (Vec d)} (hKf : Kf.Nonempty) (hKg : Kg.Nonempty)
    (hsep : ∀ x ∈ Kf, ∀ y ∈ Kg, r ^ 2 ≤ euclideanSqDist x y)
    {a b : ParCoeffField d}
    (ha : IsParabolicCoeff 1 Lam a univ (Icc s (s + H)))
    (hb : IsParabolicCoeff 1 Lam b univ (Icc (s + H) ((s + H) + H)))
    (f g : Vec d → ℝ) (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (hg1 : Integrable g volume) (hg2 : MemLp g 2 volume)
    (hL1f : ∫ x : Vec d, |f x| ≤ Bf) (hL1g : ∫ x : Vec d, |g x| ≤ Bg)
    (hfsupp : ∀ᵐ x : Vec d ∂volume, x ∉ Kf → f x = 0)
    (hgsupp : ∀ᵐ x : Vec d ∂volume, x ∉ Kg → g x = 0)
    {u : ParH1Function (univ : Set (Vec d)) (Icc s (s + H))}
    (hu : IsCauchySolution a s (s + H) f u)
    {w : ParH1Function (univ : Set (Vec d)) (Icc (s + H) ((s + H) + H))}
    (hw : IsCauchySolution b (s + H) ((s + H) + H) g w)
    {q qEnd : Vec d → ℝ} (hq : Integrable (fun x => q x * qEnd x))
    (hpair : ∫ x, q x * qEnd x =
      ∫ x, u.toFun (x, s + H) * w.toFun (x, (s + H) + H)) :
    Integrable (fun x => q x * qEnd x) ∧
      |∫ x, q x * qEnd x| ≤
        nashMidpointConstant d * (2 * H) ^ (-(d : ℝ) / 2) *
          Real.exp (-r ^ 2 / (8 * Lam * H) +
            Real.sqrt (((d : ℝ) + 2) / 2) * r / Real.sqrt (Lam * (2 * H))) * Bf * Bg := by
  let κ : ℝ := ((d : ℝ) + 2) / 2
  let p : ℝ := (d : ℝ) / 2
  obtain ⟨A, hA, hrate⟩ := nash_midpoint_weight_rate
    (lt_of_lt_of_le (by norm_num) hLam) hH hr
  have hfixed := cauchy_nash_midpoint_offDiagonal_fixed_weight
    (A := A) hd hLam hH hA hr hBf hBg hKf hKg hsep ha hb f g hf1 hf2 hg1 hg2
    hL1f hL1g hfsupp hgsupp hu hw hq hpair
  have hpow : H ^ (-p) = 2 ^ p * (2 * H) ^ (-p) := by
    have hmul : (2 * H) ^ (-p) = (2 : ℝ) ^ (-p) * H ^ (-p) :=
      Real.mul_rpow (by norm_num) hH.le
    have h2 : (2 : ℝ) ^ p * (2 : ℝ) ^ (-p) = 1 := by
      rw [← Real.rpow_add (by norm_num) p (-p)]
      simp
    calc
      H ^ (-p) = ((2 : ℝ) ^ p * (2 : ℝ) ^ (-p)) * H ^ (-p) := by rw [h2, one_mul]
      _ = (2 : ℝ) ^ p * ((2 : ℝ) ^ (-p) * H ^ (-p)) := by ring
      _ = (2 : ℝ) ^ p * (2 * H) ^ (-p) := by rw [← hmul]
  have hpexp : (-(d : ℝ) / 2) = -p := by
    dsimp [p]
    ring
  have htimeexp : (2 * H) ^ (-p) = (2 * H) ^ (-(d : ℝ) / 2) := by
    congr 1
    dsimp [p]
    ring
  have hfixedBound : |∫ x, q x * qEnd x| ≤
      nashWeightedL2Constant d *
        Real.exp (κ / (1 - Lam / A)) * H ^ (-p) *
          Real.exp (-r ^ 2 / (8 * A * H)) * Bf * Bg := by
    simpa only [κ, hpexp] using hfixed.2
  have hExpBound :
      Real.exp (κ / (1 - Lam / A)) * Real.exp (-r ^ 2 / (8 * A * H)) ≤
        Real.exp (-r ^ 2 / (8 * Lam * H) +
          Real.sqrt κ * r / Real.sqrt (Lam * (2 * H))) * Real.exp (2 * κ) := by
    have := hrate
    rw [Real.exp_add] at this
    simpa only [κ] using this
  have hconstpos : 0 < nashWeightedL2Constant d := nashWeightedL2Constant_pos hd
  have hNtime : 0 ≤ nashWeightedL2Constant d * H ^ (-p) :=
    mul_nonneg hconstpos.le (Real.rpow_nonneg hH.le _)
  have hBprod : 0 ≤ Bf * Bg := mul_nonneg hBf.le hBg.le
  have hExpMul := mul_le_mul_of_nonneg_left hExpBound hNtime
  have hExpMul' := mul_le_mul_of_nonneg_right hExpMul hBprod
  have hlast :
      (nashWeightedL2Constant d * H ^ (-p)) *
          (Real.exp (-r ^ 2 / (8 * Lam * H) +
            Real.sqrt κ * r / Real.sqrt (Lam * (2 * H))) * Real.exp (2 * κ)) *
          (Bf * Bg) =
        nashMidpointConstant d * (2 * H) ^ (-(d : ℝ) / 2) *
          Real.exp (-r ^ 2 / (8 * Lam * H) +
            Real.sqrt κ * r / Real.sqrt (Lam * (2 * H))) * Bf * Bg := by
    rw [hpow, htimeexp]
    dsimp [nashMidpointConstant, κ]
    ring
  constructor
  · exact hq
  · calc
      |∫ x, q x * qEnd x| ≤
          nashWeightedL2Constant d *
            Real.exp (κ / (1 - Lam / A)) * H ^ (-p) *
            Real.exp (-r ^ 2 / (8 * A * H)) * Bf * Bg := hfixedBound
      _ = (nashWeightedL2Constant d * H ^ (-p)) *
          (Real.exp (κ / (1 - Lam / A)) *
            Real.exp (-r ^ 2 / (8 * A * H))) * (Bf * Bg) := by ring
      _ ≤ (nashWeightedL2Constant d * H ^ (-p)) *
          (Real.exp (-r ^ 2 / (8 * Lam * H) +
            Real.sqrt κ * r / Real.sqrt (Lam * (2 * H))) * Real.exp (2 * κ)) *
            (Bf * Bg) := by
              simpa [mul_assoc] using hExpMul'
      _ = nashMidpointConstant d * (2 * H) ^ (-(d : ℝ) / 2) *
          Real.exp (-r ^ 2 / (8 * Lam * H) +
            Real.sqrt κ * r / Real.sqrt (Lam * (2 * H))) * Bf * Bg := by
              simpa only [κ] using hlast

end PDE.Parabolic.Cauchy.Weights
