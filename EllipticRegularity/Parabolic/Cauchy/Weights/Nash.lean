module

public import PDEFoundation.Analysis.Inequalities.GaussianPoincare.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Gaussian weight calculations for Nash--Aronson estimates

This file records the scalar calculations used with the bounded, truncated
distance weight in the Nash--Aronson argument.  Spatial gradient information
is kept as an explicit hypothesis: for a one-Lipschitz truncated distance
`ρ`, the chain rule gives `|∇(ρ²)|² ≤ 4ρ²` almost everywhere.
-/

@[expose] public section

open MeasureTheory

namespace PDE.Parabolic.Cauchy.Weights

variable {d : ℕ}

/-- The unnormalized Gaussian integral on the project vector space. -/
theorem integral_exp_neg_mul_vecNormSq {b : ℝ} (_hb : 0 < b) :
    ∫ x : Vec d, Real.exp (-b * vecNormSq x) =
      Real.sqrt (Real.pi / b) ^ d := by
  exact PDE.GaussianPoincare.integral_exp_neg_mul_vecNormSq (d := d) b

/-- Exact normalization of a Gaussian with arbitrary positive quadratic scale. -/
theorem integral_exp_neg_vecNormSq_div {a : ℝ} (ha : 0 < a) :
    ∫ x : Vec d, Real.exp (-vecNormSq x / a) =
      (Real.pi * a) ^ ((d : ℝ) / 2) := by
  have hbase :=
    integral_exp_neg_mul_vecNormSq (d := d) (b := a⁻¹) (inv_pos.mpr ha)
  have hexp : ∀ x : Vec d,
      Real.exp (-vecNormSq x / a) = Real.exp (-a⁻¹ * vecNormSq x) := by
    intro x
    congr 1
    field_simp
  calc
    ∫ x : Vec d, Real.exp (-vecNormSq x / a) =
        ∫ x : Vec d, Real.exp (-a⁻¹ * vecNormSq x) := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact hexp x
    _ = Real.sqrt (Real.pi / a⁻¹) ^ d := hbase
    _ = (Real.pi * a) ^ ((d : ℝ) / 2) := by
      have hscale : Real.pi / a⁻¹ = Real.pi * a := by field_simp
      have hpos : 0 < Real.pi * a := by positivity
      rw [hscale, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
        ← Real.rpow_mul hpos.le]
      congr 1
      ring

/-- Gaussian tails are bounded by extracting half of the exponential at the
inner radius and integrating the remaining Gaussian exactly. -/
theorem gaussian_tail_integral_le {a R : ℝ} (ha : 0 < a) :
    ∫ x in {x : Vec d | R ^ 2 ≤ vecNormSq x},
        Real.exp (-vecNormSq x / a) ≤
      Real.exp (-R ^ 2 / (2 * a)) * (2 * Real.pi * a) ^ ((d : ℝ) / 2) := by
  let E : Set (Vec d) := {x | R ^ 2 ≤ vecNormSq x}
  let f : Vec d → ℝ := fun x => Real.exp (-vecNormSq x / a)
  let g : Vec d → ℝ := fun x => Real.exp (-vecNormSq x / (2 * a))
  have hf : Integrable f := by
    change Integrable (fun x : Vec d => Real.exp (-vecNormSq x / a))
    rw [show (fun x : Vec d => Real.exp (-vecNormSq x / a)) =
        fun x => Real.exp (-(a⁻¹) * vecNormSq x) from funext fun x => by
          congr 1
          field_simp]
    exact PDE.GaussianPoincare.integrable_exp_neg_mul_vecNormSq
      (d := d) (b := a⁻¹) (by positivity)
  have hg : Integrable g := by
    change Integrable (fun x : Vec d => Real.exp (-vecNormSq x / (2 * a)))
    rw [show (fun x : Vec d => Real.exp (-vecNormSq x / (2 * a))) =
        fun x => Real.exp (-((2 * a)⁻¹) * vecNormSq x) from funext fun x => by
          congr 1
          field_simp]
    exact PDE.GaussianPoincare.integrable_exp_neg_mul_vecNormSq
      (d := d) (b := (2 * a)⁻¹) (by positivity)
  have hpoint : ∀ x ∈ E, f x ≤ Real.exp (-R ^ 2 / (2 * a)) * g x := by
    intro x hx
    have hxq : R ^ 2 ≤ vecNormSq x := hx
    have hq : 0 ≤ vecNormSq x := vecNormSq_nonneg x
    have hsplit : -vecNormSq x / a =
        (-R ^ 2 / (2 * a)) + (-vecNormSq x / (2 * a)) +
          (-(vecNormSq x - R ^ 2) / (2 * a)) := by
      field_simp
      ring
    have hlast : Real.exp (-(vecNormSq x - R ^ 2) / (2 * a)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)
    calc
      f x = Real.exp (-R ^ 2 / (2 * a)) *
          Real.exp (-vecNormSq x / (2 * a)) *
            Real.exp (-(vecNormSq x - R ^ 2) / (2 * a)) := by
          dsimp [f]
          rw [hsplit, Real.exp_add, Real.exp_add]
      _ ≤ Real.exp (-R ^ 2 / (2 * a)) *
          Real.exp (-vecNormSq x / (2 * a)) := by
          calc
            _ = (Real.exp (-R ^ 2 / (2 * a)) *
                Real.exp (-vecNormSq x / (2 * a))) *
                  Real.exp (-(vecNormSq x - R ^ 2) / (2 * a)) := by ring
            _ ≤ (Real.exp (-R ^ 2 / (2 * a)) *
                Real.exp (-vecNormSq x / (2 * a))) * 1 :=
                  mul_le_mul_of_nonneg_left hlast (by positivity)
            _ = Real.exp (-R ^ 2 / (2 * a)) *
                Real.exp (-vecNormSq x / (2 * a)) := by ring
      _ = Real.exp (-R ^ 2 / (2 * a)) * g x := by rfl
  have hgscaled : Integrable
      (fun x : Vec d => Real.exp (-R ^ 2 / (2 * a)) * g x) := by
    simpa only [smul_eq_mul] using
      (hg.const_mul (Real.exp (-R ^ 2 / (2 * a))))
  have hE : MeasurableSet E := by
    have hcont : Continuous (fun x : Vec d => vecNormSq x) := by
      rw [show (fun x : Vec d => vecNormSq x) = fun x => ∑ i, x i ^ 2 from
        funext vecNormSq_eq_sum_sq]
      fun_prop
    exact (isClosed_le continuous_const hcont).measurableSet
  have hfirst := setIntegral_mono_on hf.integrableOn hgscaled.integrableOn hE hpoint
  have hsecond := setIntegral_le_integral (s := E) hgscaled
    (ae_of_all _ fun x => by positivity)
  calc
    ∫ x in E, f x ≤ ∫ x in E,
        Real.exp (-R ^ 2 / (2 * a)) * g x := hfirst
    _ ≤ ∫ x, Real.exp (-R ^ 2 / (2 * a)) * g x := hsecond
    _ = Real.exp (-R ^ 2 / (2 * a)) *
        (2 * Real.pi * a) ^ ((d : ℝ) / 2) := by
      rw [integral_const_mul, integral_exp_neg_vecNormSq_div (d := d) (by positivity)]
      congr 1
      ring_nf

/-- The exponential weight generated by a truncated squared distance. -/
noncomputable def nashGaussianWeight (A τ q : ℝ) : ℝ :=
  Real.exp (q / (4 * A * τ))

/-- Time derivative of the Gaussian weight, with `τ = h + σ`. -/
theorem hasDerivAt_nashGaussianWeight {A σ q h : ℝ}
    (hA : A ≠ 0) (hτ : h + σ ≠ 0) :
    HasDerivAt (fun z : ℝ => nashGaussianWeight A (z + σ) q)
      (nashGaussianWeight A (h + σ) q *
        (-q / (4 * A * (h + σ) ^ 2))) h := by
  have hden : HasDerivAt (fun z : ℝ => 4 * A * (z + σ)) (4 * A) h := by
    convert ((hasDerivAt_id h).add_const σ).const_mul (4 * A) using 1
    · funext z
      simp only [id_eq]
    · ring
  have harg : HasDerivAt (fun z : ℝ => q / (4 * A * (z + σ)))
      (-q / (4 * A * (h + σ) ^ 2)) h := by
    have hden_ne : 4 * A * (h + σ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hA) hτ
    convert (hasDerivAt_const h q).div hden hden_ne using 1
    field_simp
    ring_nf
  change HasDerivAt (fun z : ℝ => Real.exp (q / (4 * A * (z + σ))))
    (Real.exp (q / (4 * A * (h + σ))) * (-q / (4 * A * (h + σ) ^ 2))) h
  exact (Real.hasDerivAt_exp _).comp h harg

/-- Density-level differential inequality for the truncated-distance Gaussian
weight.  The premise `g ≤ 4q` is the squared-gradient estimate for `q=ρ²`
when `ρ` is one-Lipschitz. -/
theorem nashGaussianWeight_energy_density {A Λ τ q g : ℝ}
    (hΛ : 0 ≤ Λ) (hA : Λ < A) (hτ : 0 < τ)
    (hg : g ≤ 4 * q) :
    nashGaussianWeight A τ q *
        (-q / (4 * A * τ ^ 2) * nashGaussianWeight A τ q) +
      Λ * (nashGaussianWeight A τ q ^ 2 * g / (16 * A ^ 2 * τ ^ 2)) ≤
    -(1 - Λ / A) * q * nashGaussianWeight A τ q ^ 2 /
      (4 * A * τ ^ 2) := by
  have hApos : 0 < A := lt_of_le_of_lt hΛ hA
  have hden : 0 < 16 * A ^ 2 * τ ^ 2 := by positivity
  have hweight : 0 < nashGaussianWeight A τ q := by
    simp [nashGaussianWeight, Real.exp_pos]
  have hgrad := mul_le_mul_of_nonneg_left hg
    (show 0 ≤ Λ * nashGaussianWeight A τ q ^ 2 /
      (16 * A ^ 2 * τ ^ 2) from by positivity)
  dsimp [nashGaussianWeight] at hgrad ⊢
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hτne : τ ≠ 0 := ne_of_gt hτ
  field_simp at hgrad ⊢
  nlinarith [Real.exp_pos (q / (4 * A * τ))]

/-- A squared-distance truncation makes the exponential spatial weight
bounded. -/
theorem nashGaussianWeight_le_of_le {A τ R q : ℝ}
    (hAτ : 0 < A * τ) (hqR : q ≤ R ^ 2) :
    nashGaussianWeight A τ q ≤ nashGaussianWeight A τ (R ^ 2) := by
  apply Real.exp_le_exp.mpr
  have hden : 0 < 4 * A * τ := by
    simpa [mul_assoc] using mul_pos (by norm_num : (0 : ℝ) < 4) hAτ
  exact (div_le_div_iff_of_pos_right hden).2 (by linarith)

/-- Choosing `m = κ/(2(1-Λ/A))` makes the prefactor in the Nash energy
calculation cancel exactly. -/
theorem nashGaussianWeight_prefactor_identity {A Λ κ m : ℝ}
    (hΛ : 0 ≤ Λ) (hA : Λ < A) (hm : m = κ / (2 * (1 - Λ / A))) :
    κ = 2 * (1 - Λ / A) * m := by
  have hApos : 0 < A := lt_of_le_of_lt hΛ hA
  have hden : 2 * (1 - Λ / A) ≠ 0 := by
    apply ne_of_gt
    have : 0 < 1 - Λ / A := by
      rw [sub_pos, div_lt_one (by linarith)]
      exact hA
    positivity
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hgap : A - Λ ≠ 0 := ne_of_gt (by linarith)
  rw [hm]
  field_simp [hAne, hgap]

/-- The Nash threshold `κ = 1 + d/2` gives the verified off-diagonal
prefactor exponent `κ A/(A-Λ)`. -/
theorem nashGaussianWeight_prefactor_exponent (d : ℕ) {A Λ : ℝ}
    (hΛ : 0 ≤ Λ) (hA : Λ < A) :
    2 * (((d : ℝ) / 2 + 1) / (2 * (1 - Λ / A))) =
      (((d : ℝ) + 2) / 2) * A / (A - Λ) := by
  have hApos : 0 < A := lt_of_le_of_lt hΛ hA
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hgap : A - Λ ≠ 0 := ne_of_gt (by linarith)
  field_simp [hAne, hgap]

/-- Optimization in the spatial separation variable gives the quadratic
decay and the linear correction.  Taking `κ = (d+2)/2` and
`X = r^2/(4(t-s))` yields the coefficient `sqrt((d+2)/2)` in the
Nash--Aronson bound. -/
theorem nashGaussianWeight_optimized_rate {Λ κ X A : ℝ}
    (hΛ : 0 < Λ) (hκ : 0 < κ) (hX : κ * Λ < X) (hA : Λ < A) :
    -X / A + κ * A / (A - Λ) ≥
      -X / Λ + 2 * Real.sqrt (κ * X / Λ) := by
  have hApos : 0 < A := lt_trans hΛ hA
  let s : ℝ := X / Λ
  let z : ℝ := (A - Λ) / A
  have hspos : 0 < s := div_pos (lt_trans (mul_pos hκ hΛ) hX) hΛ
  have hΛne : Λ ≠ 0 := ne_of_gt hΛ
  have hzpos : 0 < z := div_pos (by linarith) hApos
  have hzlt : z < 1 := by
    dsimp [z]
    rw [div_lt_one hApos]
    linarith
  have hform : -X / A + κ * A / (A - Λ) = -s + s * z + κ / z := by
    dsimp [s, z]
    have hAne : A ≠ 0 := ne_of_gt hApos
    have hgap : A - Λ ≠ 0 := ne_of_gt (by linarith)
    field_simp [hAne, hgap]
    ring_nf
  have hsqrt1 : Real.sqrt (s * z) ^ 2 = s * z :=
    Real.sq_sqrt (le_of_lt (mul_pos hspos hzpos))
  have hsqrt2 : Real.sqrt (κ / z) ^ 2 = κ / z :=
    Real.sq_sqrt (le_of_lt (div_pos hκ hzpos))
  have hmul : Real.sqrt (s * z) * Real.sqrt (κ / z) =
      Real.sqrt (κ * s) := by
    rw [← Real.sqrt_mul (le_of_lt (mul_pos hspos hzpos))]
    congr 1
    dsimp [s, z]
    field_simp [hΛne, ne_of_gt hApos, ne_of_gt (by linarith : 0 < A - Λ)]
  have hAM : 2 * Real.sqrt (κ * s) ≤ s * z + κ / z := by
    nlinarith [sq_nonneg (Real.sqrt (s * z) - Real.sqrt (κ / z))]
  calc
    -X / A + κ * A / (A - Λ) = -s + s * z + κ / z := hform
    _ ≥ -s + 2 * Real.sqrt (κ * s) := by linarith
    _ = -X / Λ + 2 * Real.sqrt (κ * X / Λ) := by
      dsimp [s]
      rw [show -(X / Λ) = -X / Λ by ring,
        show κ * (X / Λ) = κ * X / Λ by ring]

/-- The optimized rate is attained at the explicit choice of `A` whenever
`X > κΛ`. -/
theorem nashGaussianWeight_optimized_rate_attained {Λ κ X : ℝ}
    (hΛ : 0 < Λ) (hκ : 0 < κ) (hX : κ * Λ < X) :
    ∃ A, Λ < A ∧
      -X / A + κ * A / (A - Λ) =
        -X / Λ + 2 * Real.sqrt (κ * X / Λ) := by
  let s : ℝ := X / Λ
  have hspos : 0 < s := div_pos (lt_trans (mul_pos hκ hΛ) hX) hΛ
  have hsκ : κ < s := by
    dsimp [s]
    apply (lt_div_iff₀ hΛ).2
    nlinarith [hX]
  let r : ℝ := Real.sqrt (κ / s)
  have hrpos : 0 < r := Real.sqrt_pos.mpr (div_pos hκ hspos)
  have hratio : κ / s < 1 := (div_lt_one hspos).2 hsκ
  have hrlt : r < 1 := (Real.sqrt_lt' one_pos).2 (by simpa using hratio)
  have hr2 : r ^ 2 = κ / s := Real.sq_sqrt (div_nonneg hκ.le hspos.le)
  let A : ℝ := Λ / (1 - r)
  have hdenpos : 0 < 1 - r := by linarith
  have hA : Λ < A := by
    apply (lt_div_iff₀ hdenpos).2
    nlinarith [mul_pos hΛ hrpos]
  have hApos : 0 < A := lt_trans hΛ hA
  have hΛne : Λ ≠ 0 := ne_of_gt hΛ
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hrne : r ≠ 0 := ne_of_gt hrpos
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hgap : A - Λ ≠ 0 := ne_of_gt (by linarith)
  have hz : (A - Λ) / A = r := by
    dsimp [A]
    field_simp [hΛne, hdenpos.ne']
    ring
  have hform : -X / A + κ * A / (A - Λ) =
      -s + s * ((A - Λ) / A) + κ / ((A - Λ) / A) := by
    have hA' : A ≠ 0 := ne_of_gt hApos
    dsimp [s]
    field_simp [hA', hgap, hΛne]
    ring
  have hsr : s * r = Real.sqrt (κ * s) := by
    symm
    apply (Real.sqrt_eq_iff_eq_sq (mul_nonneg hκ.le hspos.le)
      (mul_nonneg hspos.le hrpos.le)).2
    rw [mul_pow, hr2]
    field_simp [hsne]
  have hkr : κ / r = s * r := by
    apply (div_eq_iff hrne).2
    calc
      κ = s * r ^ 2 := by
        rw [hr2]
        field_simp [hsne]
      _ = (s * r) * r := by ring
  refine ⟨A, hA, ?_⟩
  calc
    -X / A + κ * A / (A - Λ) =
        -s + s * ((A - Λ) / A) + κ / ((A - Λ) / A) := hform
    _ = -s + 2 * Real.sqrt (κ * s) := by
      have hroots : Real.sqrt (κ * s) = Real.sqrt (s * κ) :=
        congrArg Real.sqrt (mul_comm κ s)
      rw [hz, hsr, hkr, hsr, hroots]
      ring
    _ = -X / Λ + 2 * Real.sqrt (κ * X / Λ) := by
      dsimp [s]
      rw [show -(X / Λ) = -X / Λ by ring,
        show κ * (X / Λ) = κ * X / Λ by ring]

/-- Pointwise truncation estimate used after splitting the weighted energy
integral at the threshold `q/(4Aτ) = m`. -/
theorem nashGaussianWeight_split_bound {δ m X : ℝ}
    (hδ : 0 < δ) (hm : 0 ≤ m) (hX : 0 ≤ X) :
    2 * δ * (m - X) * Real.exp (2 * X) ≤
      2 * δ * m * Real.exp (2 * m) := by
  by_cases hXm : X ≤ m
  · have hexp : Real.exp (2 * X) ≤ Real.exp (2 * m) :=
      Real.exp_le_exp.mpr (by linarith)
    have hcoeff : 0 ≤ 2 * δ * (m - X) := by positivity
    calc
      2 * δ * (m - X) * Real.exp (2 * X) ≤
          2 * δ * (m - X) * Real.exp (2 * m) :=
            mul_le_mul_of_nonneg_left hexp hcoeff
      _ ≤ 2 * δ * m * Real.exp (2 * m) := by
            calc
              _ = (2 * δ * (m - X)) * Real.exp (2 * m) := by ring
              _ ≤ (2 * δ * m) * Real.exp (2 * m) := by
                apply mul_le_mul_of_nonneg_right
                · nlinarith
                · exact Real.exp_nonneg _
              _ = 2 * δ * m * Real.exp (2 * m) := by ring
  · have hcoeff : m - X < 0 := by linarith
    have hright : 0 ≤ 2 * δ * m * Real.exp (2 * m) := by positivity
    have hcoeff' : 2 * δ * (m - X) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) hcoeff
    have hleft' : 2 * δ * (m - X) * Real.exp (2 * X) < 0 :=
      mul_neg_of_neg_of_pos hcoeff' (Real.exp_pos _)
    have hleft : 2 * δ * (m - X) * Real.exp (2 * X) ≤ 0 := le_of_lt hleft'
    exact hleft.trans hright

end PDE.Parabolic.Cauchy.Weights
