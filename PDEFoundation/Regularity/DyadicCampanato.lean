module

public import PDEFoundation.Regularity.CenteredCubeAverage
public import PDEFoundation.Regularity.Holder
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Covering.DensityTheorem

/-!
# Dyadic centered-cube Campanato estimates

This module turns normalized `L²` oscillation decay on dyadic centered axis
cubes into a Hölder estimate for the precise representative.

The cubes use the inherited supremum norm on `Vec d`. The final estimate is
also exported using the explicit Euclidean magnitude, with no loss in the
constant. Every geometric-series factor is displayed; in particular, the
tail constant is

`sqrt (2 ^ d) / (1 - 2 ^ (-α))`.

The proof architecture is extracted from the native-vector Campanato
development in Superdiffusion and placed in the common foundation.
-/

@[expose] public section

namespace PDE

open Filter MeasureTheory Topology

noncomputable section

variable {d : ℕ}

/-- Uniform Campanato control on the dyadic centered cubes of initial
half-side `R`, with normalized `L²` oscillation bounded by `K r ^ α`. -/
def DyadicCenteredCubeCampanatoBoundOn
    (u : Vec d → ℝ) (S : Set (Vec d)) (R α K : ℝ) : Prop :=
  ∀ x ∈ S, ∀ n : ℕ,
    centeredCubeL2Oscillation u x (R / (2 : ℝ) ^ n) ≤
      K * (R / (2 : ℝ) ^ n) ^ α

/-- The sequence of centered-cube averages at half-sides `R / 2 ^ n`. -/
def dyadicCenteredCubeMeanSeq
    (u : Vec d → ℝ) (R : ℝ) (x : Vec d) (n : ℕ) : ℝ :=
  centeredCubeAverage u x (R / (2 : ℝ) ^ n)

/-- The precise representative selected by dyadic centered-cube averages. -/
def dyadicCenteredCubeRepresentative
    (u : Vec d → ℝ) (R : ℝ) (x : Vec d) : ℝ :=
  limUnder atTop (dyadicCenteredCubeMeanSeq u R x)

/-- The exact geometric-tail constant for dyadic centered cubes. -/
def dyadicCampanatoTailConst (d : ℕ) (α : ℝ) : ℝ :=
  Real.sqrt ((2 : ℝ) ^ d) / (1 - (2 : ℝ) ^ (-α))

/-- The explicit constant in the local dyadic Campanato-to-Hölder estimate. -/
def dyadicCampanatoHolderConst (d : ℕ) (α : ℝ) : ℝ :=
  (2 * dyadicCampanatoTailConst d α +
      2 * Real.sqrt ((2 : ℝ) ^ d) * (2 : ℝ) ^ α) *
    (2 : ℝ) ^ α

private theorem dyadicRadius_pos {R : ℝ} (hR : 0 < R) (n : ℕ) :
    0 < R / (2 : ℝ) ^ n :=
  div_pos hR (by positivity)

private theorem dyadicRadius_antitone {R : ℝ} (hR : 0 < R)
    {m n : ℕ} (hmn : m ≤ n) :
    R / (2 : ℝ) ^ n ≤ R / (2 : ℝ) ^ m := by
  apply div_le_div_of_nonneg_left hR.le (by positivity)
  exact pow_le_pow_right₀ (by norm_num) hmn

private theorem dyadicRadius_rpow {R : ℝ} (hR : 0 ≤ R) (α : ℝ) :
    ∀ n : ℕ,
      (R / (2 : ℝ) ^ n) ^ α =
        R ^ α * ((2 : ℝ) ^ (-α)) ^ n
  | 0 => by simp
  | n + 1 => by
      have hsplit :
          R / (2 : ℝ) ^ (n + 1) =
            (R / (2 : ℝ) ^ n) / 2 := by
        rw [pow_succ]
        ring
      have hrn : 0 ≤ R / (2 : ℝ) ^ n :=
        div_nonneg hR (by positivity)
      rw [hsplit, Real.div_rpow hrn (by norm_num),
        dyadicRadius_rpow hR α n, pow_succ,
        Real.rpow_neg (by norm_num)]
      field_simp

variable {u : Vec d → ℝ} {S : Set (Vec d)} {R α K : ℝ}

/-- One dyadic comparison of nested centered-cube averages. -/
theorem dist_dyadicCenteredCubeMeanSeq_succ_le
    {x : Vec d} (hR : 0 < R)
    (hu : IntegrableOn u (centeredAxisCube x R))
    (hu2 : IntegrableOn (fun z => u z ^ 2) (centeredAxisCube x R))
    (hcamp : DyadicCenteredCubeCampanatoBoundOn u S R α K)
    (hx : x ∈ S) (n : ℕ) :
    dist (dyadicCenteredCubeMeanSeq u R x n)
        (dyadicCenteredCubeMeanSeq u R x (n + 1)) ≤
      (Real.sqrt ((2 : ℝ) ^ d) * (K * R ^ α)) *
        ((2 : ℝ) ^ (-α)) ^ n := by
  have hrn : 0 < R / (2 : ℝ) ^ n :=
    dyadicRadius_pos hR n
  have hrn1 : 0 < R / (2 : ℝ) ^ (n + 1) :=
    dyadicRadius_pos hR (n + 1)
  have hsub :
      centeredAxisCube x (R / (2 : ℝ) ^ (n + 1)) ⊆
        centeredAxisCube x (R / (2 : ℝ) ^ n) :=
    centeredAxisCube_mono x
      (dyadicRadius_antitone hR (Nat.le_succ n))
  have hrnR : R / (2 : ℝ) ^ n ≤ R := by
    simpa using dyadicRadius_antitone hR (Nat.zero_le n)
  have houter :
      centeredAxisCube x (R / (2 : ℝ) ^ n) ⊆
        centeredAxisCube x R :=
    centeredAxisCube_mono x hrnR
  have hun :
      IntegrableOn u (centeredAxisCube x (R / (2 : ℝ) ^ n)) :=
    hu.mono_set houter
  have hu2n :
      IntegrableOn (fun z => u z ^ 2)
        (centeredAxisCube x (R / (2 : ℝ) ^ n)) :=
    hu2.mono_set houter
  have hratio :
      (R / (2 : ℝ) ^ n) /
          (R / (2 : ℝ) ^ (n + 1)) = 2 := by
    rw [pow_succ]
    field_simp [hR.ne']
  have hstep :=
    abs_centeredCubeAverage_sub_centeredCubeAverage_le
      (u := u) (x := x) (y := x) hrn1 hrn hsub hun hu2n
  rw [hratio] at hstep
  have hosc := hcamp x hx n
  have hsqrt : 0 ≤ Real.sqrt ((2 : ℝ) ^ d) :=
    Real.sqrt_nonneg _
  have hdist :
      dist (dyadicCenteredCubeMeanSeq u R x n)
          (dyadicCenteredCubeMeanSeq u R x (n + 1)) =
        |centeredCubeAverage u x (R / (2 : ℝ) ^ (n + 1)) -
          centeredCubeAverage u x (R / (2 : ℝ) ^ n)| := by
    simp only [dyadicCenteredCubeMeanSeq, Real.dist_eq, abs_sub_comm]
  rw [hdist]
  calc
    |centeredCubeAverage u x (R / (2 : ℝ) ^ (n + 1)) -
        centeredCubeAverage u x (R / (2 : ℝ) ^ n)| ≤
        Real.sqrt ((2 : ℝ) ^ d) *
          centeredCubeL2Oscillation u x
            (R / (2 : ℝ) ^ n) := hstep
    _ ≤ Real.sqrt ((2 : ℝ) ^ d) *
          (K * (R / (2 : ℝ) ^ n) ^ α) :=
      mul_le_mul_of_nonneg_left hosc hsqrt
    _ = (Real.sqrt ((2 : ℝ) ^ d) * (K * R ^ α)) *
        ((2 : ℝ) ^ (-α)) ^ n := by
      rw [dyadicRadius_rpow hR.le α n]
      ring

/-- Dyadic centered-cube averages form a Cauchy sequence under positive
oscillation-decay exponent. -/
theorem cauchySeq_dyadicCenteredCubeMeanSeq
    {x : Vec d} (hα : 0 < α) (hR : 0 < R)
    (hu : IntegrableOn u (centeredAxisCube x R))
    (hu2 : IntegrableOn (fun z => u z ^ 2) (centeredAxisCube x R))
    (hcamp : DyadicCenteredCubeCampanatoBoundOn u S R α K)
    (hx : x ∈ S) :
    CauchySeq (dyadicCenteredCubeMeanSeq u R x) :=
  cauchySeq_of_le_geometric ((2 : ℝ) ^ (-α))
    (Real.sqrt ((2 : ℝ) ^ d) * (K * R ^ α))
    (Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num) (by linarith))
    (dist_dyadicCenteredCubeMeanSeq_succ_le
      hR hu hu2 hcamp hx)

/-- The selected representative is the limit of the dyadic average
sequence. -/
theorem tendsto_dyadicCenteredCubeMeanSeq
    {x : Vec d} (hα : 0 < α) (hR : 0 < R)
    (hu : IntegrableOn u (centeredAxisCube x R))
    (hu2 : IntegrableOn (fun z => u z ^ 2) (centeredAxisCube x R))
    (hcamp : DyadicCenteredCubeCampanatoBoundOn u S R α K)
    (hx : x ∈ S) :
    Tendsto (dyadicCenteredCubeMeanSeq u R x) atTop
      (𝓝 (dyadicCenteredCubeRepresentative u R x)) :=
  (cauchySeq_dyadicCenteredCubeMeanSeq
    hα hR hu hu2 hcamp hx).tendsto_limUnder

/-- The exact geometric tail estimate for the dyadic centered-cube
representative. -/
theorem abs_dyadicCenteredCubeRepresentative_sub_meanSeq_le
    {x : Vec d} (hα : 0 < α) (hR : 0 < R)
    (hu : IntegrableOn u (centeredAxisCube x R))
    (hu2 : IntegrableOn (fun z => u z ^ 2) (centeredAxisCube x R))
    (hcamp : DyadicCenteredCubeCampanatoBoundOn u S R α K)
    (hx : x ∈ S) (n : ℕ) :
    |dyadicCenteredCubeRepresentative u R x -
        dyadicCenteredCubeMeanSeq u R x n| ≤
      dyadicCampanatoTailConst d α * K *
        (R / (2 : ℝ) ^ n) ^ α := by
  have hq : (2 : ℝ) ^ (-α) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num) (by linarith)
  have hne : 1 - (2 : ℝ) ^ (-α) ≠ 0 := by
    linarith
  have hbase :=
    dist_le_of_le_geometric_of_tendsto
      ((2 : ℝ) ^ (-α))
      (Real.sqrt ((2 : ℝ) ^ d) * (K * R ^ α))
      hq
      (dist_dyadicCenteredCubeMeanSeq_succ_le
        hR hu hu2 hcamp hx)
      (tendsto_dyadicCenteredCubeMeanSeq
        hα hR hu hu2 hcamp hx)
      n
  rw [Real.dist_eq, abs_sub_comm] at hbase
  refine hbase.trans_eq ?_
  rw [dyadicRadius_rpow hR.le α n,
    dyadicCampanatoTailConst]
  field_simp

theorem dyadicCampanatoTailConst_nonneg
    (d : ℕ) {α : ℝ} (hα : 0 < α) :
    0 ≤ dyadicCampanatoTailConst d α := by
  have hq : (2 : ℝ) ^ (-α) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num) (by linarith)
  exact div_nonneg (Real.sqrt_nonneg _) (by linarith)

theorem dyadicCampanatoHolderConst_nonneg
    (d : ℕ) {α : ℝ} (hα : 0 < α) :
    0 ≤ dyadicCampanatoHolderConst d α := by
  unfold dyadicCampanatoHolderConst
  exact mul_nonneg
    (add_nonneg
      (mul_nonneg (by norm_num)
        (dyadicCampanatoTailConst_nonneg d hα))
      (mul_nonneg
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (Real.rpow_nonneg (by norm_num) α)))
    (Real.rpow_nonneg (by norm_num) α)

private theorem centeredAxisCube_subset_two_mul_of_norm_sub_le
    {x y : Vec d} {r : ℝ} (hr : 0 < r)
    (hxy : ‖x - y‖ ≤ r) :
    centeredAxisCube y r ⊆ centeredAxisCube x (2 * r) := by
  rw [centeredAxisCube_eq_metric_ball y hr,
    centeredAxisCube_eq_metric_ball x (by linarith)]
  apply Metric.ball_subset_ball'
  rw [dist_eq_norm, norm_sub_rev]
  linarith

/-- Two averages on nearby equal-sized cubes can be compared through the
centered cube with twice the half-side. The factor is the sum of two exact
square roots of volume ratios. -/
theorem abs_centeredCubeAverage_sub_centeredCubeAverage_nearby_le
    {u : Vec d → ℝ} {x y : Vec d} {r : ℝ}
    (hr : 0 < r) (hxy : ‖x - y‖ ≤ r)
    (hu : IntegrableOn u (centeredAxisCube x (2 * r)))
    (hu2 : IntegrableOn (fun z => u z ^ 2)
      (centeredAxisCube x (2 * r))) :
    |centeredCubeAverage u x r -
        centeredCubeAverage u y r| ≤
      2 * Real.sqrt ((2 : ℝ) ^ d) *
        centeredCubeL2Oscillation u x (2 * r) := by
  have hx :=
    abs_centeredCubeAverage_sub_centeredCubeAverage_le
      (u := u) hr (by linarith)
      (centeredAxisCube_mono x (by linarith)) hu hu2
  have hy :=
    abs_centeredCubeAverage_sub_centeredCubeAverage_le
      (u := u) hr (by linarith)
      (centeredAxisCube_subset_two_mul_of_norm_sub_le
        hr hxy)
      hu hu2
  have hratio : (2 * r) / r = (2 : ℝ) := by
    field_simp
  rw [hratio] at hx hy
  calc
    |centeredCubeAverage u x r -
        centeredCubeAverage u y r| ≤
        |centeredCubeAverage u x r -
          centeredCubeAverage u x (2 * r)| +
        |centeredCubeAverage u y r -
          centeredCubeAverage u x (2 * r)| := by
      exact
        (abs_sub_le
          (centeredCubeAverage u x r)
          (centeredCubeAverage u x (2 * r))
          (centeredCubeAverage u y r)).trans_eq
            (by
              rw [abs_sub_comm
                (centeredCubeAverage u x (2 * r))])
    _ ≤ 2 * Real.sqrt ((2 : ℝ) ^ d) *
        centeredCubeL2Oscillation u x (2 * r) := by
      nlinarith [hx, hy]

private theorem exists_dyadicRadius_between
    {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (hρR : ρ ≤ R / 2) :
    ∃ n : ℕ,
      ρ ≤ R / (2 : ℝ) ^ (n + 1) ∧
        R / (2 : ℝ) ^ (n + 1) < 2 * ρ := by
  classical
  have hex : ∃ n : ℕ, R / (2 : ℝ) ^ n < ρ := by
    obtain ⟨n, hn⟩ :=
      exists_pow_lt_of_lt_one
        (div_pos hρ hR)
        (by norm_num : ((1 : ℝ) / 2) < 1)
    refine ⟨n, ?_⟩
    have hrw :
        R / (2 : ℝ) ^ n =
          R * ((1 : ℝ) / 2) ^ n := by
      rw [div_pow, one_pow]
      field_simp
    rw [hrw]
    calc
      R * ((1 : ℝ) / 2) ^ n <
          R * (ρ / R) :=
        mul_lt_mul_of_pos_left hn hR
      _ = ρ := by
        field_simp
  have hfind : 2 ≤ Nat.find hex := by
    refine (Nat.le_find_iff hex 2).2 fun m hm => ?_
    interval_cases m
    · simp only [pow_zero, div_one, not_lt]
      linarith
    · simp only [pow_one, not_lt]
      linarith
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Nat.find hex = n + 2 :=
    ⟨Nat.find hex - 2, by omega⟩
  refine ⟨n, ?_, ?_⟩
  · have hminimal :=
      Nat.find_min hex (m := n + 1) (by omega)
    exact not_lt.mp hminimal
  · have hspec :
        R / (2 : ℝ) ^ (Nat.find hex) < ρ :=
      Nat.find_spec hex
    rw [hn] at hspec
    have hpow :
        (2 : ℝ) ^ (n + 2) =
          2 ^ (n + 1) * 2 := by
      ring
    rw [hpow] at hspec
    have hrw :
        R / (2 : ℝ) ^ (n + 1) =
          2 * (R / ((2 : ℝ) ^ (n + 1) * 2)) := by
      field_simp
    rw [hrw]
    linarith

/-- A dyadic centered-cube Campanato bound gives a quantitative Hölder
estimate for the selected representative at pairs whose supremum-norm
distance is at most `R / 2`.

The constant retains the exact factor
`(1 - 2 ^ (-α))⁻¹`; thus its order `α⁻¹` as `α ↓ 0` is visible. -/
theorem DyadicCenteredCubeCampanatoBoundOn.abs_representative_sub_le
    (hcamp : DyadicCenteredCubeCampanatoBoundOn u S R α K)
    (hα : 0 < α) (hR : 0 < R) (hK : 0 ≤ K)
    (hu : ∀ z ∈ S,
      IntegrableOn u (centeredAxisCube z R))
    (hu2 : ∀ z ∈ S,
      IntegrableOn (fun w => u w ^ 2)
        (centeredAxisCube z R))
    {x y : Vec d} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : ‖x - y‖ ≤ R / 2) :
    |dyadicCenteredCubeRepresentative u R x -
        dyadicCenteredCubeRepresentative u R y| ≤
      (dyadicCampanatoHolderConst d α * K) *
        ‖x - y‖ ^ α := by
  by_cases hxyEq : x = y
  · subst y
    simp only [sub_self, abs_zero, norm_zero]
    exact mul_nonneg
      (mul_nonneg
        (dyadicCampanatoHolderConst_nonneg d hα) hK)
      (Real.rpow_nonneg (by norm_num) α)
  have hρ : 0 < ‖x - y‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hxyEq)
  obtain ⟨n, hlow, hhigh⟩ :=
    exists_dyadicRadius_between hR hρ hxy
  let r := R / (2 : ℝ) ^ (n + 1)
  have hr : 0 < r := by
    exact dyadicRadius_pos hR (n + 1)
  have henc :
      2 * r = R / (2 : ℝ) ^ n := by
    dsimp only [r]
    rw [pow_succ]
    field_simp
  have hscale :
      R / (2 : ℝ) ^ n ≤ R := by
    simpa using
      dyadicRadius_antitone hR (Nat.zero_le n)
  have houter :
      centeredAxisCube x (R / (2 : ℝ) ^ n) ⊆
        centeredAxisCube x R :=
    centeredAxisCube_mono x hscale
  have hux :
      IntegrableOn u (centeredAxisCube x (2 * r)) := by
    rw [henc]
    exact (hu x hx).mono_set houter
  have hu2x :
      IntegrableOn (fun w => u w ^ 2)
        (centeredAxisCube x (2 * r)) := by
    rw [henc]
    exact (hu2 x hx).mono_set houter
  have hosc :
      centeredCubeL2Oscillation u x (2 * r) ≤
        K * (R / (2 : ℝ) ^ n) ^ α := by
    rw [henc]
    exact hcamp x hx n
  have htailx :=
    abs_dyadicCenteredCubeRepresentative_sub_meanSeq_le
      hα hR (hu x hx) (hu2 x hx) hcamp hx (n + 1)
  have htaily :=
    abs_dyadicCenteredCubeRepresentative_sub_meanSeq_le
      hα hR (hu y hy) (hu2 y hy) hcamp hy (n + 1)
  have hnear :=
    abs_centeredCubeAverage_sub_centeredCubeAverage_nearby_le
      hr hlow hux hu2x
  have hnear' :
      |centeredCubeAverage u x r -
          centeredCubeAverage u y r| ≤
        2 * Real.sqrt ((2 : ℝ) ^ d) *
          (K * (R / (2 : ℝ) ^ n) ^ α) :=
    hnear.trans
      (mul_le_mul_of_nonneg_left hosc
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
  have htriangle :
      |dyadicCenteredCubeRepresentative u R x -
          dyadicCenteredCubeRepresentative u R y| ≤
        |dyadicCenteredCubeRepresentative u R x -
          dyadicCenteredCubeMeanSeq u R x (n + 1)| +
        |centeredCubeAverage u x r -
          centeredCubeAverage u y r| +
        |dyadicCenteredCubeRepresentative u R y -
          dyadicCenteredCubeMeanSeq u R y (n + 1)| := by
    change
      |dyadicCenteredCubeRepresentative u R x -
          dyadicCenteredCubeRepresentative u R y| ≤
        |dyadicCenteredCubeRepresentative u R x -
          centeredCubeAverage u x r| +
        |centeredCubeAverage u x r -
          centeredCubeAverage u y r| +
        |dyadicCenteredCubeRepresentative u R y -
          centeredCubeAverage u y r|
    calc
      |dyadicCenteredCubeRepresentative u R x -
          dyadicCenteredCubeRepresentative u R y| ≤
          |dyadicCenteredCubeRepresentative u R x -
            centeredCubeAverage u x r| +
          |centeredCubeAverage u x r -
            dyadicCenteredCubeRepresentative u R y| :=
        abs_sub_le _ _ _
      _ ≤
          |dyadicCenteredCubeRepresentative u R x -
            centeredCubeAverage u x r| +
          (|centeredCubeAverage u x r -
            centeredCubeAverage u y r| +
          |centeredCubeAverage u y r -
            dyadicCenteredCubeRepresentative u R y|) := by
        gcongr
        exact abs_sub_le _ _ _
      _ =
          |dyadicCenteredCubeRepresentative u R x -
            centeredCubeAverage u x r| +
          |centeredCubeAverage u x r -
            centeredCubeAverage u y r| +
          |dyadicCenteredCubeRepresentative u R y -
            centeredCubeAverage u y r| := by
        rw [abs_sub_comm
          (centeredCubeAverage u y r)]
        ring
  have hpow :
      (R / (2 : ℝ) ^ n) ^ α =
        (2 : ℝ) ^ α * r ^ α := by
    rw [← henc, Real.mul_rpow (by norm_num) hr.le]
  rw [hpow] at hnear'
  have hcollect :
      |dyadicCenteredCubeRepresentative u R x -
          dyadicCenteredCubeRepresentative u R y| ≤
        (2 * dyadicCampanatoTailConst d α +
          2 * Real.sqrt ((2 : ℝ) ^ d) *
            (2 : ℝ) ^ α) * K * r ^ α := by
    nlinarith [htailx, hnear', htaily]
  have hmono :
      r ^ α ≤ (2 : ℝ) ^ α * ‖x - y‖ ^ α := by
    have hbase :
        r ^ α ≤ (2 * ‖x - y‖) ^ α :=
      Real.rpow_le_rpow hr.le (le_of_lt hhigh) hα.le
    rwa [Real.mul_rpow (by norm_num) (norm_nonneg _)] at hbase
  have hcoeff :
      0 ≤ 2 * dyadicCampanatoTailConst d α +
        2 * Real.sqrt ((2 : ℝ) ^ d) *
          (2 : ℝ) ^ α := by
    exact add_nonneg
      (mul_nonneg (by norm_num)
        (dyadicCampanatoTailConst_nonneg d hα))
      (mul_nonneg
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (Real.rpow_nonneg (by norm_num) α))
  calc
    |dyadicCenteredCubeRepresentative u R x -
        dyadicCenteredCubeRepresentative u R y| ≤
        (2 * dyadicCampanatoTailConst d α +
          2 * Real.sqrt ((2 : ℝ) ^ d) *
            (2 : ℝ) ^ α) * K * r ^ α :=
      hcollect
    _ ≤
        (2 * dyadicCampanatoTailConst d α +
          2 * Real.sqrt ((2 : ℝ) ^ d) *
            (2 : ℝ) ^ α) * K *
          ((2 : ℝ) ^ α * ‖x - y‖ ^ α) :=
      mul_le_mul_of_nonneg_left hmono
        (mul_nonneg hcoeff hK)
    _ = (dyadicCampanatoHolderConst d α * K) *
        ‖x - y‖ ^ α := by
      rw [dyadicCampanatoHolderConst]
      ring

/-- If every pair of centers is within the admissible initial scale, the
dyadic Campanato estimate gives a supremum-norm Hölder-seminorm bound. -/
theorem DyadicCenteredCubeCampanatoBoundOn.supHolderSeminormLE
    (hcamp : DyadicCenteredCubeCampanatoBoundOn u S R α K)
    (hα : 0 < α) (hR : 0 < R) (hK : 0 ≤ K)
    (hu : ∀ z ∈ S,
      IntegrableOn u (centeredAxisCube z R))
    (hu2 : ∀ z ∈ S,
      IntegrableOn (fun w => u w ^ 2)
        (centeredAxisCube z R))
    (hdiam : ∀ x ∈ S, ∀ y ∈ S,
      ‖x - y‖ ≤ R / 2) :
    SupHolderSeminormLE S
      (dyadicCenteredCubeRepresentative u R) α
      (dyadicCampanatoHolderConst d α * K) := by
  intro x hx y hy
  exact hcamp.abs_representative_sub_le
    hα hR hK hu hu2 hx hy (hdiam x hx y hy)

/-- The same Campanato estimate gives the Euclidean-distance Hölder bound
with the identical exponent and constant. -/
theorem DyadicCenteredCubeCampanatoBoundOn.euclideanHolderSeminormLE
    (hcamp : DyadicCenteredCubeCampanatoBoundOn u S R α K)
    (hα : 0 < α) (hR : 0 < R) (hK : 0 ≤ K)
    (hu : ∀ z ∈ S,
      IntegrableOn u (centeredAxisCube z R))
    (hu2 : ∀ z ∈ S,
      IntegrableOn (fun w => u w ^ 2)
        (centeredAxisCube z R))
    (hdiam : ∀ x ∈ S, ∀ y ∈ S,
      ‖x - y‖ ≤ R / 2) :
    EuclideanHolderSeminormLE S
      (dyadicCenteredCubeRepresentative u R) α
      (dyadicCampanatoHolderConst d α * K) :=
  supHolderSeminormLE_to_euclidean
    (hcamp.supHolderSeminormLE
      hα hR hK hu hu2 hdiam)
    hα.le
    (mul_nonneg
      (dyadicCampanatoHolderConst_nonneg d hα) hK)

private theorem centeredCubeAverage_eq_closedBall_setAverage
    (u : Vec d → ℝ) (x : Vec d) {r : ℝ} (hr : 0 ≤ r) :
    centeredCubeAverage u x r =
      ⨍ y in Metric.closedBall x r, u y ∂volume := by
  calc
    centeredCubeAverage u x r =
        ⨍ y in centeredAxisCube x r, u y ∂volume := by
      rw [centeredCubeAverage, setAverage_eq]
      rfl
    _ = ⨍ y in closedCenteredAxisCube x r, u y ∂volume :=
      setAverage_congr
        (centeredAxisCube_ae_eq_closedCenteredAxisCube x r)
    _ = ⨍ y in Metric.closedBall x r, u y ∂volume := by
      rw [closedCenteredAxisCube_eq_metric_closedBall x hr]

private theorem tendsto_dyadicRadius {R : ℝ} (hR : 0 < R) :
    Tendsto (fun n : ℕ => R / (2 : ℝ) ^ n)
      atTop (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    _ ?_ ?_
  · exact tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt
        (by norm_num : (1 : ℝ) < 2))
  · exact Filter.Eventually.of_forall fun n =>
      dyadicRadius_pos hR n

/-- Centered-cube averages at positive dyadic radii converge almost
everywhere to every locally integrable function. -/
theorem ae_tendsto_dyadicCenteredCubeAverage
    {u : Vec d → ℝ} (hu : LocallyIntegrable u volume)
    {R : ℝ} (hR : 0 < R) :
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      Tendsto (dyadicCenteredCubeMeanSeq u R x)
        atTop (𝓝 (u x)) := by
  filter_upwards [
      IsUnifLocDoublingMeasure.ae_tendsto_average
        volume hu 1] with x hx
  have hball :=
    hx (fun _ : ℕ => x)
      (fun n => R / (2 : ℝ) ^ n)
      (tendsto_dyadicRadius hR)
      (Filter.Eventually.of_forall fun n => by
        rw [one_mul]
        exact Metric.mem_closedBall_self (by positivity))
  refine hball.congr fun n => ?_
  exact
    (centeredCubeAverage_eq_closedBall_setAverage
      u x (div_nonneg hR.le (by positivity))).symm

/-- The dyadic centered-cube representative agrees almost everywhere with
the original locally integrable function. -/
theorem dyadicCenteredCubeRepresentative_ae_eq
    {u : Vec d → ℝ} (hu : LocallyIntegrable u volume)
    {R : ℝ} (hR : 0 < R) :
    dyadicCenteredCubeRepresentative u R =ᵐ[volume] u := by
  filter_upwards [
      ae_tendsto_dyadicCenteredCubeAverage hu hR] with x hx
  exact hx.limUnder_eq

/-- A locally integrable function is integrable on every positive-radius
centered axis cube. This is the reusable local-integrability bridge for
regularity arguments based on cube averages. -/
theorem locallyIntegrable_integrableOn_centeredAxisCube
    {f : Vec d → ℝ} (hf : LocallyIntegrable f volume)
    (x : Vec d) {R : ℝ} (hR : 0 < R) :
    IntegrableOn f (centeredAxisCube x R) := by
  rw [centeredAxisCube_eq_metric_ball x hR]
  exact
    (hf.integrableOn_isCompact
      (isCompact_closedBall x R)).mono_set
        Metric.ball_subset_closedBall

/-- The Campanato estimate, local integrability, and dyadic differentiation
package the selected precise representative as an a.e.-equal Euclidean
Hölder representative. -/
theorem
    DyadicCenteredCubeCampanatoBoundOn.hasEuclideanHolderRepresentativeOn
    (hcamp : DyadicCenteredCubeCampanatoBoundOn u S R α K)
    (hα : 0 < α) (hR : 0 < R) (hK : 0 ≤ K)
    (hu : LocallyIntegrable u volume)
    (hu2 : LocallyIntegrable (fun z => u z ^ 2) volume)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S,
      ‖x - y‖ ≤ R / 2) :
    HasEuclideanHolderRepresentativeOn S u α
      (dyadicCampanatoHolderConst d α * K) := by
  refine ⟨dyadicCenteredCubeRepresentative u R, ?_, ?_⟩
  · exact
      (dyadicCenteredCubeRepresentative_ae_eq hu hR).filter_mono
        (ae_mono Measure.restrict_le_self)
  · exact hcamp.euclideanHolderSeminormLE
      hα hR hK
      (fun x _ =>
        locallyIntegrable_integrableOn_centeredAxisCube hu x hR)
      (fun x _ =>
        locallyIntegrable_integrableOn_centeredAxisCube hu2 x hR)
      hdiam

end

end PDE
