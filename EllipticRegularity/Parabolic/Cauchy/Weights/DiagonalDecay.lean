module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Topology.Algebra.Module.ModuleTopology


/-!
# Scalar Nash differential inequality

This file isolates the time-variable step in the diagonal part of the
Nash--Aronson argument.  The differential inequality is the one obtained by
combining the energy identity, Nash's inequality, and the `L¹` contraction.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Weights

open Set

/-- A nonpositive derivative makes a continuous function nonincreasing on a
closed interval. -/
theorem antitoneOn_Icc_of_deriv_nonpos {T : ℝ} {E : ℝ → ℝ}
    (hET : ContinuousOn E (Icc 0 T))
    (hderiv : ∀ x ∈ Ioo 0 T, HasDerivAt E (deriv E x) x)
    (hderiv_nonpos : ∀ x ∈ Ioo 0 T, deriv E x ≤ 0) :
    AntitoneOn E (Icc 0 T) := by
  intro x hx y hy hxy
  by_cases hxy' : x = y
  · simp [hxy']
  have hlt : x < y := lt_of_le_of_ne hxy hxy'
  have hsub : Icc x y ⊆ Icc 0 T := by
    intro z hz
    exact ⟨le_trans hx.1 hz.1, le_trans hz.2 hy.2⟩
  obtain ⟨z, hz, hslope⟩ := exists_hasDerivAt_eq_slope E (deriv E) hlt
    (hET.mono hsub)
    (fun z hz => hderiv z ⟨lt_of_le_of_lt hx.1 hz.1,
      lt_of_lt_of_le hz.2 hy.2⟩)
  have hz0 := hderiv_nonpos z ⟨lt_of_le_of_lt hx.1 hz.1,
    lt_of_lt_of_le hz.2 hy.2⟩
  have hden : 0 < y - x := by linarith
  have hquot : (E y - E x) / (y - x) ≤ 0 := by
    rw [← hslope]
    exact hz0
  have hnum : E y - E x ≤ 0 := by
    simpa using (div_le_iff₀ hden).mp hquot
  linarith

/-- The right-hand side of the integrated Nash differential inequality has
the expected Gaussian scaling after raising it to the exponent `-2/d`. -/
theorem nashDiagonalBound_rpow {d : ℕ} (hd : 0 < d) {c B t : ℝ}
    (hc : 0 < c) (hB : 0 < B) (ht : 0 < t) :
    (((d : ℝ) / (2 * c * t)) ^ ((d : ℝ) / 2) * B ^ 2) ^ (-(2 : ℝ) / d) =
      (2 * c / d) * B ^ (-(4 : ℝ) / d) * t := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdR
  have hbase : 0 < (d : ℝ) / (2 * c * t) := by positivity
  have hBsq : 0 < B ^ 2 := by positivity
  have hsum : ((d : ℝ) / 2) * (-(2 : ℝ) / d) = -1 := by
    field_simp
  have hBexp : (2 : ℝ) * (-(2 : ℝ) / d) = -(4 : ℝ) / d := by ring
  rw [Real.mul_rpow (le_of_lt (Real.rpow_pos_of_pos hbase _)) (le_of_lt hBsq)]
  rw [← Real.rpow_mul hbase.le]
  have hBpow : (B ^ 2) ^ (-(2 : ℝ) / d) = B ^ (-(4 : ℝ) / d) := by
    rw [show B ^ 2 = B * B by ring, Real.mul_rpow hB.le hB.le,
      ← Real.rpow_add hB]
    congr 1
    ring
  rw [hBpow]
  rw [hsum, Real.rpow_neg_one]
  have hratio : ((d : ℝ) / (2 * c * t))⁻¹ = (2 * c / d) * t := by
    field_simp
  rw [hratio]
  ring

/-- The differential inequality
`E' ≤ -c E^(1+2/d) B^(-4/d)` gives both `L²` contraction and the
dimensionally sharp diagonal decay.  This scalar statement is formulated for
strictly positive `B`; zero initial `L¹` mass is handled separately by the
parabolic `L¹` contraction. -/
theorem nashDiagonalDecay_of_deriv {d : ℕ} (hd : 0 < d) {T c B : ℝ}
    (hT : 0 < T) (hc : 0 < c) (hB : 0 < B) (E : ℝ → ℝ)
    (hcont : ContinuousOn E (Icc 0 T))
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ E t)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (deriv E t) t)
    (hdiss : ∀ t ∈ Ioo 0 T,
      deriv E t ≤ -c * E t ^ (1 + (2 : ℝ) / d) * B ^ (-(4 : ℝ) / d)) :
    ∀ t ∈ Icc 0 T, 0 < t →
      E t ≤ E 0 ∧
        E t ≤ ((d : ℝ) / (2 * c * t)) ^ ((d : ℝ) / 2) * B ^ 2 := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hBexp : 0 < B ^ (-(4 : ℝ) / d) := Real.rpow_pos_of_pos hB _
  have hp_nonneg (t : ℝ) (ht : 0 ≤ E t) :
      0 ≤ E t ^ (1 + (2 : ℝ) / d) := Real.rpow_nonneg ht _
  have hderiv_nonpos : ∀ t ∈ Ioo 0 T, deriv E t ≤ 0 := by
    intro t ht
    have hpow := hp_nonneg t (hnonneg t ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
    have hmul := mul_nonneg hpow hBexp.le
    have hc0 : 0 ≤ c := le_of_lt hc
    nlinarith [hdiss t ht]
  have hanti := antitoneOn_Icc_of_deriv_nonpos hcont hderiv hderiv_nonpos
  intro t ht htpos
  constructor
  · exact hanti (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, le_of_lt hT⟩)
      ht (by linarith)
  · by_cases hEt0 : E t = 0
    · rw [hEt0]
      positivity
    · have hEt : 0 < E t := lt_of_le_of_ne (hnonneg t ht) (Ne.symm hEt0)
      have hEpositive : ∀ x ∈ Icc 0 t, 0 < E x := by
        intro x hx
        have hxt : x ≤ t := hx.2
        have hxT : x ∈ Icc 0 T := ⟨hx.1, le_trans hx.2 ht.2⟩
        have hEtEx : E t ≤ E x := hanti hxT ht hxt
        exact lt_of_lt_of_le hEt hEtEx
      let q : ℝ := -(2 : ℝ) / d
      let F : ℝ → ℝ := fun x => E x ^ q
      have hFcont : ContinuousOn F (Icc 0 t) := by
        change ContinuousOn (fun x => E x ^ q) (Icc 0 t)
        exact (hcont.mono (by
          intro x hx
          exact ⟨hx.1, le_trans hx.2 ht.2⟩)).rpow_const
          (fun x hx => Or.inl (ne_of_gt (hEpositive x hx)))
      have hqneg : q < 0 := by
        dsimp [q]
        exact div_neg_of_neg_of_pos (by norm_num) hdR
      have hFderiv : ∀ x ∈ Ioo 0 t, HasDerivAt F (deriv F x) x := by
        intro x hx
        have hxT : x ∈ Ioo 0 T := ⟨hx.1, lt_of_lt_of_le hx.2 ht.2⟩
        have hEx : 0 < E x := hEpositive x ⟨le_of_lt hx.1, hx.2.le⟩
        have hcomp : HasDerivAt F
            (deriv E x * q * E x ^ (q - 1)) x := by
          simpa [F] using (hderiv x hxT).rpow_const (p := q) (Or.inl hEx.ne')
        have hformula := hcomp.deriv
        rw [← hformula] at hcomp
        exact hcomp
      have hFderiv_lower : ∀ x ∈ Ioo 0 t, (2 * c / d) *
          B ^ (-(4 : ℝ) / d) ≤ deriv F x := by
        intro x hx
        have hxT : x ∈ Ioo 0 T := ⟨hx.1, lt_of_lt_of_le hx.2 ht.2⟩
        have hEx : 0 < E x := hEpositive x ⟨le_of_lt hx.1, hx.2.le⟩
        have hexp : E x ^ (1 + (2 : ℝ) / d) * E x ^ (q - 1) = 1 := by
          rw [← Real.rpow_add hEx]
          dsimp [q]
          have : (1 : ℝ) + 2 / d + (-(2 : ℝ) / d - 1) = 0 := by ring
          rw [this, Real.rpow_zero]
        have hfacpos : 0 < E x ^ (q - 1) := Real.rpow_pos_of_pos hEx _
        have hqeq : q = -(2 : ℝ) / d := rfl
        have hmul := mul_le_mul_of_nonpos_left (hdiss x hxT)
          (show q * E x ^ (q - 1) ≤ 0 by
            rw [show q = -(2 : ℝ) / d by rfl]
            exact mul_nonpos_of_nonpos_of_nonneg
              (by have : 0 < (2 : ℝ) / d := div_pos (by norm_num) hdR; linarith)
              hfacpos.le)
        have hcomp := (hderiv x hxT).rpow_const (p := q) (Or.inl hEx.ne')
        have hderivFormula : deriv F x = deriv E x * q * E x ^ (q - 1) := by
          simpa [F, q] using hcomp.deriv
        have hexp' : E x ^ (q - 1) * E x ^ (1 + (2 : ℝ) / d) = 1 := by
          rw [← Real.rpow_add hEx]
          have hqsum : q - 1 + (1 + (2 : ℝ) / d) = 0 := by
            dsimp [q]
            ring
          rw [hqsum, Real.rpow_zero]
        have hleft : q * E x ^ (q - 1) *
            (-c * E x ^ (1 + (2 : ℝ) / d) * B ^ (-(4 : ℝ) / d)) =
            (2 * c / d) * B ^ (-(4 : ℝ) / d) := by
          calc
            _ = (q * (-c)) *
                (E x ^ (q - 1) * E x ^ (1 + (2 : ℝ) / d)) *
                  B ^ (-(4 : ℝ) / d) := by ring
            _ = (2 * c / d) * B ^ (-(4 : ℝ) / d) := by
              rw [hexp']
              dsimp [q]
              ring
        have hmul' : (2 * c / d) * B ^ (-(4 : ℝ) / d) ≤
            q * E x ^ (q - 1) * deriv E x := by
          calc
            _ = q * E x ^ (q - 1) *
                (-c * E x ^ (1 + (2 : ℝ) / d) * B ^ (-(4 : ℝ) / d)) := hleft.symm
            _ ≤ q * E x ^ (q - 1) * deriv E x := by
              simpa only [mul_assoc] using hmul
        calc
          (2 * c / d) * B ^ (-(4 : ℝ) / d) ≤
              q * E x ^ (q - 1) * deriv E x := hmul'
          _ = deriv F x := by rw [hderivFormula]; ring
      obtain ⟨x, hx, hslope⟩ := exists_hasDerivAt_eq_slope F (deriv F)
        htpos hFcont
        (fun x hx => hFderiv x hx)
      have hslower : (2 * c / d) * B ^ (-(4 : ℝ) / d) ≤
          (F t - F 0) / (t - 0) := by
        rw [← hslope]
        exact hFderiv_lower x hx
      have hFt : (2 * c / d) * B ^ (-(4 : ℝ) / d) * t ≤ F t := by
        have hF0 : 0 ≤ F 0 := Real.rpow_nonneg
          (le_of_lt (hEpositive 0 ⟨le_rfl, htpos.le⟩)) _
        have hmult := (le_div_iff₀ htpos).mp (by simpa [sub_zero] using hslower)
        nlinarith
      have htargetpos : 0 < ((d : ℝ) / (2 * c * t)) ^ ((d : ℝ) / 2) * B ^ 2 := by
        positivity
      have htargetpow := nashDiagonalBound_rpow hd hc hB htpos
      have hFtarget :
          (((d : ℝ) / (2 * c * t)) ^ ((d : ℝ) / 2) * B ^ 2) ^ q ≤ F t := by
        have hKpos : 0 < (2 * c / d) * B ^ (-(4 : ℝ) / d) * t := by positivity
        have hKle : (2 * c / d) * B ^ (-(4 : ℝ) / d) * t ≤ F t := hFt
        calc
          (((d : ℝ) / (2 * c * t)) ^ ((d : ℝ) / 2) * B ^ 2) ^ q =
              (2 * c / d) * B ^ (-(4 : ℝ) / d) * t := by
                simpa [q] using htargetpow
          _ ≤ F t := hKle
      have hEbound : E t ≤
          ((d : ℝ) / (2 * c * t)) ^ ((d : ℝ) / 2) * B ^ 2 := by
        apply (Real.rpow_le_rpow_iff_of_neg htargetpos hEt hqneg).mp
        simpa [F, q] using hFtarget
      exact hEbound

end PDE.Parabolic.Cauchy.Weights
