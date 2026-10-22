module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# ACF-A: monotonicity of `r⁻⁴ J₊ J₋` from an a.e. differential inequality

If `J_± (x) = ∫₀ˣ j_±` with `j_±` locally interval integrable on `(0, R)` and
`4 J₊ J₋ ≤ r (j₊ J₋ + J₊ j₋)` for a.e. `r ∈ (0,R)`, then `r ↦ (r⁴)⁻¹ J₊(r) J₋(r)` is
monotone on `(0, R)`.  The proof uses absolute continuity and the fundamental theorem of calculus
for absolutely continuous functions.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

namespace ACFAssembly

/-- Monotonicity of `r ↦ (r⁴)⁻¹ J₊ J₋` from the a.e. inequality `4 J₊ J₋ ≤ r (j₊ J₋ + J₊ j₋)`. -/
theorem monotoneOn_inv_pow_four_mul {R : ℝ} {jp jm : ℝ → ℝ}
    (hip : ∀ t, 0 < t → t < R → IntervalIntegrable jp volume 0 t)
    (him : ∀ t, 0 < t → t < R → IntervalIntegrable jm volume 0 t)
    (hkey : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioo 0 R →
      4 * ((∫ ρ in (0 : ℝ)..r, jp ρ) * ∫ ρ in (0 : ℝ)..r, jm ρ) ≤
        r * (jp r * (∫ ρ in (0 : ℝ)..r, jm ρ) + (∫ ρ in (0 : ℝ)..r, jp ρ) * jm r)) :
    MonotoneOn (fun r : ℝ => (r ^ 4)⁻¹ *
      ((∫ ρ in (0 : ℝ)..r, jp ρ) * ∫ ρ in (0 : ℝ)..r, jm ρ)) (Ioo 0 R) := by
  intro s hs t ht hst
  rcases hst.eq_or_lt with rfl | hlt
  · exact le_rfl
  set Jp : ℝ → ℝ := fun x => ∫ ρ in (0 : ℝ)..x, jp ρ with hJp
  set Jm : ℝ → ℝ := fun x => ∫ ρ in (0 : ℝ)..x, jm ρ with hJm
  have hs0 : 0 < s := hs.1
  have ht0 : 0 < t := ht.1
  have hsub : uIcc s t ⊆ uIcc 0 t := by
    rw [uIcc_of_le hlt.le, uIcc_of_le ht0.le]
    exact Icc_subset_Icc hs0.le le_rfl
  have hACp : AbsolutelyContinuousOnInterval Jp s t :=
    ((hip t ht0 ht.2).absolutelyContinuousOnInterval_intervalIntegral
      (c := 0) (by rw [uIcc_of_le ht0.le]; exact ⟨le_rfl, ht0.le⟩)).mono hsub
  have hACm : AbsolutelyContinuousOnInterval Jm s t :=
    ((him t ht0 ht.2).absolutelyContinuousOnInterval_intervalIntegral
      (c := 0) (by rw [uIcc_of_le ht0.le]; exact ⟨le_rfl, ht0.le⟩)).mono hsub
  have hACq : AbsolutelyContinuousOnInterval (fun x : ℝ => (x ^ 4)⁻¹) s t := by
    refine ContDiffOn.absolutelyContinuousOnInterval ?_
    refine ContDiffOn.inv (𝕜 := ℝ) (contDiff_id.pow 4).contDiffOn ?_
    intro x hx
    rw [uIcc_of_le hlt.le] at hx
    exact pow_ne_zero _ (by linarith [hx.1])
  have hACF := hACq.fun_mul (hACp.fun_mul hACm)
  have hFTC := hACF.integral_deriv_eq_sub
  have hnn : 0 ≤ ∫ x in s..t, deriv (fun x : ℝ => (x ^ 4)⁻¹ * (Jp x * Jm x)) x := by
    refine intervalIntegral.integral_nonneg_of_ae_restrict hlt.le ?_
    have hDp := (hip t ht0 ht.2).ae_hasDerivAt_integral
    have hDm := (him t ht0 ht.2).ae_hasDerivAt_integral
    filter_upwards [ae_restrict_of_ae hDp, ae_restrict_of_ae hDm, ae_restrict_of_ae hkey,
      ae_restrict_mem (measurableSet_Icc (a := s) (b := t))] with x h1 h2 h3 hx
    have hxs : x ∈ uIcc 0 t := by
      rw [uIcc_of_le ht0.le]; exact ⟨by linarith [hx.1], hx.2⟩
    have hx0 : 0 < x := by linarith [hx.1]
    have hxR : x ∈ Ioo 0 R := ⟨hx0, lt_of_le_of_lt hx.2 ht.2⟩
    have hdp : HasDerivAt Jp (jp x) x := h1 hxs 0 (by rw [uIcc_of_le ht0.le]; exact ⟨le_rfl, ht0.le⟩)
    have hdm : HasDerivAt Jm (jm x) x := h2 hxs 0 (by rw [uIcc_of_le ht0.le]; exact ⟨le_rfl, ht0.le⟩)
    have hq : HasDerivAt (fun y : ℝ => (y ^ 4)⁻¹) (-(↑4 * x ^ 3) / (x ^ 4) ^ 2) x := by
      have h4 : HasDerivAt (fun y : ℝ => y ^ 4) ((4 : ℕ) * x ^ (4 - 1)) x :=
        hasDerivAt_pow 4 x
      have := h4.fun_inv (pow_ne_zero 4 hx0.ne')
      simpa only [Nat.cast_ofNat, Nat.add_one_sub_one] using this
    have hF : HasDerivAt (fun y : ℝ => (y ^ 4)⁻¹ * (Jp y * Jm y))
        (-(↑4 * x ^ 3) / (x ^ 4) ^ 2 * (Jp x * Jm x) +
          (x ^ 4)⁻¹ * (jp x * Jm x + Jp x * jm x)) x :=
      hq.mul (hdp.mul hdm)
    show 0 ≤ deriv (fun y : ℝ => (y ^ 4)⁻¹ * (Jp y * Jm y)) x
    rw [hF.deriv]
    have hk := h3 hxR
    have hx5 : 0 < x ^ 5 := by positivity
    have : -(↑4 * x ^ 3) / (x ^ 4) ^ 2 * (Jp x * Jm x) +
        (x ^ 4)⁻¹ * (jp x * Jm x + Jp x * jm x) =
        (x ^ 5)⁻¹ * (x * (jp x * Jm x + Jp x * jm x) - 4 * (Jp x * Jm x)) := by
      field_simp
      ring
    rw [this]
    exact mul_nonneg (inv_nonneg.2 hx5.le) (by linarith only [hk])
  show (s ^ 4)⁻¹ * (Jp s * Jm s) ≤ (t ^ 4)⁻¹ * (Jp t * Jm t)
  linarith only [hFTC, hnn]

end ACFAssembly

end PDE
