module

public import EllipticRegularity.Parabolic.SliceEstimate.Matrix
public import EllipticRegularity.Parabolic.SliceEstimate.Matrix
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Absolutely continuous chain rule for a quadratic form in time

For absolutely continuous `α_i(τ) = α_i(s) + ∫_s^τ D_i` and a `C¹` weight `ψ`, the function
`ψ² ∑ᵢⱼ Sᵢⱼ αᵢ αⱼ` (`S` symmetric) has increment `∫ 2ψψ' Q(α) + 2ψ² Q(α, D)`.
-/

@[expose] public section

namespace PDE.Parabolic.Slice

open MeasureTheory Set intervalIntegral PDE

theorem ac_finset_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℝ) {a b : ℝ}
    (h : ∀ i ∈ S, AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun τ => ∑ i ∈ S, f i τ) a b := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa using (contDiffOn_const (c := (0 : ℝ))).absolutelyContinuousOnInterval (a := a) (b := b)
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem qf_eq_sum {d : ℕ} (A : Mat d) (g h : Vec d) :
    qf A g h = ∑ i, ∑ j, symmPart A i j * (g i * h j) := by
  simp only [qf, vecDot, matVecMul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem chain_quad {d : ℕ} {s t : ℝ} (hst : s ≤ t) {S : Fin d → Fin d → ℝ}
    (hS : ∀ i j, S i j = S j i) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) {α D : Fin d → ℝ → ℝ}
    (hD : ∀ i, IntervalIntegrable (D i) volume s t)
    (hα : ∀ i, ∀ τ ∈ Icc s t, α i τ = α i s + ∫ σ in s..τ, D i σ) :
    ψ t ^ 2 * (∑ i, ∑ j, S i j * (α i t * α j t)) -
        ψ s ^ 2 * (∑ i, ∑ j, S i j * (α i s * α j s)) =
      ∫ τ in s..t, (2 * ψ τ * deriv ψ τ * (∑ i, ∑ j, S i j * (α i τ * α j τ)) +
        2 * ψ τ ^ 2 * (∑ i, ∑ j, S i j * (α i τ * D j τ))) := by
  set w : Fin d → ℝ → ℝ := fun i τ => α i s + ∫ σ in s..τ, D i σ with hw
  have hws : s ∈ uIcc s t := left_mem_uIcc
  have hwac : ∀ i, AbsolutelyContinuousOnInterval (w i) s t := fun i =>
    ((contDiffOn_const (c := α i s)).absolutelyContinuousOnInterval (a := s) (b := t)).add
      ((hD i).absolutelyContinuousOnInterval_intervalIntegral hws)
  have hψac : AbsolutelyContinuousOnInterval ψ s t :=
    (hψ.contDiffOn (s := uIcc s t)).absolutelyContinuousOnInterval
  have hFac : AbsolutelyContinuousOnInterval
      (fun τ => ψ τ * ψ τ * (∑ i, ∑ j, S i j * (w i τ * w j τ))) s t := by
    refine (hψac.fun_mul hψac).fun_mul ?_
    refine ac_finset_sum _ _ fun i _ => ac_finset_sum _ _ fun j _ => ?_
    exact ((hwac i).fun_mul (hwac j)).const_mul _
  have hFTC := hFac.integral_deriv_eq_sub
  have hwv : ∀ i, ∀ τ ∈ Icc s t, w i τ = α i τ := fun i τ hτ => (hα i τ hτ).symm
  have hae : ∀ᵐ τ, ∀ i, τ ∈ uIcc s t → HasDerivAt (w i) (D i τ) τ := by
    rw [ae_all_iff]
    intro i
    filter_upwards [(hD i).ae_hasDerivAt_integral] with τ hτ hτm
    exact (hτ hτm s hws).const_add (α i s)
  have hae2 : ∀ᵐ τ, τ ∈ uIoc s t →
      deriv (fun τ => ψ τ * ψ τ * (∑ i, ∑ j, S i j * (w i τ * w j τ))) τ =
        2 * ψ τ * deriv ψ τ * (∑ i, ∑ j, S i j * (w i τ * w j τ)) +
          2 * ψ τ ^ 2 * (∑ i, ∑ j, S i j * (w i τ * D j τ)) := by
    filter_upwards [hae] with τ hτ hτm
    have hd := fun i => hτ i (uIoc_subset_uIcc hτm)
    have hψd : HasDerivAt ψ (deriv ψ τ) τ :=
      ((hψ.differentiable (by norm_num)) τ).hasDerivAt
    have hQ : HasDerivAt (fun τ => ∑ i, ∑ j, S i j * (w i τ * w j τ))
        (∑ i, ∑ j, S i j * (D i τ * w j τ + w i τ * D j τ)) τ := by
      refine HasDerivAt.fun_sum fun i _ => ?_
      refine HasDerivAt.fun_sum fun j _ => ?_
      exact (((hd i).mul (hd j)).const_mul (S i j))
    have h : HasDerivAt (fun τ => ψ τ * ψ τ * (∑ i, ∑ j, S i j * (w i τ * w j τ)))
        ((deriv ψ τ * ψ τ + ψ τ * deriv ψ τ) * (∑ i, ∑ j, S i j * (w i τ * w j τ)) +
          (ψ τ * ψ τ) * (∑ i, ∑ j, S i j * (D i τ * w j τ + w i τ * D j τ))) τ :=
      (hψd.mul hψd).mul hQ
    rw [h.deriv]
    have hsym : ∑ i, ∑ j, S i j * (D i τ * w j τ + w i τ * D j τ) =
        2 * ∑ i, ∑ j, S i j * (w i τ * D j τ) := by
      have h1 : ∑ i, ∑ j, S i j * (D i τ * w j τ) = ∑ i, ∑ j, S i j * (w i τ * D j τ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hS j i]; ring
      calc ∑ i, ∑ j, S i j * (D i τ * w j τ + w i τ * D j τ)
          = ∑ i, ∑ j, S i j * (D i τ * w j τ) + ∑ i, ∑ j, S i j * (w i τ * D j τ) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
        _ = _ := by rw [h1]; ring
    rw [hsym]
    ring
  have hint : ∫ τ in s..t, deriv (fun τ => ψ τ * ψ τ * (∑ i, ∑ j, S i j * (w i τ * w j τ))) τ =
      ∫ τ in s..t, (2 * ψ τ * deriv ψ τ * (∑ i, ∑ j, S i j * (α i τ * α j τ)) +
        2 * ψ τ ^ 2 * (∑ i, ∑ j, S i j * (α i τ * D j τ))) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae2] with τ hτ hτm
    rw [hτ hτm]
    have hτI : τ ∈ Icc s t := by
      rcases uIoc_of_le hst ▸ hτm with ⟨h1, h2⟩
      exact ⟨h1.le, h2⟩
    simp only [hwv _ τ hτI]
  rw [← hint, hFTC]
  have hts : ∀ i, w i s = α i s := fun i => by simp [hw]
  have htt : ∀ i, w i t = α i t := fun i => hwv i t ⟨hst, le_rfl⟩
  simp only [hts, htt]
  ring

end PDE.Parabolic.Slice

namespace PDE.Parabolic.Slice

open MeasureTheory Set intervalIntegral

/-- Integration by parts for `α(τ) = α(p) + ∫_p^τ D` against a `C¹` function compactly supported in
`(s, t) ⊆ [p, q]`. -/
theorem ibp_ac {p q s t : ℝ} (hps : p ≤ s) (hst : s < t) (htq : t ≤ q) {α D θ : ℝ → ℝ}
    (hD : IntervalIntegrable D volume p q) (hα : ∀ τ ∈ Icc p q, α τ = α p + ∫ σ in p..τ, D σ)
    (hθ : ContDiff ℝ 1 θ) (hθs : tsupport θ ⊆ Ioo s t) :
    ∫ τ in Ioo s t, deriv θ τ * α τ = -∫ τ in Ioo s t, θ τ * D τ := by
  set w : ℝ → ℝ := fun τ => α p + ∫ σ in p..τ, D σ with hw
  have hpI : p ∈ uIcc p q := left_mem_uIcc
  have hsub : uIcc s t ⊆ uIcc p q := by
    rw [uIcc_of_le hst.le, uIcc_of_le (hps.trans (hst.le.trans htq))]
    exact Icc_subset_Icc hps htq
  have hDst : IntervalIntegrable D volume s t := hD.mono_set hsub
  have hwac : AbsolutelyContinuousOnInterval w s t :=
    ((contDiffOn_const (c := α p)).absolutelyContinuousOnInterval (a := s) (b := t)).add
      (((hD.absolutelyContinuousOnInterval_intervalIntegral hpI)).mono hsub)
  have hθac : AbsolutelyContinuousOnInterval θ s t :=
    (hθ.contDiffOn (s := uIcc s t)).absolutelyContinuousOnInterval
  have hFac : AbsolutelyContinuousOnInterval (fun τ => θ τ * w τ) s t := hθac.fun_mul hwac
  have hFTC := hFac.integral_deriv_eq_sub
  have hθ0 : ∀ τ, τ ∉ Ioo s t → θ τ = 0 := fun τ hτ =>
    image_eq_zero_of_notMem_tsupport (fun h' => hτ (hθs h'))
  have hθs0 : θ s = 0 := hθ0 s (by simp)
  have hθt0 : θ t = 0 := hθ0 t (by simp)
  have hae : ∀ᵐ τ, τ ∈ uIcc p q → HasDerivAt w (D τ) τ := by
    filter_upwards [hD.ae_hasDerivAt_integral] with τ hτ hτm
    exact (hτ hτm p hpI).const_add (α p)
  have hae2 : ∀ᵐ τ, τ ∈ uIoc s t →
      deriv (fun τ => θ τ * w τ) τ = deriv θ τ * w τ + θ τ * D τ := by
    filter_upwards [hae] with τ hτ hτm
    have hd := hτ (hsub (uIoc_subset_uIcc hτm))
    have hθd : HasDerivAt θ (deriv θ τ) τ := ((hθ.differentiable (by norm_num)) τ).hasDerivAt
    have h : HasDerivAt (fun τ => θ τ * w τ) (deriv θ τ * w τ + θ τ * D τ) τ := hθd.mul hd
    exact h.deriv
  have hαw : ∀ τ ∈ Icc s t, α τ = w τ := fun τ hτ =>
    hα τ ⟨hps.trans hτ.1, hτ.2.trans htq⟩
  have hint : ∫ τ in s..t, deriv (fun τ => θ τ * w τ) τ =
      ∫ τ in s..t, (deriv θ τ * α τ + θ τ * D τ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae2] with τ hτ hτm
    rw [hτ hτm]
    have hτI : τ ∈ Icc s t := by
      rcases uIoc_of_le hst.le ▸ hτm with ⟨h1, h2⟩
      exact ⟨h1.le, h2⟩
    rw [hαw τ hτI]
  rw [hint] at hFTC
  simp only [hθs0, hθt0, zero_mul, sub_zero] at hFTC
  have hθ'c : Continuous (deriv θ) := hθ.continuous_deriv le_rfl
  have hαc : ContinuousOn α (uIcc s t) := by
    refine hwac.continuousOn.congr ?_
    intro τ hτ
    rw [uIcc_of_le hst.le] at hτ
    exact hαw τ hτ
  have hα_int : IntervalIntegrable (fun τ => deriv θ τ * α τ) volume s t :=
    (hθ'c.continuousOn.mul hαc).intervalIntegrable
  have hθD_int : IntervalIntegrable (fun τ => θ τ * D τ) volume s t :=
    hDst.continuousOn_mul hθ.continuous.continuousOn
  have hsplit : (∫ τ in s..t, deriv θ τ * α τ) + ∫ τ in s..t, θ τ * D τ = 0 := by
    rw [← intervalIntegral.integral_add hα_int hθD_int]; exact hFTC
  have h1 : ∫ τ in Ioo s t, deriv θ τ * α τ = ∫ τ in s..t, deriv θ τ * α τ := by
    rw [intervalIntegral.integral_of_le hst.le, integral_Ioc_eq_integral_Ioo]
  have h2 : ∫ τ in Ioo s t, θ τ * D τ = ∫ τ in s..t, θ τ * D τ := by
    rw [intervalIntegral.integral_of_le hst.le, integral_Ioc_eq_integral_Ioo]
  rw [h1, h2]
  linarith

end PDE.Parabolic.Slice
