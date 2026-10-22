module

public import PDEFoundation.Ambient.Basis
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Coordinate integration by parts for smooth compactly supported functions -/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

private instance instNontrivialVecSCCI (d : ℕ) [NeZero d] : Nontrivial (Vec d) :=
  inferInstance

private instance instNoncompactSpaceVecSCCI (d : ℕ) [NeZero d] : NoncompactSpace (Vec d) :=
  inferInstance

private theorem fderiv_centeredCoord_apply_basisVec
    {d : ℕ} [NeZero d] (i : Fin d) (z x : Vec d) :
    (fderiv ℝ (fun y : Vec d => y i - z i) x) (basisVec i) = 1 := by
  let P : Vec d →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i
  have hbase : HasFDerivAt (fun y : Vec d => y i) P x := by
    simpa only [P] using! P.hasFDerivAt
  have hsub := hbase.sub (hasFDerivAt_const (x := x) (c := z i))
  have hsub' : fderiv ℝ (fun y : Vec d => y i - z i) x = P - 0 := hsub.fderiv
  rw [hsub', sub_apply, zero_apply]
  simp [P, basisVec]

private theorem integrable_fderiv_mul_centeredCoord
    {d : ℕ} [NeZero d] {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_supp : HasCompactSupport f) (i : Fin d) (z : Vec d) :
    Integrable (fun x => (fderiv ℝ f x) (basisVec i) * (x i - z i)) volume := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  have hdcont : Continuous (fun x => (fderiv ℝ f x) (basisVec i)) :=
    (hf1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdsupp : HasCompactSupport (fun x => (fderiv ℝ f x) (basisVec i)) :=
    hf_supp.fderiv_apply ℝ (basisVec i)
  exact (hdcont.mul (by fun_prop)).integrable_of_hasCompactSupport hdsupp.mul_right

private theorem integrable_mul_centeredCoord
    {d : ℕ} [NeZero d] {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_supp : HasCompactSupport f) (i : Fin d) (z : Vec d) :
    Integrable (fun x => f x * (x i - z i)) volume := by
  let P : Vec d →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i
  have hcoord : Continuous (fun x : Vec d => x i - z i) := by
    simpa only [P, ContinuousLinearMap.coe_proj] using!
      P.continuous.sub continuous_const
  have hsupp : HasCompactSupport (fun x => f x * (x i - z i)) :=
    hf_supp.mul_right
  exact (hf.continuous.mul hcoord).integrable_of_hasCompactSupport hsupp

/-- A smooth compactly supported function may be integrated by parts against a
centered coordinate function. -/
theorem integral_eq_neg_integral_fderiv_mul_centered_coord
    {d : ℕ} [NeZero d] {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_supp : HasCompactSupport f) (i : Fin d) (z : Vec d) :
    ∫ x, f x ∂volume =
      -∫ x, (fderiv ℝ f x) (basisVec i) * (x i - z i) ∂volume := by
  let coord : Vec d → ℝ := fun x => x i - z i
  let v : Vec d := basisVec i
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  have hf_diff : Differentiable ℝ f := hf1.differentiable (by simp)
  have hcoord_diff : Differentiable ℝ coord := by
    let P : Vec d →L[ℝ] ℝ :=
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i
    have hP : Differentiable ℝ (fun x : Vec d => P x) := P.differentiable
    simpa only [coord, P, ContinuousLinearMap.coe_proj] using!
      hP.sub (differentiable_const (c := z i))
  have h1 : Integrable (fun x => (fderiv ℝ f x) v * coord x) volume := by
    simpa only [coord, v] using integrable_fderiv_mul_centeredCoord hf hf_supp i z
  have hderiv : ∀ x, (fderiv ℝ coord x) v = 1 := by
    intro x
    simpa only [coord, v] using fderiv_centeredCoord_apply_basisVec i z x
  have h2 : Integrable (fun x => f x * (fderiv ℝ coord x) v) volume := by
    have hf_int : Integrable f volume :=
      hf.continuous.integrable_of_hasCompactSupport hf_supp
    simpa only [hderiv, mul_one] using hf_int
  have h3 : Integrable (fun x => f x * coord x) volume := by
    simpa only [coord] using integrable_mul_centeredCoord hf hf_supp i z
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := f) (g := coord) (v := v)
    h1 h2 h3 (fun x _ => hf_diff x) (fun x _ => hcoord_diff x)
  simpa only [hderiv, mul_one] using h

end

end PDE
