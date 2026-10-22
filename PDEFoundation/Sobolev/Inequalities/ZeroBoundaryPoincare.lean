module

public import PDEFoundation.Geometry.AxisBox
public import PDEFoundation.Measure.LpPower
public import PDEFoundation.Sobolev.H1.ZeroBoundary
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Quantitative zero-boundary Poincaré on axis boxes

This module derives a zero-boundary `L²` Poincaré inequality from the
actual smooth compactly supported approximants carried by `H10Function`.
The intended public constants depend explicitly on the chosen coordinate side
length; no domain-dependent existential constant is introduced.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

noncomputable section

/-- Integration by parts for the square of a smooth compactly supported
function against a centered coordinate. -/
private theorem integral_sq_eq_neg_two_integral_mul_centered_coord_fderiv
    {d : ℕ} {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_supp : HasCompactSupport f) (i : Fin d) (m : ℝ) :
    (∫ x, f x ^ 2 ∂volume) =
      -2 * ∫ x, (fderiv ℝ f x) (basisVec i) * (x i - m) * f x ∂volume := by
  let g : Vec d → ℝ := fun x => x i - m
  let F : Vec d → ℝ := fun x => f x * f x
  let v : Vec d := basisVec i
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  have hfdiff : Differentiable ℝ f := hf1.differentiable (by simp)
  have hF1 : ContDiff ℝ 1 F := hf1.mul hf1
  have hFdiff : Differentiable ℝ F := hF1.differentiable (by simp)
  have hgdiff : Differentiable ℝ g := by
    dsimp [g]
    fun_prop
  have hFcont : Continuous F := hFdiff.continuous
  have hgcont : Continuous g := hgdiff.continuous
  have hFsupp : HasCompactSupport F := by
    dsimp [F]
    exact hf_supp.mul_left
  have hFderivCont : Continuous (fun x => (fderiv ℝ F x) v) := by
    exact (hF1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hFderivSupp : HasCompactSupport (fun x => (fderiv ℝ F x) v) := by
    exact hFsupp.fderiv_apply ℝ v
  have h1 : Integrable (fun x => (fderiv ℝ F x) v * g x) volume :=
    (hFderivCont.mul hgcont).integrable_of_hasCompactSupport
      hFderivSupp.mul_right
  have h2 : Integrable (fun x => F x * (fderiv ℝ g x) v) volume := by
    have hFint : Integrable F volume := hFcont.integrable_of_hasCompactSupport hFsupp
    have hderiv : ∀ x, (fderiv ℝ g x) v = 1 := by
      intro x
      let P : Vec d →L[ℝ] ℝ :=
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i
      have hbase : HasFDerivAt (fun y : Vec d => y i) P x := by
        simpa only [P] using! P.hasFDerivAt
      have hsub := hbase.sub (hasFDerivAt_const (x := x) (c := m))
      have hsub' :
          fderiv ℝ (fun y : Vec d => y i - m) x = P - 0 :=
        hsub.fderiv
      dsimp [g, v]
      rw [hsub', sub_apply,
        zero_apply]
      simp [P, basisVec]
    simpa only [hderiv, mul_one] using hFint
  have h3 : Integrable (fun x => F x * g x) volume :=
    (hFcont.mul hgcont).integrable_of_hasCompactSupport hFsupp.mul_right
  have hparts := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := F) (g := g) (v := v) h1 h2 h3
    (fun x _ => hFdiff x) (fun x _ => hgdiff x)
  have hFderiv : ∀ x,
      (fderiv ℝ F x) v = 2 * (fderiv ℝ f x) v * f x := by
    intro x
    dsimp [F]
    change (fderiv ℝ (f * f) x) v = _
    rw [fderiv_mul (hfdiff x) (hfdiff x)]
    dsimp [v]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hderiv : ∀ x, (fderiv ℝ g x) v = 1 := by
    intro x
    let P : Vec d →L[ℝ] ℝ :=
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i
    have hbase : HasFDerivAt (fun y : Vec d => y i) P x := by
      simpa only [P] using! P.hasFDerivAt
    have hsub := hbase.sub (hasFDerivAt_const (x := x) (c := m))
    have hsub' :
        fderiv ℝ (fun y : Vec d => y i - m) x = P - 0 :=
      hsub.fderiv
    dsimp [g, v]
    rw [hsub', sub_apply,
      zero_apply]
    simp [P, basisVec]
  rw [show (fun x => F x * (fderiv ℝ g x) v) = fun x => f x ^ 2 by
      funext x
      rw [hderiv]
      dsimp [F]
      ring] at hparts
  rw [show (fun x => (fderiv ℝ F x) v * g x) =
      fun x => 2 * (fderiv ℝ f x) (basisVec i) * (x i - m) * f x by
      funext x
      rw [hFderiv]
      dsimp [g, v]
      ring] at hparts
  rw [hparts]
  calc
    -∫ x, 2 * (fderiv ℝ f x) (basisVec i) * (x i - m) * f x ∂volume =
        -∫ x, 2 * ((fderiv ℝ f x) (basisVec i) * (x i - m) * f x) ∂volume := by
      congr 2
      funext x
      ring
    _ = -2 * ∫ x, (fderiv ℝ f x) (basisVec i) * (x i - m) * f x ∂volume := by
      rw [integral_const_mul]
      ring

private theorem support_fderiv_apply_basisVec_subset_of_tsupport_subset
    {d : ℕ} {U : Set (Vec d)} {f : Vec d → ℝ} (i : Fin d)
    (hsub : tsupport f ⊆ U) :
    Function.support (fun x => (fderiv ℝ f x) (basisVec i)) ⊆ U := by
  intro x hx
  apply hsub
  apply support_fderiv_subset ℝ
  change fderiv ℝ f x ≠ 0
  intro hzero
  apply hx
  simp [hzero]

private theorem setIntegral_sq_eq_neg_two_setIntegral_mul_centered_coord_fderiv
    {d : ℕ} {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf_supp : HasCompactSupport f)
    (hf_sub : tsupport f ⊆ U) (i : Fin d) (m : ℝ) :
    (∫ x in U, f x ^ 2 ∂volume) =
      -2 * ∫ x in U, (fderiv ℝ f x) (basisVec i) * (x i - m) * f x ∂volume := by
  have hzero_f : ∀ x, x ∉ U → f x ^ 2 = 0 := by
    intro x hxU
    have hx : x ∉ tsupport f := fun hxt => hxU (hf_sub hxt)
    simp [image_eq_zero_of_notMem_tsupport hx]
  have hzero_term : ∀ x, x ∉ U →
      (fderiv ℝ f x) (basisVec i) * (x i - m) * f x = 0 := by
    intro x hxU
    have hx : x ∉ Function.support
        (fun x => (fderiv ℝ f x) (basisVec i)) :=
      fun hxs => hxU
        (support_fderiv_apply_basisVec_subset_of_tsupport_subset i hf_sub hxs)
    have hderiv : (fderiv ℝ f x) (basisVec i) = 0 := by
      simpa [Function.notMem_support] using hx
    simp [hderiv]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero_f,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero_term,
    integral_sq_eq_neg_two_integral_mul_centered_coord_fderiv
      hf hf_supp i m]

/-- Smooth compactly supported functions supported in an axis box satisfy the
coordinatewise zero-boundary Poincaré estimate.  The displayed constant is
the exact squared side length in the selected coordinate. -/
theorem setIntegral_sq_le_side_sq_setIntegral_sq_fderiv_coord_of_tsupport_subset_axisBox
    {d : ℕ} {a b : Vec d} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf_supp : HasCompactSupport f)
    (hf_sub : tsupport f ⊆ axisBox a b) (hab : ∀ j, a j < b j) (i : Fin d) :
    (∫ x in axisBox a b, f x ^ 2 ∂volume) ≤
      (b i - a i) ^ 2 *
        ∫ x in axisBox a b, ((fderiv ℝ f x) (basisVec i)) ^ 2 ∂volume := by
  let U : Set (Vec d) := axisBox a b
  let m : ℝ := (a i + b i) / 2
  let L : ℝ := b i - a i
  let df : Vec d → ℝ := fun x => (fderiv ℝ f x) (basisVec i)
  have hside : 0 ≤ L := (sub_nonneg.mpr (hab i).le)
  have hcoord : ∀ x ∈ U, |x i - m| ≤ L / 2 := by
    intro x hx
    have hxi := hx i (Set.mem_univ i)
    dsimp [U, axisBox, m, L] at hxi ⊢
    rcases hxi with ⟨hleft, hright⟩
    rw [abs_le]
    constructor <;> linarith
  have hfsqCont : Continuous (fun x => f x ^ 2) :=
    hf.continuous.pow 2
  have hfsqSupp : HasCompactSupport (fun x => f x ^ 2) := by
    simpa only [pow_two] using! hf_supp.mul_left
  have hfsq : IntegrableOn (fun x => f x ^ 2) U volume :=
    (hfsqCont.integrable_of_hasCompactSupport hfsqSupp).restrict
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  have hdfCont : Continuous df := by
    exact (hf1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdfSupp : HasCompactSupport df := hf_supp.fderiv_apply ℝ _
  have hdfSq : IntegrableOn (fun x => df x ^ 2) U volume :=
    ((hdfCont.pow 2).integrable_of_hasCompactSupport
      (by simpa only [pow_two] using hdfSupp.mul_left)).restrict
  have hterm : IntegrableOn (fun x => df x * (x i - m) * f x) U volume := by
    have hcont : Continuous (fun x => df x * (x i - m) * f x) :=
      (hdfCont.mul ((by fun_prop : Continuous fun x : Vec d => x i - m))).mul
        hf.continuous
    have hsupp : HasCompactSupport (fun x => df x * (x i - m) * f x) :=
      hdfSupp.mul_right.mul_right
    exact (hcont.integrable_of_hasCompactSupport hsupp).restrict
  have hdfRight : IntegrableOn
      (fun x => ((1 / 2 : ℝ) * L ^ 2) * df x ^ 2) U volume :=
    hdfSq.const_mul _
  have hright : IntegrableOn
      (fun x => (1 / 2 : ℝ) * f x ^ 2 +
        (1 / 2 : ℝ) * L ^ 2 * df x ^ 2) U volume :=
    (hfsq.const_mul _).add (by simpa only [mul_assoc] using! hdfRight)
  have hpoint : ∀ x ∈ U,
      -2 * (df x * (x i - m) * f x) ≤
        (1 / 2 : ℝ) * f x ^ 2 +
          (1 / 2 : ℝ) * L ^ 2 * df x ^ 2 := by
    intro x hx
    have hq : (x i - m) ^ 2 ≤ (L / 2) ^ 2 := by
      rw [sq_le_sq]
      rw [abs_of_nonneg (div_nonneg hside (by norm_num))]
      exact hcoord x hx
    have hyoung : -2 * (df x * (x i - m) * f x) ≤
        (1 / 2 : ℝ) * f x ^ 2 +
          2 * (x i - m) ^ 2 * df x ^ 2 := by
      nlinarith [sq_nonneg (f x + 2 * (x i - m) * df x)]
    have hdfNonneg : 0 ≤ df x ^ 2 := sq_nonneg _
    have htermBound :
        2 * (x i - m) ^ 2 * df x ^ 2 ≤
          (1 / 2 : ℝ) * L ^ 2 * df x ^ 2 := by
      calc
        2 * (x i - m) ^ 2 * df x ^ 2 ≤
            2 * (L / 2) ^ 2 * df x ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hq (by norm_num)) hdfNonneg
        _ = (1 / 2 : ℝ) * L ^ 2 * df x ^ 2 := by ring
    calc
      -2 * (df x * (x i - m) * f x) ≤
          (1 / 2 : ℝ) * f x ^ 2 +
            2 * (x i - m) ^ 2 * df x ^ 2 := hyoung
      _ ≤ (1 / 2 : ℝ) * f x ^ 2 +
            (1 / 2 : ℝ) * L ^ 2 * df x ^ 2 := by
        linarith [htermBound]
  have hmain :
      ∫ x in U, -2 * (df x * (x i - m) * f x) ∂volume ≤
        ∫ x in U, (1 / 2 : ℝ) * f x ^ 2 +
          (1 / 2 : ℝ) * L ^ 2 * df x ^ 2 ∂volume :=
    setIntegral_mono_on (hterm.const_mul _) hright
      (isOpen_axisBox a b).measurableSet hpoint
  have hidentity :
      (∫ x in U, f x ^ 2 ∂volume) =
        -2 * ∫ x in U, df x * (x i - m) * f x ∂volume := by
    simpa only [U, df] using
      setIntegral_sq_eq_neg_two_setIntegral_mul_centered_coord_fderiv
        hf hf_supp hf_sub i m
  have hlinear :
      (∫ x in U, f x ^ 2 ∂volume) ≤
        (1 / 2 : ℝ) * (∫ x in U, f x ^ 2 ∂volume) +
          (1 / 2 : ℝ) * L ^ 2 * ∫ x in U, df x ^ 2 ∂volume := by
    calc
      (∫ x in U, f x ^ 2 ∂volume) =
          -2 * ∫ x in U, df x * (x i - m) * f x ∂volume := hidentity
      _ =
          ∫ x in U, -2 * (df x * (x i - m) * f x) ∂volume := by
        rw [integral_const_mul]
      _ ≤ ∫ x in U, (1 / 2 : ℝ) * f x ^ 2 +
          (1 / 2 : ℝ) * L ^ 2 * df x ^ 2 ∂volume := hmain
      _ = (1 / 2 : ℝ) * (∫ x in U, f x ^ 2 ∂volume) +
          (1 / 2 : ℝ) * L ^ 2 * ∫ x in U, df x ^ 2 ∂volume := by
        have hleft :
            (∫ x in U, (1 / 2 : ℝ) * f x ^ 2 ∂volume) =
              (1 / 2 : ℝ) * ∫ x in U, f x ^ 2 ∂volume := by
          rw [integral_const_mul]
        have hright :
            (∫ x in U, (1 / 2 : ℝ) * L ^ 2 * df x ^ 2 ∂volume) =
              (1 / 2 : ℝ) * L ^ 2 * ∫ x in U, df x ^ 2 ∂volume := by
          calc
            (∫ x in U, (1 / 2 : ℝ) * L ^ 2 * df x ^ 2 ∂volume) =
                ∫ x in U, ((1 / 2 : ℝ) * L ^ 2) * df x ^ 2 ∂volume := by
              rfl
            _ = (1 / 2 : ℝ) * L ^ 2 * ∫ x in U, df x ^ 2 ∂volume := by
              rw [integral_const_mul]
        rw [integral_add (hfsq.const_mul _) hdfRight, hleft, hright]
  have hfinal :
      (∫ x in U, f x ^ 2 ∂volume) ≤
        L ^ 2 * ∫ x in U, df x ^ 2 ∂volume := by
    linarith
  simpa only [U, L, df] using hfinal

private theorem tendsto_toReal_eLpNorm_two_of_tendsto_eLpNorm_sub
    {d : ℕ} {U : Set (Vec d)} {F : ℕ → Vec d → ℝ} {f : Vec d → ℝ}
    (hF : ∀ n, MemL2On U (F n)) (hf : MemL2On U f)
    (h : Tendsto
      (fun n => eLpNorm (fun x => F n x - f x) (2 : ℝ≥0∞) (volumeOn U))
      atTop (𝓝 0)) :
    Tendsto (fun n => (eLpNorm (F n) (2 : ℝ≥0∞) (volumeOn U)).toReal)
      atTop (𝓝 (eLpNorm f (2 : ℝ≥0∞) (volumeOn U)).toReal) := by
  have hLp : Tendsto (fun n => (hF n).toScalarLp) atTop (𝓝 hf.toScalarLp) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F hF f hf).mpr h
  have hnorm := hLp.norm
  have hterms :
      (fun n => ‖(hF n).toScalarLp‖) =
        fun n => (eLpNorm (F n) (2 : ℝ≥0∞) (volumeOn U)).toReal := by
    funext n
    exact Lp.norm_toLp (F n) (hF n)
  have hlimit :
      ‖hf.toScalarLp‖ = (eLpNorm f (2 : ℝ≥0∞) (volumeOn U)).toReal :=
    Lp.norm_toLp f hf
  rw [hterms, hlimit] at hnorm
  exact hnorm

/-- A scale-sharp coordinatewise zero-boundary Poincaré estimate for the
representative-level `H¹₀` interface on a nonempty axis box.  It is obtained
by applying the smooth estimate to the bundled supported approximants and
passing to the `L²` limits of both the value and the selected gradient
coordinate. -/
theorem h10_setIntegral_sq_le_side_sq_setIntegral_sq_grad_coord_on_axisBox
    {d : ℕ} {a b : Vec d} (u : H10Function (axisBox a b))
    (hab : ∀ j, a j < b j) (i : Fin d) :
    (∫ x in axisBox a b, u x ^ 2 ∂volume) ≤
      (b i - a i) ^ 2 *
        ∫ x in axisBox a b, (u.toH1Function.grad x i) ^ 2 ∂volume := by
  let U : Set (Vec d) := axisBox a b
  let L : ℝ := b i - a i
  let Fn : ℕ → Vec d → ℝ := u.approx
  let Gn : ℕ → Vec d → ℝ :=
    fun n x => (fderiv ℝ (Fn n) x) (basisVec i)
  have hFn : ∀ n, MemL2On U (Fn n) := by
    intro n
    exact ((u.approx_smooth n).continuous.memLp_of_hasCompactSupport
      (p := (2 : ℝ≥0∞)) (μ := volume)
      (u.approx_hasCompactSupport n)).restrict U
  have hGn : ∀ n, MemL2On U (Gn n) := by
    intro n
    have hcont : Continuous (Gn n) := by
      exact ((u.approx_smooth n).continuous_fderiv (by simp)).clm_apply
        continuous_const
    have hsupp : HasCompactSupport (Gn n) :=
      (u.approx_hasCompactSupport n).fderiv_apply ℝ _
    exact (hcont.memLp_of_hasCompactSupport
      (p := (2 : ℝ≥0∞)) (μ := volume) hsupp).restrict U
  have hValueNorm := tendsto_toReal_eLpNorm_two_of_tendsto_eLpNorm_sub
    hFn u.toH1Function.memL2 (by simpa only [Fn, U] using u.tendsto_approx)
  have hGradNorm := tendsto_toReal_eLpNorm_two_of_tendsto_eLpNorm_sub
    hGn (u.toH1Function.gradMemL2 i)
      (by simpa only [Gn, Fn, U] using u.tendsto_approx_grad i)
  have hSmooth : ∀ n,
      (eLpNorm (Fn n) (2 : ℝ≥0∞) (volumeOn U)).toReal ^ 2 ≤
        L ^ 2 * (eLpNorm (Gn n) (2 : ℝ≥0∞) (volumeOn U)).toReal ^ 2 := by
    intro n
    have h :=
      setIntegral_sq_le_side_sq_setIntegral_sq_fderiv_coord_of_tsupport_subset_axisBox
        (u.approx_smooth n) (u.approx_hasCompactSupport n)
        (u.approx_support_subset n) hab i
    calc
      (eLpNorm (Fn n) (2 : ℝ≥0∞) (volumeOn U)).toReal ^ 2 =
          ∫ x in U, Fn n x ^ 2 ∂volume :=
        toReal_eLpNorm_two_sq_eq_integral_sq (hFn n)
      _ ≤ L ^ 2 * ∫ x in U, Gn n x ^ 2 ∂volume := by
        simpa only [Fn, Gn, U, L] using h
      _ = L ^ 2 *
          (eLpNorm (Gn n) (2 : ℝ≥0∞) (volumeOn U)).toReal ^ 2 := by
        rw [toReal_eLpNorm_two_sq_eq_integral_sq (hGn n)]
  have hValueSq := hValueNorm.pow 2
  have hGradSq := (hGradNorm.pow 2).const_mul (L ^ 2)
  have hlimit :
      (eLpNorm u.toH1Function.toFun (2 : ℝ≥0∞) (volumeOn U)).toReal ^ 2 ≤
        L ^ 2 *
          (eLpNorm (fun x => u.toH1Function.grad x i)
            (2 : ℝ≥0∞) (volumeOn U)).toReal ^ 2 := by
    exact le_of_tendsto_of_tendsto' hValueSq hGradSq hSmooth
  calc
    (∫ x in axisBox a b, u x ^ 2 ∂volume) =
        (eLpNorm u.toH1Function.toFun (2 : ℝ≥0∞) (volumeOn U)).toReal ^ 2 := by
      symm
      simpa only [U] using
        toReal_eLpNorm_two_sq_eq_integral_sq u.toH1Function.memL2
    _ ≤ L ^ 2 *
        (eLpNorm (fun x => u.toH1Function.grad x i)
          (2 : ℝ≥0∞) (volumeOn U)).toReal ^ 2 := hlimit
    _ = (b i - a i) ^ 2 *
        ∫ x in axisBox a b, (u.toH1Function.grad x i) ^ 2 ∂volume := by
      rw [toReal_eLpNorm_two_sq_eq_integral_sq (u.toH1Function.gradMemL2 i)]

end

end PDE
