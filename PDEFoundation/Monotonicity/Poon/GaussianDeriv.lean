module

public import PDEFoundation.Monotonicity.Defs
public import PDEFoundation.Sobolev.ClassicalLaplacian
public import PDEFoundation.Geometry.EuclideanBall.Topology
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Calculus of the heat kernel

Explicit derivatives of `heatKernel d s x = (4π s)^(-d/2) exp(-|x|²/(4s))` in `s` and `x`,
the identity `∂_s Φ = ΔΦ`, and joint smoothness on `s > 0`.
-/

@[expose] public section

namespace PDE

noncomputable section

/-- The Fréchet derivative of `x ↦ |x|²`. -/
def vecNormSqFDeriv {d : ℕ} (x : Vec d) : Vec d →L[ℝ] ℝ :=
  ∑ i, (2 * x i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i

theorem vecNormSqFDeriv_basisVec {d : ℕ} (x : Vec d) (j : Fin d) :
    vecNormSqFDeriv x (basisVec j) = 2 * x j := by
  simp [vecNormSqFDeriv, basisVec_apply]

theorem hasFDerivAt_vecNormSq {d : ℕ} (x : Vec d) :
    HasFDerivAt (vecNormSq : Vec d → ℝ) (vecNormSqFDeriv x) x := by
  have e : (vecNormSq : Vec d → ℝ) = fun x => ∑ i, x i ^ 2 := funext vecNormSq_eq_sum_sq
  rw [e]
  have h : ∀ i ∈ Finset.univ, HasFDerivAt (fun y : Vec d => y i ^ 2)
      ((2 * x i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) x := by
    intro i _
    have := (hasFDerivAt_apply (𝕜 := ℝ) i x).pow 2
    simpa using this
  exact HasFDerivAt.fun_sum h

/-- The Fréchet derivative of the heat kernel in `x`. -/
theorem hasFDerivAt_heatKernel {d : ℕ} (s : ℝ) (x : Vec d) :
    HasFDerivAt (heatKernel d s)
      ((-(1 / (4 * s)) * heatKernel d s x) • vecNormSqFDeriv x) x := by
  have h1 : HasFDerivAt (fun y : Vec d => -vecNormSq y / (4 * s))
      ((-(1 / (4 * s))) • vecNormSqFDeriv x) x := by
    have e : (fun y : Vec d => -vecNormSq y / (4 * s)) =
        fun y => (-(1 / (4 * s))) * vecNormSq y := by
      funext y; ring
    rw [e]
    exact (hasFDerivAt_vecNormSq x).const_mul _
  have h2 := (h1.exp).const_mul ((4 * Real.pi * s) ^ (-(d : ℝ) / 2))
  refine h2.congr_fderiv ?_
  simp only [smul_smul]
  congr 1
  unfold heatKernel
  ring

theorem classicalGradient_heatKernel {d : ℕ} {s : ℝ} (hs : 0 < s) (x : Vec d) :
    classicalGradient (heatKernel d s) x =
      (-(1 / (2 * s)) * heatKernel d s x) • x := by
  funext i
  rw [classicalGradient_apply, (hasFDerivAt_heatKernel s x).fderiv]
  simp only [smul_apply, vecNormSqFDeriv_basisVec, smul_eq_mul,
    Pi.smul_apply]
  field_simp
  ring

theorem euclideanCoordDeriv_heatKernel {d : ℕ} {s : ℝ} (hs : 0 < s) (i : Fin d) :
    euclideanCoordDeriv i (heatKernel d s) =
      fun y => (-(1 / (2 * s)) * heatKernel d s y) * y i := by
  funext y
  have := congrFun (classicalGradient_heatKernel hs y) i
  simpa [euclideanCoordDeriv] using this

theorem euclideanCoordSecondDeriv_heatKernel_diag {d : ℕ} {s : ℝ} (hs : 0 < s) (i : Fin d)
    (x : Vec d) :
    euclideanCoordSecondDeriv i i (heatKernel d s) x =
      -(1 / (2 * s)) * heatKernel d s x + x i ^ 2 / (4 * s ^ 2) * heatKernel d s x := by
  unfold euclideanCoordSecondDeriv
  rw [euclideanCoordDeriv_heatKernel hs]
  have hΦ := hasFDerivAt_heatKernel s x
  have hc := (hΦ.const_mul (-(1 / (2 * s)))).fun_mul (hasFDerivAt_apply (𝕜 := ℝ) i x)
  rw [hc.fderiv]
  simp [vecNormSqFDeriv_basisVec]
  field_simp

/-- The `s`-derivative of the heat kernel. -/
theorem hasDerivAt_heatKernel_s {d : ℕ} {s : ℝ} (hs : 0 < s) (x : Vec d) :
    HasDerivAt (fun t => heatKernel d t x)
      ((-(d : ℝ) / (2 * s) + vecNormSq x / (4 * s ^ 2)) * heatKernel d s x) s := by
  have hs' : (4 * Real.pi * s) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => 4 * Real.pi * t) (4 * Real.pi) s := by
    simpa using (hasDerivAt_id s).const_mul (4 * Real.pi)
  have h2 := h1.rpow_const (p := -(d : ℝ) / 2) (Or.inl hs')
  have h3 : HasDerivAt (fun t : ℝ => -vecNormSq x / (4 * t))
      (vecNormSq x / (4 * s ^ 2)) s := by
    have h := (hasDerivAt_inv hs.ne').const_mul (-vecNormSq x / 4)
    refine h.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
    · field_simp
    · exact Filter.Eventually.of_forall fun t => by field_simp
  have h4 := h2.fun_mul h3.exp
  refine h4.congr_deriv ?_
  unfold heatKernel
  rw [Real.rpow_sub_one hs']
  field_simp

/-- `∂_s Φ = ΔΦ`. -/
theorem euclideanCoordLaplacian_heatKernel {d : ℕ} {s : ℝ} (hs : 0 < s) (x : Vec d) :
    euclideanCoordLaplacian (heatKernel d s) x =
      (-(d : ℝ) / (2 * s) + vecNormSq x / (4 * s ^ 2)) * heatKernel d s x := by
  unfold euclideanCoordLaplacian
  simp only [euclideanCoordSecondDeriv_heatKernel_diag hs]
  rw [Finset.sum_add_distrib]
  have e1 : ∑ i : Fin d, x i ^ 2 / (4 * s ^ 2) * heatKernel d s x =
      vecNormSq x / (4 * s ^ 2) * heatKernel d s x := by
    rw [← Finset.sum_mul, ← Finset.sum_div, ← vecNormSq_eq_sum_sq]
  rw [e1]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem hasDerivAt_heatKernel_s_eq_laplacian {d : ℕ} {s : ℝ} (hs : 0 < s) (x : Vec d) :
    HasDerivAt (fun t => heatKernel d t x) (euclideanCoordLaplacian (heatKernel d s) x) s := by
  rw [euclideanCoordLaplacian_heatKernel hs]
  exact hasDerivAt_heatKernel_s hs x

/-- Joint smoothness of `(s, x) ↦ Φ(s, x)` on `s > 0`. -/
theorem contDiffOn_heatKernel (d : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec d => heatKernel d p.1 p.2) {p | 0 < p.1} := by
  intro p hp
  have hp' : (0 : ℝ) < p.1 := hp
  refine ContDiffAt.contDiffWithinAt ?_
  unfold heatKernel
  have hq : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec d => vecNormSq q.2) :=
    contDiff_vecNormSq.comp contDiff_snd
  have hl : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec d => 4 * Real.pi * q.1) p :=
    (contDiff_const.mul contDiff_fst).contDiffAt
  refine (hl.rpow_const_of_ne (by positivity)).mul ?_
  refine ContDiffAt.exp ?_
  exact hq.neg.contDiffAt.div (contDiff_const.mul contDiff_fst).contDiffAt (by positivity)

end

end PDE
