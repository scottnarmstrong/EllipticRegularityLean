module

public import EllipticRegularity.Ch4.Meyers.ExamDiv
public import PDEFoundation.Analysis.LocalDivergenceIBP
public import PDEFoundation.Sobolev.WeakDivergenceRemovablePoint

/-!
# Meyers' example is a weak solution
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4Meyers

open MeasureTheory Set

variable {d : ℕ}

theorem exam_bracket_zero (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    2 * ((examα d Λ - 1) / 2) +
      (Λ - 1 + 2 * ((examα d Λ - 1) / 2) * Λ) * ((d : ℝ) - 1 + 2 * ((examα d Λ - 1) / 2)) = 0 := by
  have hΛ0 : 0 < Λ := by linarith
  have hq := examα_quadratic hd hΛ
  have h2 : Λ * (examα d Λ ^ 2 + ((d : ℝ) - 2) * examα d Λ) = (d : ℝ) - 1 := by
    rw [hq]; field_simp
  nlinarith [h2]

theorem contDiffAt_profFlux_apply {y : Vec d} (hs : 0 < axisSq (fun _ => (1 : ℝ)) y) (Λ γ : ℝ)
    (i0 i : Fin d) (n : ℕ∞) :
    ContDiffAt ℝ n (fun z => profFlux (fun _ => (1 : ℝ)) Λ γ i0 z i) y := by
  have h1 : ContDiffAt ℝ n (axisSq (fun _ => (1 : ℝ))) y :=
    (contDiff_axisSq _).contDiffAt.of_le (by exact_mod_cast le_top)
  have hc : ∀ j, ContDiffAt ℝ n (fun z : Vec d => z j) y := fun j =>
    (contDiff_apply ℝ ℝ j).contDiffAt.of_le (by exact_mod_cast le_top)
  unfold profFlux
  have hp1 : ContDiffAt ℝ n (fun z : Vec d => axisSq (fun _ => (1 : ℝ)) z ^ γ) y :=
    h1.rpow_const_of_ne (p := γ) hs.ne'
  have hp2 : ContDiffAt ℝ n (fun z : Vec d => axisSq (fun _ => (1 : ℝ)) z ^ (γ - 1)) y :=
    h1.rpow_const_of_ne (p := γ - 1) hs.ne'
  exact (hp1.mul contDiffAt_const).add
    (((contDiffAt_const.mul hp2).mul (hc i0)).mul (contDiffAt_const.mul (hc i)))

theorem memLp_exam_flux (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ) (i : Fin d) :
    MemLp (fun x => profFlux (fun _ => (1 : ℝ)) Λ ((examα d Λ - 1) / 2)
      (⟨0, by omega⟩ : Fin d) x i) 2 (volume.restrict (euclideanBall (0 : Vec d) 1)) := by
  have hα0 := examα_pos hd hΛ
  have hα1 := examα_le_one hd hΛ
  exact memLp_profFlux (fun _ => Or.inr rfl) (i0 := ⟨0, by omega⟩) (i1 := ⟨1, by omega⟩)
    (by simp [Fin.ext_iff]) rfl rfl rfl (by linarith) (by linarith) Λ i

theorem axisSq_one_pos {x : Vec d} (hx : x ≠ 0) : 0 < axisSq (fun _ => (1 : ℝ)) x := by
  rw [axisSq_one_eq]
  have := vecEuclideanNorm_pos_iff.mpr hx
  exact Real.sqrt_pos.mp this

theorem exam_flux_integral_zero (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (φ : WeakTestFunction (euclideanBall (0 : Vec d) 1)) :
    ∫ x in euclideanBall (0 : Vec d) 1,
      vecDot (profFlux (fun _ => (1 : ℝ)) Λ ((examα d Λ - 1) / 2) (⟨0, by omega⟩ : Fin d) x)
        (classicalGradient φ.toFun x) = 0 := by
  refine integral_vecDot_classicalGradient_eq_zero_of_diff_singleton_zero hd
    (isOpen_euclideanBall _ _) (memLp_exam_flux hd hΛ) ?_ φ
  intro φ'
  have hU' : IsOpen (euclideanBall (0 : Vec d) 1 \ {(0 : Vec d)}) :=
    (isOpen_euclideanBall _ _).sdiff isClosed_singleton
  have hJ : ∀ i, ContDiffOn ℝ 1 (fun x => profFlux (fun _ => (1 : ℝ)) Λ ((examα d Λ - 1) / 2)
      (⟨0, by omega⟩ : Fin d) x i) (euclideanBall (0 : Vec d) 1 \ {(0 : Vec d)}) := by
    intro i x hx
    exact (contDiffAt_profFlux_apply (axisSq_one_pos hx.2) _ _ _ _ 1).contDiffWithinAt
  have h := integral_vecDot_weakTestFunction_grad_eq_neg_integral_divergence_mul hU'
    (fun x => profFlux (fun _ => (1 : ℝ)) Λ ((examα d Λ - 1) / 2) (⟨0, by omega⟩ : Fin d) x)
    hJ φ'
  change ∫ x in euclideanBall (0 : Vec d) 1 \ {(0 : Vec d)},
    vecDot (profFlux (fun _ => (1 : ℝ)) Λ ((examα d Λ - 1) / 2) (⟨0, by omega⟩ : Fin d) x)
      (φ'.grad x) = 0
  rw [h]
  have hz : ∀ x ∈ euclideanBall (0 : Vec d) 1 \ {(0 : Vec d)},
      (∑ i : Fin d, classicalGradient (fun y => profFlux (fun _ => (1 : ℝ)) Λ
        ((examα d Λ - 1) / 2) (⟨0, by omega⟩ : Fin d) y i) x i) * φ' x = 0 := by
    intro x hx
    rw [div_profFlux (axisSq_one_pos hx.2), exam_bracket_zero hd hΛ]
    simp
  rw [setIntegral_congr_fun hU'.measurableSet hz]
  simp

end PDE.Ch4Meyers
