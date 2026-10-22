module

public import PDEFoundation.Sobolev.Cutoff.Ball
public import PDEFoundation.Sobolev.H1.CutoffEnergy
public import PDEFoundation.Sobolev.Inequalities.ZeroBoundarySobolevPower
public import PDEFoundation.Measure.LpPower

/-!
# The Sobolev step of the Moser one-step estimates

For `w ∈ H¹(U)` and concentric balls `B_r ⊂ B_s ⊆ U`, if the cutoff product `η w` has energy at
most `Θ ∫_{B_s} w²`, then `‖w‖_{L^{2*}(B_r)} ≤ C_S √Θ ‖w‖_{L²(B_s)}` (in `ℝ≥0∞`).
-/

@[expose] public section

open scoped ENNReal NNReal

namespace PDE.DGNMOneStep

open MeasureTheory PDE

variable {d : ℕ} {U : Set (Vec d)}

/-- Extended norm of a vector field magnitude in terms of its energy. -/
theorem euclideanFieldELpNormOn_two_le {g : Vec d → Vec d}
    (hg : MemLp (fun x => vecEuclideanNorm (g x)) 2 (volumeOn U)) {E : ℝ}
    (hE : ∫ x in U, vecNormSq (g x) ≤ E) :
    euclideanFieldELpNormOn U 2 g ≤ ENNReal.ofReal (Real.sqrt E) := by
  have hsq := toReal_eLpNorm_two_sq_eq_integral_sq hg
  have hint : (∫ x, vecEuclideanNorm (g x) ^ 2 ∂volumeOn U) = ∫ x in U, vecNormSq (g x) := by
    simp only [vecEuclideanNorm_sq]
  rw [hint] at hsq
  have hne : eLpNorm (fun x => vecEuclideanNorm (g x)) 2 (volumeOn U) ≠ ∞ := hg.eLpNorm_ne_top
  have hT : (eLpNorm (fun x => vecEuclideanNorm (g x)) 2 (volumeOn U)).toReal ≤ Real.sqrt E := by
    apply Real.le_sqrt_of_sq_le
    rw [hsq]; exact hE
  unfold euclideanFieldELpNormOn eLpNormOn
  rw [← ENNReal.ofReal_toReal hne]
  exact ENNReal.ofReal_le_ofReal hT

/-- The `L²` extended norm of an `L²` function on a set, via its integral. -/
theorem eLpNorm_two_eq_ofReal_sqrt {f : Vec d → ℝ} {S : Set (Vec d)}
    (hf : MemLp f 2 (volumeOn S)) :
    eLpNorm f 2 (volumeOn S) = ENNReal.ofReal (Real.sqrt (∫ x in S, f x ^ 2)) := by
  have hsq := toReal_eLpNorm_two_sq_eq_integral_sq hf
  have hne : eLpNorm f 2 (volumeOn S) ≠ ∞ := hf.eLpNorm_ne_top
  rw [← hsq, Real.sqrt_sq ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hne]

/-- Sobolev step. -/
theorem sobolev_step (hd : 3 ≤ d) (hU : IsOpenBoundedConvexDomain U) (w : H1Function U)
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hball : euclideanBall (0 : Vec d) s ⊆ U) {Θ : ℝ}
    (hΘ : 0 ≤ Θ)
    (hE : ∫ x in U, vecNormSq
        ((w.mulCutoffToH10 hU (quantitativeBallCutoff (0 : Vec d) hr hrs) hball).toH1Function.grad x) ≤
      Θ * ∫ x in euclideanBall (0 : Vec d) s, w x ^ 2) :
    eLpNorm w.toFun (ENNReal.ofReal (sobolevConjugate d 2)) (volumeOn (euclideanBall (0 : Vec d) r)) ≤
      ENNReal.ofReal ((zeroBoundarySobolevConstantTwo d : ℝ) * Real.sqrt Θ) *
        eLpNorm w.toFun 2 (volumeOn (euclideanBall (0 : Vec d) s)) := by
  set η := quantitativeBallCutoff (0 : Vec d) hr hrs with hη
  set v := w.mulCutoffToH10 hU η hball with hv
  have hSob := eLpNormOn_sobolevConjugate_two_le_euclideanFieldELpNormOn hd v
  have hvfun : v.toFun = fun x => η x * w x := by
    have := H1Function.mulCutoffToH10_toFun w hU η hball
    exact this
  have hinnerU : euclideanBall (0 : Vec d) r ⊆ U :=
    (euclideanBall_mono hr hrs.le).trans hball
  have hinner : eLpNorm w.toFun (ENNReal.ofReal (sobolevConjugate d 2))
      (volumeOn (euclideanBall (0 : Vec d) r)) ≤
      eLpNormOn U (ENNReal.ofReal (sobolevConjugate d 2)) v.toFun := by
    calc eLpNorm w.toFun (ENNReal.ofReal (sobolevConjugate d 2))
          (volumeOn (euclideanBall (0 : Vec d) r))
        = eLpNorm v.toFun (ENNReal.ofReal (sobolevConjugate d 2))
          (volumeOn (euclideanBall (0 : Vec d) r)) := by
          apply eLpNorm_congr_ae
          refine ae_restrict_of_forall_mem (isOpen_euclideanBall 0 r).measurableSet ?_
          intro x hx
          rw [hvfun]
          simp only [η.eq_one_on_inner x hx, one_mul]
      _ ≤ eLpNorm v.toFun (ENNReal.ofReal (sobolevConjugate d 2)) (volumeOn U) :=
          eLpNorm_mono_measure _ (Measure.restrict_mono hinnerU le_rfl)
  have hGradMem : MemLp (fun x => vecEuclideanNorm (v.toH1Function.grad x)) 2 (volumeOn U) :=
    v.toH1Function.gradMemL2.memLp_vecEuclideanNorm
  have hgrad := euclideanFieldELpNormOn_two_le hGradMem hE
  have hwL2 : MemLp w.toFun 2 (volumeOn (euclideanBall (0 : Vec d) s)) :=
    w.memL2.mono_measure (Measure.restrict_mono hball le_rfl)
  have hwNorm := eLpNorm_two_eq_ofReal_sqrt hwL2
  have hIw : 0 ≤ ∫ x in euclideanBall (0 : Vec d) s, w x ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  calc eLpNorm w.toFun (ENNReal.ofReal (sobolevConjugate d 2))
        (volumeOn (euclideanBall (0 : Vec d) r))
      ≤ eLpNormOn U (ENNReal.ofReal (sobolevConjugate d 2)) v.toFun := hinner
    _ ≤ (zeroBoundarySobolevConstantTwo d : ℝ≥0∞) *
        euclideanFieldELpNormOn U 2 v.toH1Function.grad := hSob
    _ ≤ (zeroBoundarySobolevConstantTwo d : ℝ≥0∞) *
        ENNReal.ofReal (Real.sqrt (Θ * ∫ x in euclideanBall (0 : Vec d) s, w x ^ 2)) :=
        by gcongr
    _ = ENNReal.ofReal ((zeroBoundarySobolevConstantTwo d : ℝ) * Real.sqrt Θ) *
        eLpNorm w.toFun 2 (volumeOn (euclideanBall (0 : Vec d) s)) := by
        rw [hwNorm, Real.sqrt_mul hΘ, ENNReal.ofReal_mul (by positivity),
          ← mul_assoc, ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp

end PDE.DGNMOneStep
