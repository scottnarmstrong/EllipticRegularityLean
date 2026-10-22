module

public import Mathlib.MeasureTheory.Function.L2Space
public import EllipticRegularity.Meyers.RHBoundaryShift
public import PDEFoundation.Sobolev.ClassicalGradient
public import PDEFoundation.Measure.AxisBoxVolume
public import PDEFoundation.PDE.WeakDivergenceForm

/-!
# The Hölder step of the boundary reverse Hölder inequality on a cube

The Hölder integral bound of Step 2 of the reverse Hölder lemma for the zero-extended data
on `P = 4Q`, and the integrability facts needed by the boundary theorem.
-/

@[expose] public section

open MeasureTheory

namespace PDE

namespace MeyersRH

variable {d : ℕ}

/-- The Hölder--Young--Jensen bound on the cube `P = 4Q`, in terms of the shift `c`. -/
theorem boundary_step (hd : 2 ≤ d) (S : ℝ) (hS : 0 ≤ S)
    (Λ : ℝ) (a : CoeffField d)
    (hA : ∀ i j : Fin d, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (f : Vec d → Vec d)
    (hf : MemLp (fun x => vecEuclideanNorm (f x)) 2 (volumeOn (euclideanBall (0 : Vec d) 1)))
    (u : H10Function (euclideanBall (0 : Vec d) 1))
    (hE : ∀ x ∈ euclideanBall (0 : Vec d) 1,
      vecEuclideanNorm (u.grad x) ≤ wField a u x ∧
      vecEuclideanNorm (matVecMul (a x) (u.grad x)) ≤ Real.sqrt Λ * wField a u x ∧
      wField a u x ≤ Real.sqrt Λ * vecEuclideanNorm (u.grad x))
    (z : Vec d) (r : ℝ) (hr : 0 < r) (c : ℝ)
    (hSP1 : MemLp (fun x => uExt u x - integralAverage (centeredAxisCube z (4 * r)) (uExt u))
      (ENNReal.ofReal (qDual d)) (volume.restrict (centeredAxisCube z (4 * r))))
    (hSP2 : lpAvg (centeredAxisCube z (4 * r)) (qDual d)
        (fun x => |uExt u x - integralAverage (centeredAxisCube z (4 * r)) (uExt u)|) ≤
      S * (2 * (4 * r)) * lpAvg (centeredAxisCube z (4 * r)) (qExp d)
        (fun x => vecEuclideanNorm (gradExt u x)))
    (hc : |integralAverage (centeredAxisCube z (4 * r)) (uExt u) - c| ≤
      (2 : ℝ) ^ (d - 1) * lpAvg (centeredAxisCube z (4 * r)) (qDual d)
        (fun x => |uExt u x - integralAverage (centeredAxisCube z (4 * r)) (uExt u)|)) :
    (∫ x in centeredAxisCube z (4 * r), |uExt u x - c| *
        (Real.sqrt Λ * wExt a u x + sExt f x)) ≤
      (volume (centeredAxisCube z (4 * r))).toReal * (1 + (2 : ℝ) ^ (d - 1)) *
        (S * (2 * (4 * r))) *
        (Real.sqrt Λ * (lpAvg (centeredAxisCube z (4 * r)) (qExp d) (wExt a u)) ^ 2 +
          lpAvg (centeredAxisCube z (4 * r)) (qExp d) (wExt a u) *
            lpAvg (centeredAxisCube z (4 * r)) (qExp d) (sExt f)) ∧
    Integrable (fun x => |uExt u x - c| * (Real.sqrt Λ * wExt a u x + sExt f x))
      (volume.restrict (centeredAxisCube z (4 * r))) := by
  have hB : MeasurableSet (euclideanBall (0 : Vec d) 1) := measurableSet_euclideanBall _ _
  set P := centeredAxisCube z (4 * r) with hP
  have hPfin : volume P ≠ ⊤ := volume_centeredAxisCube_ne_top _ _
  have hV0 : 0 < (volume P).toReal := volume_centeredAxisCube_toReal_pos z (by positivity)
  have hpp := qExp_holderConjugate hd
  have hq0 : 0 < qExp d := hpp.pos
  have hq2 : ENNReal.ofReal (qExp d) ≤ 2 := by
    have : qExp d ≤ 2 := by
      have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      unfold qExp
      rw [div_le_iff₀ (by linarith)]; linarith
    calc ENNReal.ofReal (qExp d) ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal this
      _ = 2 := by simp
  have hL0 : 0 ≤ Real.sqrt Λ := Real.sqrt_nonneg _
  have hm2 := memLp_grad_norm u
  have hmfun : (fun x => vecEuclideanNorm (gradExt u x)) =
      (euclideanBall (0 : Vec d) 1).indicator (fun x => vecEuclideanNorm (u.grad x)) :=
    funext (vecEuclideanNorm_gradExt u)
  have hmE : MemLp (fun x => vecEuclideanNorm (gradExt u x)) (ENNReal.ofReal (qExp d))
      (volume.restrict P) := by
    rw [hmfun]; exact memLp_indicator_restrict hB hPfin hq2 hm2
  have hsE : MemLp (sExt f) (ENNReal.ofReal (qExp d)) (volume.restrict P) :=
    memLp_indicator_restrict hB hPfin hq2 hf
  have hwmeas : AEStronglyMeasurable (wExt a u) (volume.restrict P) :=
    aestronglyMeasurable_indicator_restrict hB (aestronglyMeasurable_wField a hA u)
  have hwE : MemLp (wExt a u) (ENNReal.ofReal (qExp d)) (volume.restrict P) := by
    refine hmE.of_le_mul (c := Real.sqrt Λ) hwmeas (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (wExt_nonneg a u x), Real.norm_of_nonneg (vecEuclideanNorm_nonneg _),
      vecEuclideanNorm_gradExt]
    by_cases hx : x ∈ euclideanBall (0 : Vec d) 1
    · simp only [wExt, Set.indicator_of_mem hx]
      exact (hE x hx).2.2
    · simp [wExt, Set.indicator_of_notMem hx]
  refine ⟨?_, integrable_abs_sub_mul_add hpp hPfin (wExt_nonneg a u) (sExt_nonneg f) hSP1 hwE hsE⟩
  refine sp_holder_step hpp hV0 hPfin (by positivity) (by positivity) hL0
    (wExt_nonneg a u) (sExt_nonneg f) (fun x => vecEuclideanNorm_nonneg _) ?_ hSP1 hwE hsE hmE
    hSP2 hc
  intro x
  rw [vecEuclideanNorm_gradExt]
  by_cases hx : x ∈ euclideanBall (0 : Vec d) 1
  · simp only [wExt, Set.indicator_of_mem hx]
    exact (hE x hx).1
  · simp [wExt, Set.indicator_of_notMem hx]

/-- Integrability of `w²`, `|f|²` and `|f|^q` on the cube. -/
theorem boundary_integrable (hd : 2 ≤ d) (Λ : ℝ) (a : CoeffField d)
    (hA : ∀ i j : Fin d, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (f : Vec d → Vec d)
    (hf : MemLp (fun x => vecEuclideanNorm (f x)) 2 (volumeOn (euclideanBall (0 : Vec d) 1)))
    (u : H10Function (euclideanBall (0 : Vec d) 1))
    (hE : ∀ x ∈ euclideanBall (0 : Vec d) 1,
      wField a u x ≤ Real.sqrt Λ * vecEuclideanNorm (u.grad x))
    (P : Set (Vec d)) (hPfin : volume P ≠ ⊤) :
    IntegrableOn (gExt a u) P ∧ IntegrableOn (hExt f) P ∧
      IntegrableOn (fun x => sExt f x ^ (qExp d)) P := by
  have hB : MeasurableSet (euclideanBall (0 : Vec d) 1) := measurableSet_euclideanBall _ _
  have hpp := qExp_holderConjugate hd
  have hq0 : 0 < qExp d := hpp.pos
  have hm2 := memLp_grad_norm u
  have hmfun : (fun x => vecEuclideanNorm (gradExt u x)) =
      (euclideanBall (0 : Vec d) 1).indicator (fun x => vecEuclideanNorm (u.grad x)) :=
    funext (vecEuclideanNorm_gradExt u)
  have hmE2 : MemLp (fun x => vecEuclideanNorm (gradExt u x)) 2 (volume.restrict P) := by
    rw [hmfun]; exact memLp_indicator_restrict hB hPfin le_rfl hm2
  have hsE2 : MemLp (sExt f) 2 (volume.restrict P) :=
    memLp_indicator_restrict hB hPfin le_rfl hf
  have hwmeas : AEStronglyMeasurable (wExt a u) (volume.restrict P) :=
    aestronglyMeasurable_indicator_restrict hB (aestronglyMeasurable_wField a hA u)
  have hwE2 : MemLp (wExt a u) 2 (volume.restrict P) := by
    refine hmE2.of_le_mul (c := Real.sqrt Λ) hwmeas (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (wExt_nonneg a u x), Real.norm_of_nonneg (vecEuclideanNorm_nonneg _),
      vecEuclideanNorm_gradExt]
    by_cases hx : x ∈ euclideanBall (0 : Vec d) 1
    · simp only [wExt, Set.indicator_of_mem hx]
      exact hE x hx
    · simp [wExt, Set.indicator_of_notMem hx]
  have hq2 : ENNReal.ofReal (qExp d) ≤ 2 := by
    have : qExp d ≤ 2 := by
      have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      unfold qExp
      rw [div_le_iff₀ (by linarith)]; linarith
    calc ENNReal.ofReal (qExp d) ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal this
      _ = 2 := by simp
  refine ⟨?_, ?_, ?_⟩
  · have := MeasureTheory.MemLp.integrable_sq hwE2
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    exact wExt_sq a u x
  · have := MeasureTheory.MemLp.integrable_sq hsE2
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    exact sExt_sq f x
  · have hsE : MemLp (sExt f) (ENNReal.ofReal (qExp d)) (volume.restrict P) :=
      memLp_indicator_restrict hB hPfin hq2 hf
    have := hsE.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hq0).ne' ENNReal.ofReal_ne_top
    have h' : Integrable (fun x => sExt f x ^ (qExp d)) (volume.restrict P) := by
      simpa [ENNReal.toReal_ofReal hq0.le, Real.norm_of_nonneg (sExt_nonneg f _)] using this
    exact h'

end MeyersRH

end PDE
