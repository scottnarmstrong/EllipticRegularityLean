module

public import PDEFoundation.Measure.DyadicSparseDomination
public import PDEFoundation.Measure.DyadicSparseGeometricBound
public import PDEFoundation.Measure.DyadicBoxEssentialInf

@[expose] public section

namespace PDE
open BoxIntegral MeasureTheory Set
open scoped _root_.ENNReal

/-- Conditional pointwise assembly of the source mean and geometric cube
excess bounds. Consumers must prove both visible analytic premises. -/
theorem ae_vecEuclideanNorm_le_of_mean_and_dyadic_excess
    {d : ℕ} (I : Box (Fin d)) (hd : 0 < d) (g : Vec d → Vec d)
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volumeOn (I : Set (Vec d))))
    (b : Vec d → ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hmean : vecEuclideanNorm (coordinateVectorAverage (I : Set (Vec d)) g) ≤ A)
    (hexcess : ∀ q, dyadicMeanOscillation I g q ≤
      A * (1 / 2 : ℝ) ^ q.length + B * dyadicBoxEssentialInfReal I b q) :
    ∀ᵐ x ∂volume.restrict (I : Set (Vec d)),
      ENNReal.ofReal (vecEuclideanNorm (g x)) ≤
        ENNReal.ofReal ((1 + 2 * (2 : ℝ) ^ (1 + (d : ℝ) / 2)) * A) +
          ENNReal.ofReal ((2 : ℝ) ^ (1 + (d : ℝ) / 2) * B) *
            dyadicSparseSum I (dyadicSparseFamily I g) (dyadicBoxEssentialInfReal I b) x := by
  let C := (2 : ℝ) ^ (1 + (d : ℝ) / 2)
  let m := coordinateVectorAverage (I : Set (Vec d)) g
  have hC : 0 ≤ C := Real.rpow_nonneg (by norm_num) _
  have hsplit (x : Vec d) := dyadicSparseSum_le_geometric_add I
    (dyadicSparseFamily I g) (dyadicMeanOscillation I g) (dyadicBoxEssentialInfReal I b)
    hA hB (fun q _ => dyadicBoxEssentialInfReal_nonneg I b q)
    (fun q _ => hexcess q) x
  filter_upwards [ae_vecEuclideanNorm_sub_coordinateVectorAverage_le_dyadicSparseSum
    I hd g hg] with x hx
  have htriangle : vecEuclideanNorm (g x) ≤ vecEuclideanNorm (g x - m) + A := by
    calc
      vecEuclideanNorm (g x) = vecEuclideanNorm ((g x - m) + m) := by
        rw [sub_add_cancel]
      _ ≤ vecEuclideanNorm (g x - m) + vecEuclideanNorm m := vecEuclideanNorm_add_le _ _
      _ ≤ vecEuclideanNorm (g x - m) + A := add_le_add le_rfl hmean
  have htri := ENNReal.ofReal_le_ofReal htriangle
  rw [ENNReal.ofReal_add (vecEuclideanNorm_nonneg _) hA] at htri
  have htotal := htri.trans (add_le_add hx le_rfl)
  have hsplitC := mul_le_mul_right (hsplit x) (ENNReal.ofReal C)
  have hbound := htotal.trans (add_le_add hsplitC le_rfl)
  have hid : ENNReal.ofReal C *
      (ENNReal.ofReal (2 * A) + ENNReal.ofReal B *
        dyadicSparseSum I (dyadicSparseFamily I g) (dyadicBoxEssentialInfReal I b) x) +
        ENNReal.ofReal A =
      ENNReal.ofReal ((1 + 2 * C) * A) + ENNReal.ofReal (C * B) *
        dyadicSparseSum I (dyadicSparseFamily I g) (dyadicBoxEssentialInfReal I b) x := by
    rw [mul_add, ← mul_assoc, ← ENNReal.ofReal_mul hC,
      ← ENNReal.ofReal_mul hC]
    have hreal : C * (2 * A) + A = (1 + 2 * C) * A := by ring
    rw [add_right_comm, ← ENNReal.ofReal_add (mul_nonneg hC (by positivity)) hA, hreal]
  exact hbound.trans_eq hid

end PDE
