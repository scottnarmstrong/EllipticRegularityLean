module

public import PDEFoundation.Sobolev.Trace.Model.TracePointwise
public import PDEFoundation.Sobolev.Trace.Model.TraceLp

/-!
# Measurability facts for the trace estimates

Continuity of the Euclidean length on `Vec n`, measurability of `tanGrad`, `tanGradNorm` and of the
parametrised integral `vertInt v x' r`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ}

theorem traceM_continuous_vecEuclideanNorm : Continuous (fun x : Vec n => vecEuclideanNorm x) := by
  have : (fun x : Vec n => vecEuclideanNorm x) = fun x => Real.sqrt (∑ i, x i ^ 2) := by
    funext x
    rw [vecEuclideanNorm, vecNormSq_eq_sum_sq]
  rw [this]
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2)

theorem measurable_vecEuclideanNorm : Measurable (fun x : Vec n => vecEuclideanNorm x) :=
  traceM_continuous_vecEuclideanNorm.measurable

theorem measurable_tanGrad (v : Vec n × ℝ → ℝ) : Measurable (tanGrad v) :=
  measurable_pi_iff.2 fun i => measurable_fderiv_apply_const ℝ v ((basisVec i : Vec n), (0 : ℝ))

theorem measurable_tanGradNorm (v : Vec n × ℝ → ℝ) : Measurable (tanGradNorm v) :=
  measurable_vecEuclideanNorm.comp (measurable_tanGrad v)

theorem measurable_vertInt (v : Vec n × ℝ → ℝ) :
    Measurable (fun q : Vec n × ℝ => vertInt v q.1 q.2) := by
  set F : (Vec n × ℝ) × ℝ → ℝ≥0∞ :=
    Set.indicator {q : (Vec n × ℝ) × ℝ | 0 < q.2 ∧ q.2 ≤ q.1.2}
      (fun q => ENNReal.ofReal |normDeriv v (q.1.1, q.2)|) with hF
  have hFm : Measurable F := by
    refine Measurable.indicator ?_ ?_
    · exact ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
        ((measurable_normDeriv v).comp (measurable_fst.comp measurable_fst |>.prodMk measurable_snd)))
    · exact (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (measurable_snd.comp measurable_fst))
  have := hFm.lintegral_prod_right' (ν := (volume : Measure ℝ))
  convert this using 2 with q
  rw [vertInt, ← lintegral_indicator measurableSet_Ioc]
  refine lintegral_congr (fun t => ?_)
  simp only [hF, Set.indicator, mem_Ioc, Set.mem_ofPred_eq]

end PDE.TraceLane
