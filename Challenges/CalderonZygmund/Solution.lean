module

public import EllipticRegularity.CalderonZygmund.GeneralProof

@[expose] public section

open scoped BigOperators ENNReal

namespace PDE

open MeasureTheory

/-- The Calderón–Zygmund estimate (Proposition 3.4).  For `Λ ≥ 1` there is a constant `C ≥ 1` such that for
every `p ≥ 2`, every measurable coefficient field `a` on the unit ball `B₁` with `IsEllipticMatrix 1 Λ (a x)`
for a.e. `x` and with `a x` within `1 / (C p)` of its ball average `A₀` (in Euclidean operator norm) for
a.e. `x`, every `u ∈ H¹(B₁)` solving `-div (a ∇u) = div F` with `F ∈ L^p(B₁)` lies in `W^{1,p}(B_{1/2})`, and
`‖∇u‖_{L^p(B_{1/2})} ≤ C (‖∇u‖_{L²(B₁)} + p ‖F‖_{L^p(B₁)})` (normalized `L^p` norms). -/
theorem exists_calderonZygmund
    (d : ℕ) (hd : 0 < d) (Lambda : ℝ) (hLambda : 1 ≤ Lambda) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (p : ℝ), 2 ≤ p →
      ∀ (a : CoeffField d),
      (∀ i j : Fin d,
        AEMeasurable (fun x => a x i j)
          (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
        IsEllipticMatrix 1 Lambda (a x)) →
      (let A0 : Mat d := fun i j =>
          integralAverage (euclideanBall (0 : Vec d) 1)
            (fun x => a x i j)
        ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
          IsMatrixPerturbationLE (1 / (C * p)) (a x) A0) →
      ∀ (u : H1Function (euclideanBall (0 : Vec d) 1))
        (F : Vec d → Vec d),
      (∀ i : Fin d,
        AEStronglyMeasurable (fun x => F x i)
          (volumeOn (euclideanBall (0 : Vec d) 1))) →
      ∀ (hF : MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
          (volumeOn (euclideanBall (0 : Vec d) 1))),
      IsWeakDivergenceFormSolutionOn a
          (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) F →
      MemW1p (euclideanBall (0 : Vec d) (1 / 2 : ℝ))
          (ENNReal.ofReal p) u.toFun ∧
        ∃ hgrad : MemLp (fun x => vecEuclideanNorm (u.grad x))
            (ENNReal.ofReal p)
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2 : ℝ))),
          euclideanFieldLpMeanNormOn
              (euclideanBall (0 : Vec d) (1 / 2 : ℝ))
              (ENNReal.ofReal p) u.grad
              (memLp_normalizedVolumeOn_of_memLpOn hgrad
                (volume_euclideanBall_pos (0 : Vec d) (by norm_num))) ≤
            C *
              (Real.sqrt
                  (integralAverage (euclideanBall (0 : Vec d) 1)
                    (fun x => vecNormSq (u.grad x))) +
                p * euclideanFieldLpMeanNormOn
                  (euclideanBall (0 : Vec d) 1) (ENNReal.ofReal p) F
                  (memLp_normalizedVolumeOn_of_memLpOn hF
                    (volume_euclideanBall_pos (0 : Vec d) (by norm_num)))) :=
  PDE.CZGeneralProof.result d hd Lambda hLambda

end PDE
