module

public import PDEFoundation.Measure.EssInfAffineBound
public import PDEFoundation.Measure.QuadraticBallMaximalReal
public import PDEFoundation.Measure.DyadicBoxEssentialInf
public import PDEFoundation.PDE.LaplacianDyadicCubeExcess

/-! # Dyadic Laplacian excess with an essential-infimum source term -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The pointwise maximal forcing term in the dyadic cube excess estimate can
be replaced by its literal essential infimum on that cube. -/
theorem centeredVectorMeanL2_dyadicDescendant_le_essentialInf
    {d : ℕ} (I : Box (Fin d)) (L : ℝ) (hd : 0 < d)
    (hwidth : ∀ i, I.upper i - I.lower i = L)
    (u : H1Function (euclideanBall (boxCenter I)
      (2 * (Real.sqrt d * L / 2))))
    (F : Vec d → Vec d)
    (hF : MemVectorL2On (euclideanBall (boxCenter I)
      (2 * (Real.sqrt d * L / 2))) F)
    (hsol : IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat d))
      (euclideanBall (boxCenter I) (2 * (Real.sqrt d * L / 2))) u 0 F)
    {p : ℝ} (hp : 2 < p)
    (hFp : MemLp (fun x => vecEuclideanNorm (F x))
      (ENNReal.ofReal p) volume)
    (q : List (Set (Fin d))) :
    centeredVectorMeanL2 (dyadicDescendant I q : Set (Vec d)) u.grad ≤
      (Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
          (Real.sqrt d / 2) ^ d) * Real.sqrt ((2 : ℝ) ^ d) /
          (2 : ℝ) ^ q.length) *
        Real.sqrt (integralAverage
          (euclideanBall (boxCenter I) (2 * (Real.sqrt d * L / 2)))
          (fun y => vecNormSq (u.grad y))) +
      (Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
          (Real.sqrt d / 2) ^ d) *
        (((d : ℝ) + 2) / 2 * (1 + 2 / (d : ℝ)) ^ ((d : ℝ) / 2))) *
        dyadicBoxEssentialInfReal I
          (fun x => (quadraticBallMaximal F x).toReal) q := by
  let Q : Set (Vec d) := (dyadicDescendant I q : Set (Vec d))
  let e := centeredVectorMeanL2 Q u.grad
  let A := (Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
      (Real.sqrt d / 2) ^ d) * Real.sqrt ((2 : ℝ) ^ d) /
      (2 : ℝ) ^ q.length) *
    Real.sqrt (integralAverage
      (euclideanBall (boxCenter I) (2 * (Real.sqrt d * L / 2)))
      (fun y => vecNormSq (u.grad y)))
  let B := Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
      (Real.sqrt d / 2) ^ d) *
    (((d : ℝ) + 2) / 2 * (1 + 2 / (d : ℝ)) ^ ((d : ℝ) / 2))
  let b : Vec d → ℝ := fun x => (quadraticBallMaximal F x).toReal
  have hIoo : ∀ᵐ x ∂volume.restrict Q,
      x ∈ Box.Ioo (dyadicDescendant I q) := by
    apply (ae_restrict_iff' (dyadicDescendant I q).measurableSet_coe).mpr
    filter_upwards [Box.coe_ae_eq_Ioo (dyadicDescendant I q)] with x hx hxQ
    exact hx.mp hxQ
  have hfinite : ∀ᵐ x ∂volume.restrict Q,
      quadraticBallMaximal F x ≠ ∞ :=
    ae_restrict_of_ae (ae_quadraticBallMaximal_ne_top F hp hFp)
  have hb : ∀ᵐ x ∂volume.restrict Q, 0 ≤ b x :=
    ae_of_all _ fun x => ENNReal.toReal_nonneg
  have he : 0 ≤ e := by
    dsimp only [e]
    exact Real.sqrt_nonneg _
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hB : 0 < B := by
    have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
    have hunit : 0 < (volume (euclideanBall (0 : Vec d) 1)).toReal :=
      volume_euclideanBall_toReal_pos (0 : Vec d) (by norm_num)
    dsimp only [B]
    positivity
  have hpoint : ∀ᵐ x ∂volume.restrict Q,
      ENNReal.ofReal e ≤ ENNReal.ofReal A +
        ENNReal.ofReal B * ENNReal.ofReal (b x) := by
    filter_upwards [hIoo, hfinite] with x hx hxtop
    have hxbound := ofReal_centeredVectorMeanL2_dyadicDescendant_le
      I L hd hwidth u F hF hsol q hx
    dsimp only [e, A, B, b, Q]
    rwa [ENNReal.ofReal_toReal hxtop]
  have hess := ofReal_le_add_mul_essInf_of_ae
    (volume.restrict Q) b e A B hb he hA hB hpoint
  have hreembed : essInf (fun x => ENNReal.ofReal (b x))
      (volume.restrict Q) =
      ENNReal.ofReal (dyadicBoxEssentialInfReal I b q) := by
    rw [← dyadicBoxEssentialInf_eq_essInf_of_ae_nonneg I b q hb,
      ofReal_dyadicBoxEssentialInfReal]
  rw [hreembed] at hess
  have hcoef : 0 ≤ B * dyadicBoxEssentialInfReal I b q :=
    mul_nonneg hB.le (dyadicBoxEssentialInfReal_nonneg I b q)
  have hRHS : 0 ≤ A + B * dyadicBoxEssentialInfReal I b q :=
    add_nonneg hA hcoef
  rw [← ENNReal.ofReal_mul hB.le,
    ← ENNReal.ofReal_add hA hcoef,
    ENNReal.ofReal_le_ofReal_iff hRHS] at hess
  exact hess

end

end PDE
