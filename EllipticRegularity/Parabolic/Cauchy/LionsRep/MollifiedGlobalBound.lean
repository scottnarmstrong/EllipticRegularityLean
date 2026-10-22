module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.Lions.MollifiedGlobalSlice

/-! # Scale independent bounds for mollified time slices -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.LionsRep

/-- The energy bound obtained from the compact spatial cutoff identity.  Its value depends only
on the initial datum and the space-time `L²` norms of the Lions value, gradient, and flux. -/
noncomputable def cauchySliceEnergyBound {d : ℕ} {s T : ℝ}
    {a : ParCoeffField d} (f : Vec d → ℝ) (u : PDE.Parabolic.Lions.CauchyX d s T) : ℝ :=
  (eLpNorm f 2 volume).toReal ^ 2 +
    2 * ∑ i : Fin d,
      ((eLpNorm (fun z => matVecMul (a z)
          (PDE.Parabolic.Lions.cauchyEnergyGradient u z) i)
          2 (PDE.Parabolic.Lions.slabMeasure d s T)).toReal *
          (eLpNorm (fun z => PDE.Parabolic.Lions.cauchyEnergyGradient u z i)
            2 (PDE.Parabolic.Lions.slabMeasure d s T)).toReal +
        64 * (eLpNorm (fun z => matVecMul (a z)
          (PDE.Parabolic.Lions.cauchyEnergyGradient u z) i)
          2 (PDE.Parabolic.Lions.slabMeasure d s T)).toReal *
          (eLpNorm (PDE.Parabolic.Lions.cauchyEnergyValue u)
            2 (PDE.Parabolic.Lions.slabMeasure d s T)).toReal)

/-- Each spatial mollification of the Lions value has a uniform-in-scale energy bound on every
Euclidean ball at each time strictly after the initial time.  The representative is jointly
measurable and has continuous time sections; the bound is independent of the mollifier scale and
the ball radius. -/
theorem exists_cauchy_mollified_uniformBallBound
    {d : ℕ} {lam Lam s T ε : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (hε : 0 < ε) (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u) :
    ∃ w : Vec d × ℝ → ℝ, Measurable w ∧
      (∀ x, ContinuousOn (fun t => w (x, t)) (Icc s T)) ∧
      (∀ᵐ z ∂(PDE.Parabolic.Lions.slabMeasure d s T),
        w z = PDE.Parabolic.Energy.mollT ε univ
          (PDE.Parabolic.Lions.cauchyEnergyValue u) z) ∧
      ∀ t ∈ Icc s T, s < t → ∀ n : ℕ,
        (∫ x in euclideanClosedBall (0 : Vec d) ((n : ℝ) + 1), w (x, t) ^ 2) ≤
          cauchySliceEnergyBound (a := a) f u := by
  obtain ⟨w, hwm, hwcont, _hwsec, hwae⟩ :=
    PDE.Parabolic.Lions.exists_cauchy_mollified_joint_representative
      hsT ha hε f hf u hrep
  refine ⟨w, hwm, hwcont, hwae, ?_⟩
  intro t ht hst n
  exact PDE.Parabolic.Lions.cauchy_mollified_cutoff_ball_bound
    hsT ha hε f hf u hclose hrep hwcont (by
      intro x
      exact _hwsec x) hst ht.2 n

end PDE.Parabolic.LionsRep
