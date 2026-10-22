module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.LionsRep.L2WeakTrace

/-! # The Riesz slice at the initial endpoint -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.LionsRep

/-- The all-time Riesz representative has the prescribed datum as its initial `L²` class. -/
theorem cauchyL2TimeSlice_initial_eq
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u) :
    cauchyL2TimeSlice hsT ha f hf u hclose hrep ⟨s, ⟨le_rfl, hsT.le⟩⟩ = hf.toLp f := by
  apply ext_inner_right ℝ
  intro q
  let ψ : Vec d → ℝ := q
  have hψ : MemLp ψ 2 (volume : Measure (Vec d)) := by
    simpa [ψ] using Lp.memLp q
  obtain ⟨v, hvcont, hpair, hinit, _hraw⟩ :=
    exists_cauchyL2TimeSlice_pairing_continuous_initial
      hsT ha f hf u hclose hrep ψ hψ
  let ts : Icc s T := ⟨s, ⟨le_rfl, hsT.le⟩⟩
  have hq := hpair ts
  have hq' : inner ℝ (cauchyL2TimeSlice hsT ha f hf u hclose hrep ts)
      (hψ.toLp ψ) = ∫ x, f x * ψ x := by
    rw [hq, hinit]
  have hint : (∫ x, f x * ψ x) = inner ℝ (hf.toLp f) (hψ.toLp ψ) := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hψ.coeFn_toLp] with x hfx hψx
    rw [hfx, hψx]
    simp only [Real.inner_apply]
  simpa [ts, ψ] using hq'.trans hint

end PDE.Parabolic.LionsRep
