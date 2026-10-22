module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.LionsRep.RepresentativeAssembly

/-! # Slice properties of the all-time Riesz representative -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set Filter

namespace PDE.Parabolic.LionsRep

/-- Every time slice of the jointly measurable representative is globally in spatial `L²`. -/
theorem cauchyRieszSliceRepresentative_slice_memLp
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (t : Icc s T) :
    MemLp (fun x : Vec d =>
      cauchyRieszSliceRepresentative hsT ha f hf u hclose hrep (x, t))
      2 (volume : Measure (Vec d)) := by
  have hslice := cauchyRieszSliceRepresentative_ae_eq_slice
    hsT ha f hf u hclose hrep t
  exact (memLp_congr_ae hslice).mpr
    (Lp.memLp (cauchyL2TimeSlice hsT ha f hf u hclose hrep t))

private theorem cauchyRieszSliceRepresentative_integral_eq_inner
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (ψ : Vec d → ℝ) (hψ : MemLp ψ 2 (volume : Measure (Vec d))) (t : Icc s T) :
    (∫ x, cauchyRieszSliceRepresentative hsT ha f hf u hclose hrep (x, t) * ψ x) =
      inner ℝ (cauchyL2TimeSlice hsT ha f hf u hclose hrep t) (hψ.toLp ψ) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cauchyRieszSliceRepresentative_ae_eq_slice
    hsT ha f hf u hclose hrep t, hψ.coeFn_toLp] with x hx hψx
  rw [hx, hψx]
  simp only [Real.inner_apply]

/-- For every compactly supported `L²` test, the representative has a weakly continuous spatial
pairing on the closed time slab. -/
theorem cauchyRieszSliceRepresentative_pairing_continuousOn
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (ψ : Vec d → ℝ) (hψ : PDE.IsL2c (univ : Set (Vec d)) ψ) :
    ContinuousOn (fun t => ∫ x in (univ : Set (Vec d)),
      cauchyRieszSliceRepresentative hsT ha f hf u hclose hrep (x, t) * ψ x)
      (Icc s T) := by
  rcases hψ with ⟨hψL2, K, hK, hKU, hψ0⟩
  have hψLp : MemLp ψ 2 (volume : Measure (Vec d)) := by
    simpa [PDE.MemL2On, PDE.MemLpOn, PDE.volumeOn, Measure.restrict_univ] using hψL2
  obtain ⟨v, hvcont, hpair, _hinit, _hraw⟩ :=
    exists_cauchyL2TimeSlice_pairing_continuous_initial
      hsT ha f hf u hclose hrep ψ hψLp
  have hcont : Continuous (fun t : Icc s T =>
      ∫ x, cauchyRieszSliceRepresentative hsT ha f hf u hclose hrep (x, t) * ψ x) :=
    hvcont.congr fun t => by
      rw [cauchyRieszSliceRepresentative_integral_eq_inner
        hsT ha f hf u hclose hrep ψ hψLp t, hpair t]
  apply (continuousOn_iff_continuous_domRestrict).2
  convert hcont using 1
  funext t
  simp [Measure.restrict_univ]

end PDE.Parabolic.LionsRep
