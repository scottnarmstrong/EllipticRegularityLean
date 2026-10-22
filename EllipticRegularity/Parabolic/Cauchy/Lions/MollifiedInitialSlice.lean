module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.Lions.MollifiedSliceIdentity
public import EllipticRegularity.Parabolic.Cauchy.Lions.PairingTrace

/-! # Initial slice of a fixed-scale mollified representative -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.Lions

/-- Identify the initial value of a fixed representative from its sectionwise almost-everywhere
relation and the scalar pairing representative. -/
theorem cauchyMollified_initialSlice_of_section
    {d : ℕ} {lam Lam s T ε : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (hε : 0 < ε) (f : Vec d → ℝ) (hf : MemLp f 2 (volume : Measure (Vec d)))
    (u : CauchyX d s T)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (w : Vec d × ℝ → ℝ) (hwcont : ∀ x, ContinuousOn (fun t => w (x, t)) (Icc s T))
    (hwsec : ∀ x, (fun t => PDE.Parabolic.Energy.mollT ε univ
      (cauchyEnergyValue u) (x, t)) =ᵐ[volume.restrict (Icc s T)]
        (fun t => w (x, t))) (x : Vec d) :
    w (x, s) = PDE.wholeSpaceMollify ε f x := by
  obtain ⟨v, hvcont, hvae, hvinit, _hvinc⟩ :=
    exists_cauchy_scalar_pairing_representative hsT ha f hf u hrep
      (cauchyKernelTest ε x) (cauchyKernelTest_contDiff_one ε x)
      (cauchyKernelTest_hasCompactSupport hε x)
  have hkernel : (fun t => PDE.Parabolic.Energy.mollT ε univ
      (cauchyEnergyValue u) (x, t)) =ᵐ[volume.restrict (Icc s T)]
        cauchyValuePairing u (cauchyKernelTest ε x) := by
    exact Filter.Eventually.of_forall fun t =>
      (cauchyValuePairing_kernelTest_eq_mollT u x t).symm
  have htrace : (fun t => w (x, t)) =ᵐ[volume.restrict (Icc s T)] v :=
    (hwsec x).symm.trans (hkernel.trans hvae)
  have hEqOn : EqOn (fun t => w (x, t)) v (Icc s T) :=
    Measure.eqOn_Icc_of_ae_eq (volume : Measure ℝ) hsT.ne htrace
      (hwcont x) hvcont
  have hs := hEqOn (show s ∈ Icc s T from ⟨le_rfl, hsT.le⟩)
  change w (x, s) = v s at hs
  rw [hs, hvinit]
  calc
    (∫ y, f y * cauchyKernelTest ε x y) =
        ∫ y, PDE.Parabolic.Energy.kern ε (x - y) * f y := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun y => by
            simp only [cauchyKernelTest]
            ring
    _ = PDE.wholeSpaceMollify ε f x := by
      symm
      exact PDE.Parabolic.Energy.moll_eq ε f x

/-- The chosen representative of the fixed spatial mollification has initial slice equal to the
same mollification of the prescribed datum, pointwise in the spatial center. -/
theorem exists_cauchy_mollified_initial_slice
    {d : ℕ} {lam Lam s T ε : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (hε : 0 < ε) (f : Vec d → ℝ) (hf : MemLp f 2 (volume : Measure (Vec d)))
    (u : CauchyX d s T) {u₀ : CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u) :
    ∃ W : ParH1Function (univ : Set (Vec d)) (Icc s T),
      ∃ w : Vec d × ℝ → ℝ, ∃ D : Vec d × ℝ → Vec d,
        Measurable w ∧
        (∀ x, ContinuousOn (fun t => w (x, t)) (Icc s T)) ∧
        (∀ t ∈ Icc s T, ∀ K : Set (Vec d), IsCompact K →
          MemLp (fun x => w (x, t)) 2 (volume.restrict K)) ∧
        (∀ x, w (x, s) = PDE.wholeSpaceMollify ε f x) ∧ W.toFun = w ∧ W.grad = D := by
  obtain ⟨W, w, D, _G, hwm, _hDm, _hGm, hwcont, hwsec, hloc, _hWmem, _hDmem,
    _hGmem, _hwae, _hDae, _hGae, _hWgrad, _hbound, hW, hD⟩ :=
      exists_cauchy_mollified_parabolicFunction hsT ha hε f hf u hclose hrep
  refine ⟨W, w, D, hwm, hwcont, hloc, ?_, hW, hD⟩
  intro x
  exact cauchyMollified_initialSlice_of_section hsT ha hε f hf u hrep
    w hwcont hwsec x

end PDE.Parabolic.Lions
