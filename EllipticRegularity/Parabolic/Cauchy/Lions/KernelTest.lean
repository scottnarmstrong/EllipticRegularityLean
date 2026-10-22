module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.Lions.PairingTrace
public import EllipticRegularity.Parabolic.Energy.Mollifier

/-! # Compact spatial tests from the parabolic mollifier -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.Lions

private theorem cauchyKernelGradient_hasCompactSupport {d : ℕ} {ψ : Vec d → ℝ}
    (hψc : HasCompactSupport ψ) (i : Fin d) :
    HasCompactSupport (fun y => spaceGradC1 ψ y i) := by
  apply hasCompactSupport_of_zero_off hψc.isCompact
  intro y hy
  have hD : fderiv ℝ ψ y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hy (tsupport_fderiv_subset ℝ h))
  simp [spaceGradC1, hD]

/-- The spatial mollifier centered at `x`, written as a function of the integration variable. -/
noncomputable def cauchyKernelTest {d : ℕ} (a : ℝ) (x : Vec d) : Vec d → ℝ :=
  fun y => PDE.Parabolic.Energy.kern a (x - y)

/-- The normalized radial parabolic kernel is even. -/
theorem cauchyKernel_even {d : ℕ} (a : ℝ) (y : Vec d) :
    PDE.Parabolic.Energy.kern a (-y) = PDE.Parabolic.Energy.kern a y := by
  change (a ^ d)⁻¹ * PDE.unitConvexApproxKernel (a⁻¹ • -y) =
    (a ^ d)⁻¹ * PDE.unitConvexApproxKernel (a⁻¹ • y)
  rw [smul_neg, PDE.unitConvexApproxKernel, PDE.unitContDiffBump,
    ContDiffBump.normed_neg]

/-- The centered mollifier is smooth enough for the scalar pairing trace theorem. -/
theorem cauchyKernelTest_contDiff_one {d : ℕ} (a : ℝ) (x : Vec d) :
    ContDiff ℝ 1 (cauchyKernelTest a x) := by
  exact ((PDE.Parabolic.Energy.kern_smooth a).comp
    (contDiff_const.sub contDiff_id)).of_le (by exact_mod_cast le_top)

/-- The centered mollifier has compact support. -/
theorem cauchyKernelTest_hasCompactSupport {d : ℕ} {a : ℝ} (ha : 0 < a)
    (x : Vec d) : HasCompactSupport (cauchyKernelTest a x) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x a)
  intro y hy
  by_contra hxy
  apply hy
  have hnorm : a < ‖x - y‖ := by
    have hnorm' : a < ‖y - x‖ := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hxy
    simpa [norm_sub_rev] using hnorm'
  simp only [cauchyKernelTest]
  exact PDE.Parabolic.Energy.kern_eq_zero_of_lt_norm ha hnorm

/-- The support of the centered mollifier is contained in its closed radius-`a` ball. -/
theorem cauchyKernelTest_tsupport_subset {d : ℕ} {a : ℝ} (ha : 0 < a)
    (x : Vec d) : tsupport (cauchyKernelTest a x) ⊆ Metric.closedBall x a := by
  refine closure_minimal ?_ Metric.isClosed_closedBall
  intro y hy
  by_contra hxy
  apply hy
  have hnorm : a < ‖x - y‖ := by
    have hnorm' : a < ‖y - x‖ := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hxy
    simpa [norm_sub_rev] using hnorm'
  simp only [cauchyKernelTest]
  exact PDE.Parabolic.Energy.kern_eq_zero_of_lt_norm ha hnorm

/-- The gradient of a centered kernel test is the negative derivative of the kernel in its
center variable. -/
theorem cauchyKernelTest_spaceGrad {d : ℕ} (a : ℝ) (x y : Vec d) (i : Fin d) :
    spaceGradC1 (cauchyKernelTest a x) y i =
      -fderiv ℝ (PDE.Parabolic.Energy.kern a) (x - y) (basisVec i) := by
  unfold spaceGradC1
  have hcomp :
      fderiv ℝ (fun y : Vec d => PDE.Parabolic.Energy.kern a (x - y)) y =
        (fderiv ℝ (PDE.Parabolic.Energy.kern a) (x - y)).comp
          (-(1 : Vec d →L[ℝ] Vec d)) := by
    change fderiv ℝ (PDE.Parabolic.Energy.kern a ∘ fun y : Vec d => x - y) y = _
    rw [fderiv_comp]
    · have harg : fderiv ℝ (fun y : Vec d => x - y) y =
        -(1 : Vec d →L[ℝ] Vec d) := by
        simpa using! (fderiv_const_sub (𝕜 := ℝ) (f := fun y : Vec d => y) (x := y) x)
      rw [harg]
    · exact ((PDE.Parabolic.Energy.kern_smooth a).differentiable (by simp)) (x - y)
    · fun_prop
  change (fderiv ℝ (fun z : Vec d => PDE.Parabolic.Energy.kern a (x - z)) y)
      (basisVec i) = _
  rw [hcomp]
  simp

/-- Pairing the rescaled Lions field against a centered kernel is exactly its spatial
mollification. -/
theorem cauchyValuePairing_kernelTest_eq_mollT {d : ℕ} {s T a : ℝ}
    (u : CauchyX d s T) (x : Vec d) (t : ℝ) :
    cauchyValuePairing u (cauchyKernelTest a x) t =
      PDE.Parabolic.Energy.mollT a univ (cauchyEnergyValue u) (x, t) := by
  rw [cauchyValuePairing, PDE.Parabolic.Energy.mollT_eq]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [cauchyKernelTest]
  rw [Set.indicator_of_mem (Set.mem_univ y)]
  ring

/-- The time derivative of a centered spatial pairing, expressed as a flux pairing, belongs to
time `L²`. -/
theorem cauchyKernelFluxPairing_memLp {d : ℕ} {lam Lam s T a : ℝ}
    {A : ParCoeffField d} (ha : IsParabolicCoeff lam Lam A univ (Icc s T))
    (haε : 0 < a) (u : CauchyX d s T) (x : Vec d) :
    MemLp (cauchyFluxPairing A u (cauchyKernelTest a x)) 2
      (volume.restrict (Icc s T)) := by
  exact cauchyFluxPairing_memLp ha u (cauchyKernelTest_contDiff_one a x)
    (cauchyKernelTest_hasCompactSupport haε x)

/-- Almost every time slice of each coefficient flux coordinate is globally `L²`. -/
theorem cauchyEnergyFlux_ae_sliceMemLp {d : ℕ} {lam Lam s T : ℝ}
    {A : ParCoeffField d} (ha : IsParabolicCoeff lam Lam A univ (Icc s T))
    (u : CauchyX d s T) :
    ∀ᵐ t ∂(volume.restrict (Icc s T)), ∀ i : Fin d,
      MemLp (fun y : Vec d => matVecMul (A (y, t))
        (cauchyEnergyGradient u (y, t)) i) 2 (volume : Measure (Vec d)) := by
  rw [ae_all_iff]
  intro i
  have hflux := cauchyEnergyFlux_coord_memLp ha u i
  have hslice := PDE.Parabolic.Energy.ae_slice_memLp (d := d)
    (K1 := (univ : Set (Vec d))) (J := Icc s T)
    (g := fun z => matVecMul (A z) (cauchyEnergyGradient u z) i)
    MeasurableSet.univ hflux
  filter_upwards [hslice] with t ht
  simpa using ht

/-- At almost every time, the centered flux pairing is minus the divergence of the spatially
mollified coefficient flux. This is the scalar equation used in the mollified energy estimate. -/
theorem cauchyFluxPairing_kernelTest_eq_neg_div_mollifiedFlux
    {d : ℕ} {lam Lam s T a : ℝ} {A : ParCoeffField d}
    (ha : IsParabolicCoeff lam Lam A univ (Icc s T))
    (haε : 0 < a) (u : CauchyX d s T) (x : Vec d) :
    cauchyFluxPairing A u (cauchyKernelTest a x) =ᵐ[
      volume.restrict (Icc s T)]
        fun t => -∑ i : Fin d,
          fderiv ℝ
            (PDE.wholeSpaceMollify a
              (fun y => matVecMul (A (y, t)) (cauchyEnergyGradient u (y, t)) i))
            x (basisVec i) := by
  have hslice := cauchyEnergyFlux_ae_sliceMemLp ha u
  filter_upwards [hslice] with t ht
  let F : Fin d → Vec d → ℝ := fun i y =>
    matVecMul (A (y, t)) (cauchyEnergyGradient u (y, t)) i
  have hFloc (i : Fin d) : LocallyIntegrable (F i) volume :=
    (ht i).locallyIntegrable (by norm_num)
  have hderiv (i : Fin d) :
      fderiv ℝ (PDE.wholeSpaceMollify a (F i)) x (basisVec i) =
        ∫ y, fderiv ℝ (PDE.Parabolic.Energy.kern a) (x - y) (basisVec i) * F i y :=
    PDE.Parabolic.Energy.moll_fderiv_apply haε (hFloc i) x (basisVec i)
  have hgradcont : ∀ i : Fin d,
      Continuous fun y : Vec d => spaceGradC1 (cauchyKernelTest a x) y i := by
    intro i
    change Continuous fun y : Vec d =>
      (fderiv ℝ (cauchyKernelTest a x) y) (basisVec i)
    exact ((cauchyKernelTest_contDiff_one a x).continuous_fderiv
      (by norm_num)).clm_apply continuous_const
  have hgradmem : ∀ i : Fin d,
      MemLp (fun y : Vec d => spaceGradC1 (cauchyKernelTest a x) y i) 2
        (volume : Measure (Vec d)) := by
    intro i
    exact (hgradcont i).memLp_of_hasCompactSupport
      (cauchyKernelGradient_hasCompactSupport
        (cauchyKernelTest_hasCompactSupport haε x) i)
  have hterm : ∀ i : Fin d, Integrable
      (fun y : Vec d => F i y * spaceGradC1 (cauchyKernelTest a x) y i) volume := by
    intro i
    exact (ht i).integrable_mul (hgradmem i)
  have hsum : cauchyFluxPairing A u (cauchyKernelTest a x) t =
      ∑ i : Fin d, ∫ y, F i y * spaceGradC1 (cauchyKernelTest a x) y i := by
    rw [cauchyFluxPairing]
    change (∫ y, ∑ i : Fin d, F i y * spaceGradC1 (cauchyKernelTest a x) y i) = _
    rw [integral_finsetSum _ fun i _ => hterm i]
  rw [hsum]
  simp_rw [cauchyKernelTest_spaceGrad]
  have hi (i : Fin d) :
      (∫ y, F i y * -fderiv ℝ (PDE.Parabolic.Energy.kern a) (x - y)
        (basisVec i)) = -(fderiv ℝ (PDE.wholeSpaceMollify a (F i))
          x (basisVec i)) := by
    calc
      _ = ∫ y, -(F i y * fderiv ℝ (PDE.Parabolic.Energy.kern a) (x - y)
          (basisVec i)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by ring
      _ = -(∫ y, F i y * fderiv ℝ (PDE.Parabolic.Energy.kern a) (x - y)
          (basisVec i)) := by rw [integral_neg]
      _ = -(∫ y, fderiv ℝ (PDE.Parabolic.Energy.kern a) (x - y)
          (basisVec i) * F i y) := by
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by ring
      _ = _ := by rw [hderiv i]
  simp_rw [hi]
  simp [F]

/-- The spatial mollification has a continuous time representative at every center. Its initial
value is the mollification of the datum, and its time increments are given by the mollified flux. -/
theorem exists_cauchy_mollified_time_representative
    {d : ℕ} {lam Lam s T a : ℝ} {A : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam A univ (Icc s T))
    (haε : 0 < a) (f : Vec d → ℝ) (hf : MemLp f 2 (volume : Measure (Vec d)))
    (u : CauchyX d s T)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (x : Vec d) :
    ∃ v : ℝ → ℝ, ContinuousOn v (Icc s T) ∧
      (fun t => PDE.Parabolic.Energy.mollT a univ (cauchyEnergyValue u) (x, t)) =ᵐ[
        volume.restrict (Icc s T)] v ∧
      v s = ∫ y, f y * cauchyKernelTest a x y ∧
      ∀ p ∈ Icc s T, ∀ q ∈ Icc s T,
        v q - v p = ∫ t in p..q,
          -cauchyFluxPairing A u (cauchyKernelTest a x) t := by
  obtain ⟨v, hvcont, hvae, hvis, hvinc⟩ :=
    exists_cauchy_scalar_pairing_representative hsT ha f hf u hrep
      (cauchyKernelTest a x) (cauchyKernelTest_contDiff_one a x)
      (cauchyKernelTest_hasCompactSupport haε x)
  refine ⟨v, hvcont, ?_, hvis, hvinc⟩
  filter_upwards [hvae] with t ht
  rw [cauchyValuePairing_kernelTest_eq_mollT] at ht
  exact ht

end PDE.Parabolic.Lions
