module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.Lions.JointRepresentative
public import EllipticRegularity.Parabolic.Cauchy.Lions.KernelFluxL1

/-! # Every-time local bounds for the spatially mollified Lions representative -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.Lions

/-- Centered kernel tests belong to spatial `L²`. -/
theorem cauchyKernelTest_memLp {d : ℕ} {a : ℝ} (ha : 0 < a) (x : Vec d) :
    MemLp (cauchyKernelTest a x) 2 (volume : Measure (Vec d)) := by
  exact (cauchyKernelTest_contDiff_one a x).continuous.memLp_of_hasCompactSupport
    (cauchyKernelTest_hasCompactSupport ha x)

/-- The initial trace pairing against a centered mollifier is bounded by the two `L²` norms. -/
theorem cauchyKernelInitialPairing_abs_le {d : ℕ} {a : ℝ} {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume : Measure (Vec d))) (x : Vec d)
    (hkernel : MemLp (cauchyKernelTest a x) 2 (volume : Measure (Vec d))) :
    |∫ y, f y * cauchyKernelTest a x y| ≤
      ‖hf.toLp f‖ * ‖hkernel.toLp (cauchyKernelTest a x)‖ := by
  have hpairing :
      (∫ y, f y * cauchyKernelTest a x y) =
        inner ℝ (hf.toLp f) (hkernel.toLp (cauchyKernelTest a x)) := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hkernel.coeFn_toLp] with y hy hk
    rw [hy, hk]
    change f y * cauchyKernelTest a x y = cauchyKernelTest a x y * f y
    ring
  rw [hpairing]
  exact abs_real_inner_le_norm _ _

private theorem abs_intervalIntegral_cauchyFlux_le {s T t : ℝ}
    (ht : t ∈ Icc s T) {F : ℝ → ℝ}
    (hF : Integrable F (volume.restrict (Icc s T))) :
    |∫ r in s..t, -F r| ≤ ∫ r, |F r| ∂(volume.restrict (Icc s T)) := by
  have hFOn : IntegrableOn F (Icc s T) volume := hF
  have hsub : Ioc s t ⊆ Icc s T := by
    intro r hr
    exact ⟨le_of_lt hr.1, hr.2.trans ht.2⟩
  have hIoc : IntegrableOn F (Ioc s t) volume := hFOn.mono_set hsub
  have hIocAbs : IntegrableOn (fun r => |F r|) (Ioc s t) volume := hIoc.abs
  have hnorm : ‖∫ r in Ioc s t, -F r‖ ≤ ∫ r in Ioc s t, |F r| := by
    apply norm_integral_le_of_norm_le hIocAbs
    filter_upwards [] with r
    simp [Real.norm_eq_abs]
  have hfullAbs : IntegrableOn (fun r => |F r|) (Icc s T) volume := hFOn.abs
  have hsubset : Ioc s t ≤ᵐ[volume] Icc s T :=
    Filter.Eventually.of_forall fun r hr => hsub hr
  have hnonneg : 0 ≤ᵐ[volume.restrict (Icc s T)] fun r => |F r| :=
    Filter.Eventually.of_forall fun r => abs_nonneg _
  have hmono := setIntegral_mono_set hfullAbs hnonneg hsubset
  calc
    |∫ r in s..t, -F r| = ‖∫ r in Ioc s t, -F r‖ := by
      rw [intervalIntegral.integral_of_le ht.1, Real.norm_eq_abs]
    _ ≤ ∫ r in Ioc s t, |F r| := hnorm
    _ ≤ ∫ r, |F r| ∂(volume.restrict (Icc s T)) := by
      simpa [MeasureTheory.integral_def] using hmono

/-- For fixed mollification scale, the jointly measurable representative has a spatially uniform
pointwise bound at every time in the closed Cauchy interval. The bound uses the global Lions
space-time flux norm and the initial `L²` norm; it is independent of the center and of time. -/
theorem exists_cauchy_mollified_global_pointwise_bound
    {d : ℕ} {lam Lam s T a : ℝ} {A : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam A univ (Icc s T))
    (haε : 0 < a) (f : Vec d → ℝ) (hf : MemLp f 2 (volume : Measure (Vec d)))
    (u : CauchyX d s T)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u) :
    ∃ w : Vec d × ℝ → ℝ, Measurable w ∧
      (∀ x, ContinuousOn (fun t => w (x, t)) (Icc s T)) ∧
      (∀ x, (fun t => PDE.Parabolic.Energy.mollT a univ
        (cauchyEnergyValue u) (x, t)) =ᵐ[volume.restrict (Icc s T)]
          (fun t => w (x, t))) ∧
      (∀ᵐ z ∂(slabMeasure d s T),
        w z = PDE.Parabolic.Energy.mollT a univ (cauchyEnergyValue u) z) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Vec d, ∀ t ∈ Icc s T, |w (x, t)| ≤ B := by
  obtain ⟨w, hwm, hwcont, hwsec, hwae⟩ :=
    exists_cauchy_mollified_joint_representative hsT ha haε f hf u hrep
  let hkernel0 : MemLp (cauchyKernelTest a (0 : Vec d)) 2
      (volume : Measure (Vec d)) := cauchyKernelTest_memLp haε 0
  let Cflux : ℝ := ∑ i : Fin d,
      ‖cauchyGradientTestLp
        (cauchyKernelTest_contDiff_one a (0 : Vec d))
        (cauchyKernelTest_hasCompactSupport haε (0 : Vec d)) i‖ *
        ∫ t, Real.sqrt (∫ y, (matVecMul (A (y, t))
          (cauchyEnergyGradient u (y, t)) i) ^ 2)
          ∂(volume.restrict (Icc s T))
  let B : ℝ := ‖hf.toLp f‖ * ‖hkernel0.toLp (cauchyKernelTest a (0 : Vec d))‖ + Cflux
  have hCflux : 0 ≤ Cflux := by
    dsimp [Cflux]
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg (norm_nonneg _)
    apply integral_nonneg_of_ae
    filter_upwards [] with t
    exact Real.sqrt_nonneg _
  have hB : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hCflux
  refine ⟨w, hwm, hwcont, hwsec, hwae, B, hB, ?_⟩
  intro x t ht
  obtain ⟨v, hvcont, hvAe, hv0, hvinc⟩ :=
    exists_cauchy_mollified_time_representative hsT ha haε f hf u hrep x
  have hwv : (fun r => w (x, r)) =ᵐ[volume.restrict (Icc s T)] v :=
    (hwsec x).symm.trans hvAe
  have heq : EqOn (fun r => w (x, r)) v (Icc s T) :=
    MeasureTheory.Measure.eqOn_Icc_of_ae_eq (volume : Measure ℝ) hsT.ne hwv
      (hwcont x) hvcont
  have hvalue : w (x, t) = v t := heq ht
  have hkernelx : MemLp (cauchyKernelTest a x) 2 (volume : Measure (Vec d)) :=
    cauchyKernelTest_memLp haε x
  have hkernelNorm :
      ‖hkernelx.toLp (cauchyKernelTest a x)‖ =
        ‖hkernel0.toLp (cauchyKernelTest a (0 : Vec d))‖ :=
    cauchyKernelTest_norm_eq x hkernelx hkernel0
  have hv0bound : |v s| ≤
      ‖hf.toLp f‖ * ‖hkernel0.toLp (cauchyKernelTest a (0 : Vec d))‖ := by
    rw [hv0]
    have h := cauchyKernelInitialPairing_abs_le hf x hkernelx
    calc
      |∫ y, f y * cauchyKernelTest a x y| ≤
          ‖hf.toLp f‖ * ‖hkernelx.toLp (cauchyKernelTest a x)‖ := h
      _ = ‖hf.toLp f‖ * ‖hkernel0.toLp (cauchyKernelTest a (0 : Vec d))‖ := by
        rw [hkernelNorm]
  have hfluxMem : MemLp (cauchyFluxPairing A u (cauchyKernelTest a x)) 2
      (volume.restrict (Icc s T)) :=
    cauchyKernelFluxPairing_memLp ha haε u x
  have hfluxInt : Integrable (cauchyFluxPairing A u (cauchyKernelTest a x))
      (volume.restrict (Icc s T)) := hfluxMem.integrable (by norm_num)
  have hinterval := abs_intervalIntegral_cauchyFlux_le ht hfluxInt
  have hfluxFull :
      (∫ r, |cauchyFluxPairing A u (cauchyKernelTest a x) r|
        ∂(volume.restrict (Icc s T))) ≤ Cflux := by
    simpa [Cflux] using cauchyKernelFluxPairing_integral_abs_le ha haε u x
  have hvinc' := hvinc s ⟨le_rfl, hsT.le⟩ t ht
  have hvDiff : |v t - v s| ≤ Cflux := by
    calc
      |v t - v s| = |∫ r in s..t,
          -cauchyFluxPairing A u (cauchyKernelTest a x) r| := by rw [hvinc']
      _ ≤ ∫ r, |cauchyFluxPairing A u (cauchyKernelTest a x) r|
          ∂(volume.restrict (Icc s T)) := hinterval
      _ ≤ Cflux := hfluxFull
  have hvbound : |v t| ≤ B := by
    calc
      |v t| = |(v t - v s) + v s| := by congr 1; ring
      _ ≤ |v t - v s| + |v s| := abs_add_le _ _
      _ ≤ Cflux + (‖hf.toLp f‖ *
          ‖hkernel0.toLp (cauchyKernelTest a (0 : Vec d))‖) :=
            add_le_add hvDiff hv0bound
      _ = B := by simp [B, add_comm]
  rw [hvalue]
  exact hvbound

end PDE.Parabolic.Lions
