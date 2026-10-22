module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.Lions.MollifiedRepresentatives
public import EllipticRegularity.Parabolic.Cauchy.Lions.MollifiedPairing
public import EllipticRegularity.Parabolic.Energy.Data
public import EllipticRegularity.Parabolic.Energy.Bridge

/-! # Time-slice identities for mollified Lions fields -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set Metric

namespace PDE.Parabolic.Lions

private theorem mollifiedKernelPairing_continuousOn {d : ℕ} {s T δ : ℝ}
    {w : Vec d × ℝ → ℝ} (hwm : Measurable w)
    (hwcont : ∀ x, ContinuousOn (fun t => w (x, t)) (Icc s T))
    {B : ℝ} (_hB : 0 ≤ B) (hwB : ∀ x t, t ∈ Icc s T → |w (x, t)| ≤ B)
    (hδ : 0 < δ) (x : Vec d) :
    ContinuousOn (fun t => ∫ y, PDE.Parabolic.Energy.kern δ (x - y) * w (y, t))
      (Icc s T) := by
  let k : Vec d → ℝ := fun y => PDE.Parabolic.Energy.kern δ (x - y)
  have hkcont : Continuous k := by
    exact (PDE.Parabolic.Energy.kern_continuous δ).comp
      (continuous_const.sub continuous_id)
  have hkcompact : HasCompactSupport k := by
    change HasCompactSupport (cauchyKernelTest δ x)
    exact cauchyKernelTest_hasCompactSupport hδ x
  have hkint : Integrable k (volume : Measure (Vec d)) :=
    hkcont.integrable_of_hasCompactSupport hkcompact
  have hboundInt : Integrable (fun y : Vec d => B * ‖k y‖) volume := by
    simpa [mul_comm] using hkint.norm.const_mul B
  apply continuousOn_of_dominated
  · intro t ht
    have hsection : Measurable (fun y : Vec d => w (y, t)) :=
      hwm.comp (measurable_id.prodMk measurable_const)
    exact hkcont.aestronglyMeasurable.mul hsection.aestronglyMeasurable
  · intro t ht
    filter_upwards [] with y
    have hy := hwB y t ht
    simp only [Real.norm_eq_abs, abs_mul]
    calc
      |k y| * |w (y, t)| ≤ |k y| * B := mul_le_mul_of_nonneg_left hy (abs_nonneg _)
      _ = B * ‖k y‖ := by rw [Real.norm_eq_abs]; ring
  · exact hboundInt
  · filter_upwards [] with y
    exact continuousOn_const.mul (hwcont y)

private theorem mollifiedKernelPairing_ae_eq_scalarPairing
    {d : ℕ} {s T δ ε : ℝ} {u : CauchyX d s T}
    {w : Vec d × ℝ → ℝ}
    (hwae : w =ᵐ[slabMeasure d s T]
      PDE.Parabolic.Energy.mollT ε univ (cauchyEnergyValue u))
    (hδ : 0 < δ) (hε : 0 < ε) (x : Vec d) :
    (fun t => ∫ y, PDE.Parabolic.Energy.kern δ (x - y) * w (y, t)) =ᵐ[
      volume.restrict (Icc s T)]
        cauchyValuePairing u (cauchyDoubleKernelTest δ ε x) := by
  have hmeasure : (volume : Measure (Vec d)).prod
      (volume.restrict (Icc s T)) = slabMeasure d s T := by
    change (volume : Measure (Vec d)).prod (volume.restrict (Icc s T)) =
      (volume : Measure (Vec d × ℝ)).restrict (univ ×ˢ Icc s T)
    calc
      _ = (volume.restrict (univ : Set (Vec d))).prod
          (volume.restrict (Icc s T)) := by simp
      _ = (volume : Measure (Vec d × ℝ)).restrict (univ ×ˢ Icc s T) :=
        (PDE.Parabolic.Energy.volume_restrict_prod univ (Icc s T)).symm
  have hprod : ∀ᵐ z ∂((volume : Measure (Vec d)).prod
      (volume.restrict (Icc s T))),
      w z = PDE.Parabolic.Energy.mollT ε univ (cauchyEnergyValue u) z := by
    have hwae' : ∀ᵐ z ∂(slabMeasure d s T),
        w z = PDE.Parabolic.Energy.mollT ε univ (cauchyEnergyValue u) z := hwae
    rw [← hmeasure] at hwae'
    exact hwae'
  have htime := PDE.Parabolic.Energy.ae_ae_swap hprod
  have hslice := cauchyEnergyValue_ae_sliceMemLp u
  have hkcont : Continuous (fun y : Vec d =>
      PDE.Parabolic.Energy.kern δ (x - y)) := by
    exact (PDE.Parabolic.Energy.kern_continuous δ).comp
      (continuous_const.sub continuous_id)
  have hkcompact : HasCompactSupport (cauchyKernelTest δ x) :=
    cauchyKernelTest_hasCompactSupport hδ x
  have htestcont : Continuous (cauchyKernelTest δ x) := hkcont
  filter_upwards [htime, hslice] with t hwt hraw
  have hrawLoc : LocallyIntegrable (fun y : Vec d => cauchyEnergyValue u (y, t)) volume :=
    hraw.locallyIntegrable (by norm_num)
  have hwt' : ∀ᵐ y ∂(volume : Measure (Vec d)),
      w (y, t) = PDE.wholeSpaceMollify ε (fun q => cauchyEnergyValue u (q, t)) y := by
    filter_upwards [hwt] with y hy
    have hmoll : PDE.Parabolic.Energy.mollT ε univ (cauchyEnergyValue u) (y, t) =
        PDE.wholeSpaceMollify ε (fun q => cauchyEnergyValue u (q, t)) y := by
      simp [PDE.Parabolic.Energy.mollT]
    rw [hy, hmoll]
  have hself := wholeSpaceMollify_pairing hε hrawLoc htestcont hkcompact
  have hleft : ∫ y, PDE.Parabolic.Energy.kern δ (x - y) * w (y, t) =
      ∫ y, PDE.wholeSpaceMollify ε (fun q => cauchyEnergyValue u (q, t)) y *
        cauchyKernelTest δ x y := by
    apply integral_congr_ae
    filter_upwards [hwt'] with y hy
    rw [hy]
    simp only [cauchyKernelTest]
    ring
  have hright : ∫ y,
      (fun q => cauchyEnergyValue u (q, t)) y *
        PDE.wholeSpaceMollify ε (cauchyKernelTest δ x) y =
      cauchyValuePairing u (cauchyDoubleKernelTest δ ε x) t := by
    rw [cauchyValuePairing, cauchyDoubleKernelTest]
  have hpair : ∫ y, PDE.wholeSpaceMollify ε
      (fun q => cauchyEnergyValue u (q, t)) y * cauchyKernelTest δ x y =
      ∫ y, (fun q => cauchyEnergyValue u (q, t)) y *
        PDE.wholeSpaceMollify ε (cauchyKernelTest δ x) y := by
    exact hself
  rw [hleft, hpair, hright]

private theorem mollifiedRepresentative_weakCont {d : ℕ} {s T : ℝ}
    {w : Vec d × ℝ → ℝ} (hwm : Measurable w)
    (hwcont : ∀ x, ContinuousOn (fun t => w (x, t)) (Icc s T))
    {B : ℝ} (_hB : 0 ≤ B) (hwB : ∀ x t, t ∈ Icc s T → |w (x, t)| ≤ B)
    (ψ : Vec d → ℝ) (hψ : PDE.IsL2c (univ : Set (Vec d)) ψ) :
    ContinuousOn (fun t => ∫ x in (univ : Set (Vec d)), w (x, t) * ψ x) (Icc s T) := by
  rcases hψ with ⟨hψL2, K, hK, hKU, hψ0⟩
  let : IsFiniteMeasure (volume.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  have hψK : MemLp ψ 2 (volume.restrict K) :=
    hψL2.mono_measure (Measure.restrict_mono hKU le_rfl)
  have hψInt : Integrable ψ (volume.restrict K) := hψK.integrable (by norm_num)
  have hbound : Integrable (fun x : Vec d => B * |ψ x|) (volume.restrict K) := by
    simpa [mul_comm] using hψInt.norm.const_mul B
  have hFcont : ∀ᵐ x ∂(volume.restrict K),
      ContinuousOn (fun t => ψ x * w (x, t)) (Icc s T) :=
    ae_of_all _ fun x => continuousOn_const.mul (hwcont x)
  have hFmeas : ∀ t ∈ Icc s T,
      AEStronglyMeasurable (fun x : Vec d => ψ x * w (x, t)) (volume.restrict K) := by
    intro t ht
    have hwx : Measurable (fun x : Vec d => w (x, t)) :=
      hwm.comp (measurable_id.prodMk measurable_const)
    exact hψK.aestronglyMeasurable.mul hwx.aestronglyMeasurable
  have hFbound : ∀ t ∈ Icc s T, ∀ᵐ x ∂(volume.restrict K),
      ‖ψ x * w (x, t)‖ ≤ B * |ψ x| := by
    intro t ht
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |ψ x| * |w (x, t)| ≤ |ψ x| * B :=
        mul_le_mul_of_nonneg_left (hwB x t ht) (abs_nonneg _)
      _ = B * |ψ x| := by ring
  have hcontK : ContinuousOn (fun t => ∫ x in K, ψ x * w (x, t)) (Icc s T) := by
    apply continuousOn_of_dominated hFmeas hFbound hbound hFcont
  have hset (t : ℝ) :
      (∫ x in (univ : Set (Vec d)), w (x, t) * ψ x) = ∫ x in K, ψ x * w (x, t) := by
    rw [setIntegral_univ]
    calc
      ∫ x, w (x, t) * ψ x = ∫ x, ψ x * w (x, t) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
      _ = ∫ x in K, ψ x * w (x, t) := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        simp [hψ0 x hx]
  exact hcontK.congr fun t ht => hset t

/-- The fixed-scale chosen value and gradient representatives form an `H¹_par` function.
This is an intermediate object; its mollified flux is retained separately in the accompanying
bundle because spatial convolution does not commute with a variable coefficient field. -/
theorem exists_cauchy_mollified_parabolicFunction
    {d : ℕ} {lam Lam s T ε : ℝ} {A : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam A univ (Icc s T))
    (hε : 0 < ε) (f : Vec d → ℝ) (hf : MemLp f 2 (volume : Measure (Vec d)))
    (u : CauchyX d s T) {u₀ : CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u) :
    ∃ W : ParH1Function (univ : Set (Vec d)) (Icc s T),
      ∃ w : Vec d × ℝ → ℝ, ∃ D G : Vec d × ℝ → Vec d,
      Measurable w ∧ Measurable D ∧ Measurable G ∧
      (∀ x, ContinuousOn (fun t => w (x, t)) (Icc s T)) ∧
      (∀ x, (fun t => PDE.Parabolic.Energy.mollT ε univ
        (cauchyEnergyValue u) (x, t)) =ᵐ[volume.restrict (Icc s T)]
          (fun t => w (x, t))) ∧
      (∀ t ∈ Icc s T, ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun x => w (x, t)) 2 (volume.restrict K)) ∧
      MemLp w 2 (slabMeasure d s T) ∧
      (∀ i : Fin d, MemLp (fun z => D z i) 2 (slabMeasure d s T)) ∧
      (∀ i : Fin d, MemLp (fun z => G z i) 2 (slabMeasure d s T)) ∧
      (∀ᵐ z ∂(slabMeasure d s T),
        w z = PDE.Parabolic.Energy.mollT ε univ (cauchyEnergyValue u) z) ∧
      (∀ i, ∀ᵐ z ∂(slabMeasure d s T),
        D z i = PDE.Parabolic.Energy.mollT ε univ
          (fun z => cauchyEnergyGradient u z i) z) ∧
      (∀ i, ∀ᵐ z ∂(slabMeasure d s T),
        G z i = PDE.Parabolic.Energy.mollT ε univ
          (fun z => matVecMul (A z) (cauchyEnergyGradient u z) i) z) ∧
      (∀ᵐ t ∂(volume.restrict (Icc s T)),
        HasWeakGradientOn (univ : Set (Vec d)) (fun x => w (x, t))
          (fun x i => D (x, t) i)) ∧
      (∃ B : ℝ, 0 ≤ B ∧ (∀ x t, t ∈ Icc s T → |w (x, t)| ≤ B)) ∧
      W.toFun = w ∧ W.grad = D := by
  obtain ⟨w, D, G, hwm, hDm, hGm, hwcont, hwsec, hloc, hWmem, hDmem, hGmem,
    hwae, hDae, hGae, hWgrad, ⟨B, hB, hwB⟩⟩ :=
      exists_cauchy_mollified_energy_representatives hsT ha hε f hf u hclose hrep
  let W : ParH1Function (univ : Set (Vec d)) (Icc s T) := {
    toFun := w
    grad := D
    memL2 := by simpa [slabMeasure] using hWmem
    gradMemL2 := by
      intro i
      simpa [slabMeasure] using hDmem i
    sliceWeakGradient := hWgrad
    sliceL2loc := by
      intro t ht K hK _
      exact hloc t ht K hK
    weakCont := by
      intro ψ hψ
      exact mollifiedRepresentative_weakCont hwm hwcont hB hwB ψ hψ }
  exact ⟨W, w, D, G, hwm, hDm, hGm, hwcont, hwsec, hloc, hWmem, hDmem, hGmem,
    hwae, hDae, hGae, hWgrad, ⟨B, hB, hwB⟩, rfl, rfl⟩

/-- A chosen mollified representative retains the spatial weak-gradient identity at almost every
time, in the collar format expected by `Energy.Data`. -/
theorem cauchyMollifiedRepresentative_hwg
    {d : ℕ} {s T : ℝ} {K : Set (Vec d)} (_hK : IsCompact K)
    {δ0 : ℝ} (_hδ0 : 0 < δ0)
    {W : ParH1Function (univ : Set (Vec d)) (Icc s T)}
    {w : Vec d × ℝ → ℝ} {D : Vec d × ℝ → Vec d}
    (hW : W.toFun = w) (hD : W.grad = D)
    (hWgrad : ∀ᵐ t ∂(volume.restrict (Icc s T)),
      HasWeakGradientOn (univ : Set (Vec d))
        (fun x => w (x, t)) (fun x i => D (x, t) i)) :
    ∀ᵐ τ ∂(volume.restrict (Ioc s T)), ∀ a' : ℝ, 0 < a' → a' ≤ δ0 →
      ∀ x ∈ K, ∀ i,
        ∫ y in cthickening δ0 K,
            fderiv ℝ (PDE.Parabolic.Energy.kern a') (x - y) (basisVec i) * w (y, τ) =
          ∫ y in cthickening δ0 K,
            PDE.Parabolic.Energy.kern a' (x - y) * D (y, τ) i := by
  have hIoc : Ioc s T ⊆ Icc s T := Ioc_subset_Icc_self
  have hslice := ae_restrict_of_ae_restrict_of_subset hIoc hWgrad
  filter_upwards [hslice] with τ hτ a' ha' haδ x hx i
  have hball : closedBall x a' ⊆ cthickening δ0 K :=
    (closedBall_subset_cthickening hx a').trans (cthickening_mono haδ K)
  have hweak : HasWeakGradientOn (univ : Set (Vec d))
      (parSlice W.toFun τ) (parSlice W.grad τ) := by
    change HasWeakGradientOn (univ : Set (Vec d))
      (fun x => W.toFun (x, τ)) (fun x i => W.grad (x, τ) i)
    rw [hW, hD]
    exact hτ
  have hid := PDE.Parabolic.Energy.weakGrad_identity isOpen_univ W
    isClosed_cthickening.measurableSet (Set.subset_univ _) ha' hball hweak
    (fun j => Filter.EventuallyEq.rfl) i
  simpa [hW, hD] using hid

private theorem doubleKernelFluxPairing_ae
    {d : ℕ} {lam Lam s T δ ε : ℝ} {A : ParCoeffField d}
    (ha : IsParabolicCoeff lam Lam A univ (Icc s T))
    {u : CauchyX d s T} (hδ : 0 < δ) (hε : 0 < ε) (x : Vec d) :
    -cauchyFluxPairing A u (cauchyDoubleKernelTest δ ε x) =ᵐ[
      volume.restrict (Icc s T)] fun t =>
        ∑ i : Fin d, ∫ y,
          PDE.wholeSpaceMollify ε
            (fun q => matVecMul (A (q, t)) (cauchyEnergyGradient u (q, t)) i) y *
            fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i) := by
  have hψ : ContDiff ℝ 1 (cauchyDoubleKernelTest δ ε x) :=
    (cauchyDoubleKernelTest_contDiff hε x).of_le (by norm_num)
  have hψc : HasCompactSupport (cauchyDoubleKernelTest δ ε x) :=
    cauchyDoubleKernelTest_hasCompactSupport hδ hε x
  have hslice := cauchyEnergyFlux_ae_sliceMemLp ha (u := u)
  have hgradCont (i : Fin d) : Continuous fun y : Vec d =>
      fderiv ℝ (cauchyDoubleKernelTest δ ε x) y (basisVec i) := by
    exact (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hgradComp (i : Fin d) : HasCompactSupport (fun y : Vec d =>
      fderiv ℝ (cauchyDoubleKernelTest δ ε x) y (basisVec i)) := by
    exact (hψc.fderiv (𝕜 := ℝ)).comp_left
      (g := fun L : Vec d →L[ℝ] ℝ => L (basisVec i)) (by simp)
  filter_upwards [hslice] with t ht
  let F : Fin d → Vec d → ℝ := fun i y =>
    matVecMul (A (y, t)) (cauchyEnergyGradient u (y, t)) i
  have hFloc (i : Fin d) : LocallyIntegrable (F i) volume :=
    (ht i).locallyIntegrable (by norm_num)
  have hgradLp (i : Fin d) : MemLp
      (fun y : Vec d => fderiv ℝ (cauchyDoubleKernelTest δ ε x) y (basisVec i)) 2 volume :=
    (hgradCont i).memLp_of_hasCompactSupport (hgradComp i)
  have hterm (i : Fin d) : Integrable
      (fun y : Vec d => F i y *
        fderiv ℝ (cauchyDoubleKernelTest δ ε x) y (basisVec i)) volume :=
    (ht i).integrable_mul (hgradLp i)
  have hpair (i : Fin d) :
      ∫ y, PDE.wholeSpaceMollify ε (F i) y *
          fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i) =
        -∫ y, F i y *
          fderiv ℝ (cauchyDoubleKernelTest δ ε x) y (basisVec i) := by
    simpa [F] using wholeSpaceMollify_kernelDerivative_pairing hδ hε (hFloc i) x i
  have hsum : cauchyFluxPairing A u (cauchyDoubleKernelTest δ ε x) t =
      ∑ i : Fin d, ∫ y, F i y *
        fderiv ℝ (cauchyDoubleKernelTest δ ε x) y (basisVec i) := by
    rw [cauchyFluxPairing]
    calc
      ∫ y, vecDot (matVecMul (A (y, t)) (cauchyEnergyGradient u (y, t)))
          (spaceGradC1 (cauchyDoubleKernelTest δ ε x) y) =
          ∫ y, ∑ i : Fin d, F i y *
            fderiv ℝ (cauchyDoubleKernelTest δ ε x) y (basisVec i) := by
              apply integral_congr_ae
              filter_upwards [] with y
              simp [vecDot, F, spaceGradC1]
      _ = ∑ i : Fin d, ∫ y, F i y *
          fderiv ℝ (cauchyDoubleKernelTest δ ε x) y (basisVec i) :=
            integral_finsetSum _ fun i _ => hterm i
  calc
    -cauchyFluxPairing A u (cauchyDoubleKernelTest δ ε x) t =
        -∑ i : Fin d, ∫ y, F i y *
          fderiv ℝ (cauchyDoubleKernelTest δ ε x) y (basisVec i) := by rw [hsum]
    _ = ∑ i : Fin d, ∫ y, PDE.wholeSpaceMollify ε (F i) y *
          fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hpair i]

theorem exists_cauchy_mollified_kernel_time_representative
    {d : ℕ} {lam Lam s T δ ε : ℝ} {A : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam A univ (Icc s T))
    (hδ : 0 < δ) (hε : 0 < ε) (f : Vec d → ℝ)
    (hf : MemLp f 2 (volume : Measure (Vec d)))
    (u : CauchyX d s T)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (w : Vec d × ℝ → ℝ) (hwm : Measurable w)
    (hwcont : ∀ x, ContinuousOn (fun t => w (x, t)) (Icc s T))
    (hwae : w =ᵐ[slabMeasure d s T]
      PDE.Parabolic.Energy.mollT ε univ (cauchyEnergyValue u))
    (B : ℝ) (hB : 0 ≤ B)
    (hwB : ∀ x t, t ∈ Icc s T → |w (x, t)| ≤ B)
    (x : Vec d) :
    ∃ v : ℝ → ℝ, ContinuousOn v (Icc s T) ∧
      (∀ t ∈ Icc s T,
        (∫ y, PDE.Parabolic.Energy.kern δ (x - y) * w (y, t)) = v t) ∧
      v s = ∫ y, f y * cauchyDoubleKernelTest δ ε x y ∧
      ∀ p ∈ Icc s T, ∀ q ∈ Icc s T,
        v q - v p = ∫ t in p..q, ∑ i : Fin d, ∫ y,
          PDE.wholeSpaceMollify ε
            (fun z => matVecMul (A (z, t)) (cauchyEnergyGradient u (z, t)) i) y *
            fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i) := by
  obtain ⟨v, hvcont, hvae, hvinit, hvinc⟩ :=
    exists_cauchy_scalar_pairing_representative hsT ha f hf u hrep
      (cauchyDoubleKernelTest δ ε x)
      ((cauchyDoubleKernelTest_contDiff hε x).of_le (by norm_num))
      (cauchyDoubleKernelTest_hasCompactSupport hδ hε x)
  have hAcont := mollifiedKernelPairing_continuousOn hwm hwcont hB hwB hδ x
  have hAae := mollifiedKernelPairing_ae_eq_scalarPairing hwae hδ hε x
  have hAev :
      (fun t => ∫ y, PDE.Parabolic.Energy.kern δ (x - y) * w (y, t)) =ᵐ[
        volume.restrict (Icc s T)] v := hAae.trans hvae
  have hEqOn : EqOn
      (fun t => ∫ y, PDE.Parabolic.Energy.kern δ (x - y) * w (y, t)) v (Icc s T) :=
    Measure.eqOn_Icc_of_ae_eq (volume : Measure ℝ) hsT.ne hAev hAcont hvcont
  refine ⟨v, hvcont, fun t ht => hEqOn ht, ?_, ?_⟩
  · simpa [cauchyDoubleKernelTest] using hvinit
  · intro p hp q hq
    have hflux := doubleKernelFluxPairing_ae ha (u := u) hδ hε x
    have hflux' : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Icc s T →
        -cauchyFluxPairing A u (cauchyDoubleKernelTest δ ε x) t =
          ∑ i : Fin d, ∫ y,
            PDE.wholeSpaceMollify ε
              (fun z => matVecMul (A (z, t)) (cauchyEnergyGradient u (z, t)) i) y *
              fderiv ℝ (PDE.Parabolic.Energy.kern δ) (x - y) (basisVec i) :=
      (ae_restrict_iff' measurableSet_Icc).1 hflux
    rw [hvinc p hp q hq]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hflux'] with t ht htu
    have htu' : t ∈ Icc s T := by
      rcases mem_uIoc.mp htu with ⟨hpt, htq⟩ | ⟨hqt, htp⟩
      · exact ⟨hp.1.trans hpt.le, htq.trans hq.2⟩
      · exact ⟨hq.1.trans hqt.le, htp.trans hp.2⟩
    exact ht htu'

end PDE.Parabolic.Lions
