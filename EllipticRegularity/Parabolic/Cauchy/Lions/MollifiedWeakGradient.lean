module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.Lions.KernelTest
public import EllipticRegularity.Parabolic.Cauchy.Lions.EnergyFields

/-! # Spatial weak gradients of the mollified Lions fields -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.Lions

/-- At almost every time, spatial mollification commutes with the weak gradient of a Lions value
field. The mollified function is smooth in space, and its classical derivative is the mollification
of the weak-gradient coordinate. -/
theorem cauchyMollified_ae_sliceWeakGradient
    {d : ℕ} {s T ε : ℝ} (hε : 0 < ε)
    {u : CauchyX d s T} {u₀ : CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀) :
    ∀ᵐ t ∂(volume.restrict (Icc s T)),
      HasWeakGradientOn (univ : Set (Vec d))
        (fun x => PDE.Parabolic.Energy.mollT ε univ (cauchyEnergyValue u) (x, t))
        (fun x i => PDE.Parabolic.Energy.mollT ε univ
          (fun z => cauchyEnergyGradient u z i) (x, t)) := by
  have hweak := cauchyClosure_ae_energySliceWeakGradient hclose
  have hval := PDE.Parabolic.Energy.ae_slice_memLp (d := d)
    (K1 := (univ : Set (Vec d))) (J := Icc s T) (g := cauchyEnergyValue u)
    MeasurableSet.univ (cauchyEnergyValue_memLp u)
  have hval' : ∀ᵐ t ∂(volume.restrict (Icc s T)),
      MemLp (fun x => cauchyEnergyValue u (x, t)) 2 volume := by
    filter_upwards [hval] with t ht
    simpa using ht
  have hgrad : ∀ i : Fin d, ∀ᵐ t ∂(volume.restrict (Icc s T)),
      MemLp (fun x => cauchyEnergyGradient u (x, t) i) 2 volume := by
    intro i
    have hs := PDE.Parabolic.Energy.ae_slice_memLp (d := d)
      (K1 := (univ : Set (Vec d))) (J := Icc s T)
      (g := fun z => cauchyEnergyGradient u z i) MeasurableSet.univ
      (cauchyEnergyGradient_coord_memLp u i)
    filter_upwards [hs] with t ht
    simpa using ht
  have hgradAll : ∀ᵐ t ∂(volume.restrict (Icc s T)), ∀ i : Fin d,
      MemLp (fun x => cauchyEnergyGradient u (x, t) i) 2 volume := by
    rw [ae_all_iff]
    exact hgrad
  filter_upwards [hweak, hval', hgradAll] with t ht hvt hgt
  have hFloc : LocallyIntegrable (fun x : Vec d => cauchyEnergyValue u (x, t)) volume :=
    hvt.locallyIntegrable (by norm_num)
  have hcont : ContDiff ℝ (⊤ : ℕ∞)
      (PDE.wholeSpaceMollify ε
        (fun y => cauchyEnergyValue u (y, t))) :=
    PDE.Parabolic.Energy.moll_contDiff hε hFloc
  have hderiv : ∀ i : Fin d, ∀ x : Vec d,
      fderiv ℝ (PDE.wholeSpaceMollify ε
        (univ.indicator fun y => cauchyEnergyValue u (y, t))) x (basisVec i) =
      PDE.Parabolic.Energy.mollT ε univ
        (fun z => cauchyEnergyGradient u z i) (x, t) := by
    intro i x
    have hGloc : LocallyIntegrable (fun y : Vec d => cauchyEnergyGradient u (y, t) i)
        volume := (hgt i).locallyIntegrable (by norm_num)
    have htestTop : ContDiff ℝ (⊤ : ℕ∞) (cauchyKernelTest ε x) := by
      unfold cauchyKernelTest
      exact (PDE.Parabolic.Energy.kern_smooth ε).comp
        (contDiff_const.sub contDiff_id)
    have hweakKernel := ht i (cauchyKernelTest ε x)
      htestTop
      (cauchyKernelTest_hasCompactSupport hε x) (subset_univ _)
    have hweakKernel' :
        ∫ y, cauchyEnergyValue u (y, t) *
          (fderiv ℝ (cauchyKernelTest ε x) y) (basisVec i) =
        -∫ y, cauchyEnergyGradient u (y, t) i * cauchyKernelTest ε x y := by
      simpa only [setIntegral_univ] using hweakKernel
    have hpair :
        ∫ y, fderiv ℝ (PDE.Parabolic.Energy.kern ε) (x - y) (basisVec i) *
            cauchyEnergyValue u (y, t) =
        ∫ y, PDE.Parabolic.Energy.kern ε (x - y) *
            cauchyEnergyGradient u (y, t) i := by
      have hrewrite :
          ∫ y, cauchyEnergyValue u (y, t) *
              (fderiv ℝ (cauchyKernelTest ε x) y) (basisVec i) =
            -(∫ y, cauchyEnergyValue u (y, t) *
              fderiv ℝ (PDE.Parabolic.Energy.kern ε) (x - y) (basisVec i)) := by
        calc
          _ = ∫ y, cauchyEnergyValue u (y, t) *
              spaceGradC1 (cauchyKernelTest ε x) y i := by
                apply integral_congr_ae
                filter_upwards [] with y
                rfl
          _ = ∫ y, -(cauchyEnergyValue u (y, t) *
              fderiv ℝ (PDE.Parabolic.Energy.kern ε) (x - y) (basisVec i)) := by
                apply integral_congr_ae
                filter_upwards [] with y
                rw [cauchyKernelTest_spaceGrad]
                ring
          _ = -(∫ y, cauchyEnergyValue u (y, t) *
              fderiv ℝ (PDE.Parabolic.Energy.kern ε) (x - y) (basisVec i)) := by
                rw [integral_neg]
      have hrewriteR :
          -∫ y, cauchyEnergyGradient u (y, t) i * cauchyKernelTest ε x y =
            -(∫ y, PDE.Parabolic.Energy.kern ε (x - y) *
              cauchyEnergyGradient u (y, t) i) := by
        rw [show cauchyKernelTest ε x =
          (fun y => PDE.Parabolic.Energy.kern ε (x - y)) by rfl]
        congr 1
        apply integral_congr_ae
        filter_upwards [] with y
        ring
      have hpairNeg :
          -(∫ y, cauchyEnergyValue u (y, t) *
              fderiv ℝ (PDE.Parabolic.Energy.kern ε) (x - y) (basisVec i)) =
            -(∫ y, PDE.Parabolic.Energy.kern ε (x - y) *
              cauchyEnergyGradient u (y, t) i) := by
        calc
          _ = ∫ y, cauchyEnergyValue u (y, t) *
              (fderiv ℝ (cauchyKernelTest ε x) y) (basisVec i) := hrewrite.symm
          _ = -∫ y, cauchyEnergyGradient u (y, t) i * cauchyKernelTest ε x y :=
              hweakKernel'
          _ = _ := hrewriteR
      have hcomm :
          (∫ y, PDE.Parabolic.Energy.kern ε (x - y) *
              cauchyEnergyGradient u (y, t) i) =
            ∫ y, cauchyEnergyGradient u (y, t) i *
              PDE.Parabolic.Energy.kern ε (x - y) := by
        apply integral_congr_ae
        filter_upwards [] with y
        ring
      calc
        _ = ∫ y, cauchyEnergyValue u (y, t) *
            fderiv ℝ (PDE.Parabolic.Energy.kern ε) (x - y) (basisVec i) := by
              apply integral_congr_ae
              filter_upwards [] with y
              ring
        _ = ∫ y, PDE.Parabolic.Energy.kern ε (x - y) *
            cauchyEnergyGradient u (y, t) i := neg_injective hpairNeg
    have hfd := PDE.Parabolic.Energy.moll_fderiv_apply hε hFloc x (basisVec i)
    have hind : univ.indicator (fun y : Vec d => cauchyEnergyValue u (y, t)) =
        (fun y => cauchyEnergyValue u (y, t)) := by
      funext y
      simp
    rw [hind, hfd, hpair]
    rw [PDE.Parabolic.Energy.mollT_eq]
    apply integral_congr_ae
    filter_upwards [] with y
    simp
  have hgradEq :
      (fun x i => (fderiv ℝ
        (PDE.wholeSpaceMollify ε
          (fun y => cauchyEnergyValue u (y, t))) x) (basisVec i)) =
      (fun x i => PDE.wholeSpaceMollify ε
        (fun y => cauchyEnergyGradient u (y, t) i) x) := by
    funext x i
    have hdi := hderiv i x
    rw [show univ.indicator (fun y : Vec d => cauchyEnergyValue u (y, t)) =
      (fun y => cauchyEnergyValue u (y, t)) by funext y; simp] at hdi
    simpa [PDE.Parabolic.Energy.mollT, Set.indicator_univ] using hdi
  have hclassical := HasWeakGradientOn.of_contDiff (U := (univ : Set (Vec d)))
    (hcont.of_le (by exact_mod_cast le_top))
  have hwithMoll : HasWeakGradientOn (univ : Set (Vec d))
      (PDE.wholeSpaceMollify ε (fun y => cauchyEnergyValue u (y, t)))
      (fun x i => PDE.wholeSpaceMollify ε
        (fun y => cauchyEnergyGradient u (y, t) i) x) := by
    rw [← hgradEq]
    exact hclassical
  simpa [PDE.Parabolic.Energy.mollT, Set.indicator_univ] using hwithMoll

end PDE.Parabolic.Lions
