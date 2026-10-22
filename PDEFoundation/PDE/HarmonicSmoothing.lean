module

public import PDEFoundation.PDE.HarmonicConvolution
public import PDEFoundation.Sobolev.H1.Pairing

/-!
# Harmonicity survives native compact convolution

The variational weak-gradient equation is converted to a coordinate Laplacian
pairing using the stored weak derivative identities. Testing with a reflected
smooth kernel then proves the mollified function is classically harmonic.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped Convolution

noncomputable section

variable {d : ℕ}

private theorem integrableOn_mul_of_memL2On_of_continuous_hasCompactSupport
    {U : Set (Vec d)} {u g : Vec d → ℝ}
    (hu : MemL2On U u) (hg : Continuous g) (hgc : HasCompactSupport g) :
    IntegrableOn (fun x => u x * g x) U := by
  apply integrableOn_mul_of_memL2On hu
  exact (hg.memLp_of_hasCompactSupport (μ := volume) (p := 2) hgc).restrict U

theorem integral_mul_laplacian_eq_zero_of_weakHarmonic
    {U : Set (Vec d)} (h : H1Function U)
    (hzero : ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U →
      ∫ x in U, vecDot (h.grad x) (classicalGradient ψ x) ∂volume = 0) :
    ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∫ x in U, h.toFun x * euclideanCoordLaplacian ψ x = 0 := by
  intro ψ hψ hψc hsupp
  have hdψ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (euclideanCoordDeriv i ψ) :=
    fun i => contDiff_euclideanCoordDeriv hψ i
  have hdψc : ∀ i : Fin d, HasCompactSupport (euclideanCoordDeriv i ψ) :=
    fun i => hasCompactSupport_euclideanCoordDeriv hψc i
  have hdψs : ∀ i : Fin d, tsupport (euclideanCoordDeriv i ψ) ⊆ U :=
    fun i => (tsupport_euclideanCoordDeriv_subset_tsupport i ψ).trans hsupp
  have hddψ : ∀ i : Fin d, Continuous (euclideanCoordSecondDeriv i i ψ) := by
    intro i
    exact ((contDiff_euclideanCoordDeriv (hdψ i) i).continuous)
  have hddψc : ∀ i : Fin d, HasCompactSupport (euclideanCoordSecondDeriv i i ψ) :=
    fun i => hasCompactSupport_euclideanCoordDeriv (hdψc i) i
  -- integrability of the two families of scalar pairings
  have hintL : ∀ i : Fin d,
      IntegrableOn (fun x => h.toFun x * euclideanCoordSecondDeriv i i ψ x) U volume :=
    fun i => integrableOn_mul_of_memL2On_of_continuous_hasCompactSupport
      h.memL2 (hddψ i) (hddψc i)
  have hintR : ∀ i : Fin d,
      IntegrableOn (fun x => h.grad x i * euclideanCoordDeriv i ψ x) U volume :=
    fun i => integrableOn_mul_of_memL2On_of_continuous_hasCompactSupport
      (h.grad_memL2 i) (hdψ i).continuous (hdψc i)
  -- the weak integration by parts, one coordinate at a time
  have key : ∀ i : Fin d,
      ∫ x in U, h.toFun x * euclideanCoordSecondDeriv i i ψ x ∂volume =
        -∫ x in U, h.grad x i * euclideanCoordDeriv i ψ x ∂volume := fun i =>
    h.hasWeakGradient i (euclideanCoordDeriv i ψ) (hdψ i) (hdψc i) (hdψs i)
  have hsplitL :
      ∫ x in U, h.toFun x * euclideanCoordLaplacian ψ x ∂volume =
        ∑ i : Fin d, ∫ x in U, h.toFun x * euclideanCoordSecondDeriv i i ψ x ∂volume := by
    have hpt : ∀ x : Vec d, h.toFun x * euclideanCoordLaplacian ψ x =
        ∑ i : Fin d, h.toFun x * euclideanCoordSecondDeriv i i ψ x := by
      intro x
      rw [euclideanCoordLaplacian, Finset.mul_sum]
    simp only [hpt]
    exact integral_finsetSum Finset.univ fun i _ => hintL i
  have hsplitR :
      ∫ x in U, vecDot (h.grad x) (classicalGradient ψ x) ∂volume =
        ∑ i : Fin d, ∫ x in U, h.grad x i * euclideanCoordDeriv i ψ x ∂volume := by
    have hpt : ∀ x : Vec d, vecDot (h.grad x) (classicalGradient ψ x) =
        ∑ i : Fin d, h.grad x i * euclideanCoordDeriv i ψ x := fun _ => rfl
    simp only [hpt]
    exact integral_finsetSum Finset.univ fun i _ => hintR i
  calc ∫ x in U, h.toFun x * euclideanCoordLaplacian ψ x ∂volume
      = ∑ i : Fin d, ∫ x in U, h.toFun x * euclideanCoordSecondDeriv i i ψ x ∂volume :=
        hsplitL
    _ = ∑ i : Fin d, -∫ x in U, h.grad x i * euclideanCoordDeriv i ψ x ∂volume :=
        Finset.sum_congr rfl fun i _ => key i
    _ = -∑ i : Fin d, ∫ x in U, h.grad x i * euclideanCoordDeriv i ψ x ∂volume :=
        Finset.sum_neg_distrib _
    _ = -∫ x in U, vecDot (h.grad x) (classicalGradient ψ x) ∂volume := by rw [hsplitR]
    _ = 0 := by rw [hzero ψ hψ hψc hsupp, neg_zero]


theorem euclideanCoordLaplacian_convolution_indicator_eq_zero {U : Set (Vec d)}
    (hUopen : IsOpen U) {u : H1Function U} (hu : ∀ φ : WeakTestFunction U,
      ∫ x in U, vecDot (u.grad x) (φ.grad x) = 0)
    {K : Vec d → ℝ} (hK_supp : HasCompactSupport K) (hK : ContDiff ℝ (⊤ : ℕ∞) K) (A : Vec d)
    (hsub : tsupport (fun y : Vec d => K (A - y)) ⊆ U) :
    euclideanCoordLaplacian
        (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Set.indicator U u.toFun) A = 0 := by
  have hUm : MeasurableSet U := hUopen.measurableSet
  have hmem_indicator : MemLp (Set.indicator U u.toFun) 2 volume := by
    rw [MeasureTheory.memLp_indicator_iff_restrict hUm]
    exact u.memL2
  have hloc_indicator : LocallyIntegrable (Set.indicator U u.toFun) volume :=
    hmem_indicator.locallyIntegrable (by norm_num)
  set ψ : Vec d → ℝ := fun y => K (A - y) with hψdef
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hK.comp (contDiff_const.sub contDiff_id)
  have hψ_supp : HasCompactSupport ψ := by
    show HasCompactSupport (K ∘ Homeomorph.subLeft A)
    simpa [ψ, Function.comp_def] using hK_supp.comp_homeomorph (Homeomorph.subLeft A)
  have hweak_zero : ∫ y in U, u y * euclideanCoordLaplacian ψ y ∂volume = 0 :=
    integral_mul_laplacian_eq_zero_of_weakHarmonic u
      (fun φ hφ hφc hφs => hu ⟨φ, hφ, hφc, hφs⟩)
      ψ hψ hψ_supp hsub
  have hweak_zero' : ∫ y in U, u y * euclideanCoordLaplacian K (A - y) ∂volume = 0 := by
    refine Eq.trans ?_ hweak_zero
    refine MeasureTheory.setIntegral_congr_fun hUm fun y _ => ?_
    congr 1
    exact (euclideanCoordLaplacian_comp_const_sub hK A y).symm
  rw [euclideanCoordLaplacian_convolution_left hK_supp hK hloc_indicator,
    MeasureTheory.convolution_def]
  simpa using
    (integral_mul_indicator_const_sub_eq_setIntegral hUm A (euclideanCoordLaplacian K)
      u.toFun).trans hweak_zero'


end

end PDE
