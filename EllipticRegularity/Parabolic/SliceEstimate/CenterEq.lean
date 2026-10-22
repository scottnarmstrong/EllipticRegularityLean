module

public import EllipticRegularity.Parabolic.SliceEstimate.VSlice

/-!
# The equation holds a.e. in time, tested with a fixed smooth function

For a weak solution `u` with `v = ∂ₜu` (through product test functions) and a fixed
`ζ ∈ C¹_c(U)`: for a.e. `τ`, `∫ v(τ) ζ + ∫ a∇u(τ)·∇ζ = 0`.
-/

@[expose] public section

namespace PDE.Parabolic.Slice

open MeasureTheory Set Filter Topology PDE PDE.Parabolic PDE.Parabolic.WeakSlice

variable {d : ℕ}

/-- If all increments of an integrable `g` vanish then `g = 0` a.e. -/
theorem ae_zero_of_integral_Ioc_eq_zero {s t : ℝ} (hst : s < t) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioc s t))
    (h : ∀ p q : ℝ, s ≤ p → p ≤ q → q ≤ t → ∫ τ in Ioc p q, g τ = 0) :
    ∀ᵐ τ ∂(volume.restrict (Ioc s t)), g τ = 0 := by
  have hii : IntervalIntegrable g volume s t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hst.le).2 hg
  have hder := hii.ae_hasDerivAt_integral
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm, ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hder] with τ hτ hτm
  have hτI : τ ∈ uIcc s t := by rw [uIcc_of_le hst.le]; exact ⟨hτm.1.le, hτm.2.le⟩
  have hd := hτ hτI s (by rw [uIcc_of_le hst.le]; exact ⟨le_rfl, hst.le⟩)
  -- the primitive vanishes near `τ`
  have hzero : ∀ᶠ σ in 𝓝 τ, (∫ x in s..σ, g x) = 0 := by
    have hmem : Ioo s t ∈ 𝓝 τ := Ioo_mem_nhds hτm.1 hτm.2
    filter_upwards [hmem] with σ hσ
    rw [intervalIntegral.integral_of_le hσ.1.le]
    exact h s σ le_rfl hσ.1.le hσ.2.le
  have hd0 : HasDerivAt (fun σ => ∫ x in s..σ, g x) 0 τ :=
    (hasDerivAt_const τ (0 : ℝ)).congr_of_eventuallyEq hzero
  exact hd.unique hd0


/-- The equation for `u`, tested with a fixed `C¹_c` function, holds for a.e. time. -/
theorem equation_ae {lam Lam : ℝ} {U : Set (Vec d)} (hU : IsOpen U) {I : Set ℝ}
    (hI : I.OrdConnected) {a : ParCoeffField d} (ha : IsParabolicCoeff lam Lam a U I)
    (u v : ParH1Function U I) (hu : IsParabolicWeakSolution a U I u)
    (hv : ∀ ψ : ParTestFunction U (interior I),
      ∫ z in U ×ˢ I, v.toFun z * ψ.toFun z = -∫ z in U ×ˢ I, u.toFun z * parTimeDeriv ψ.toFun z)
    {ζ : Vec d → ℝ} (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ) (hζU : tsupport ζ ⊆ U)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) (hst : s < t) :
    ∀ᵐ τ ∂(volume.restrict (Ioc s t)),
      (∫ x in U, v.toFun (x, τ) * ζ x) +
        (∫ x in U, vecDot (matVecMul (a (x, τ)) (u.grad (x, τ))) (spaceGradC1 ζ x)) = 0 := by
  have hSub : Icc s t ⊆ I := hI.out hs ht
  have hfinIcc : volume (Icc s t) < ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have hvζ : IntegrableOn (fun z : Vec d × ℝ => v.toFun z * ζ z.1) (U ×ˢ Icc s t) :=
    integrableOn_mul_fst hU v.memL2 hζ.continuous hζc hζU hSub measurableSet_Icc hfinIcc
  have hN : IntegrableOn (fun τ => ∫ x in U, v.toFun (x, τ) * ζ x) (Icc s t) :=
    (integral_prod_slices hvζ).1
  have hF := integrableOn_flux_Icc hU hI ha u hζ hζc hζU hs ht
  have hΦ : IntegrableOn (fun τ => ∫ x in U, vecDot (matVecMul (a (x, τ)) (u.grad (x, τ)))
      (spaceGradC1 ζ x)) (Icc s t) := (integral_prod_slices hF).1
  refine ae_zero_of_integral_Ioc_eq_zero hst
    ((hN.mono_set Ioc_subset_Icc_self).add (hΦ.mono_set Ioc_subset_Icc_self)) ?_
  intro p q hp hpq hq
  rcases hpq.eq_or_lt with rfl | hlt
  · simp
  · have hpI : p ∈ I := hSub ⟨hp, hpq.trans hq⟩
    have hqI : q ∈ I := hSub ⟨hp.trans hpq, hq⟩
    have h1 := time_derivative_slice hU hI u v hv hζ hζc hζU hpI hqI hlt
    obtain ⟨hFi, h2⟩ := weak_slice d lam Lam U hU I hI a ha u hu ζ hζ hζc hζU p q hpI hqI hlt
    obtain ⟨_, hfub⟩ := integral_prod_slices hFi
    rw [hfub] at h2
    have hNi : IntegrableOn (fun τ => ∫ x in U, v.toFun (x, τ) * ζ x) (Ioc p q) :=
      hN.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc hp hq))
    have hΦi : IntegrableOn (fun τ => ∫ x in U, vecDot (matVecMul (a (x, τ)) (u.grad (x, τ)))
        (spaceGradC1 ζ x)) (Ioc p q) :=
      hΦ.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc hp hq))
    rw [integral_add hNi hΦi]
    simp only at h2
    linarith

end PDE.Parabolic.Slice
