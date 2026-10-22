module

public import EllipticRegularity.Parabolic.Sobolev.EndpointGN
public import EllipticRegularity.Parabolic.ParabolicDef
public import EllipticRegularity.Parabolic.Energy.Slab
public import PDEFoundation.Sobolev.Ch4.ZeroExtension

/-!
# Parabolic Sobolev inequalities on almost-everywhere slices

Joint `L²` control in `ParH1Function` gives `L²` spatial slices for almost
every time.  Combined with the stored slice weak-gradient property, this
recovers whole-space or compactly supported spatial `H¹` functions to which
the all-dimensional Gagliardo--Nirenberg estimate applies.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic

open MeasureTheory Set

/-- Convert a powered extended `Lᵖ` norm into its defining spatial energy
integral.  This identifies the time-integrated norm statement below with the
double-integral form of the parabolic Sobolev inequality. -/
theorem eLpNorm_rpow_eq_lintegral_enorm_rpow
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (q : ℝ) (hq : 0 < q) (hf : AEStronglyMeasurable f μ) :
    (eLpNorm f (ENNReal.ofReal q) μ) ^ q =
      ∫⁻ x, ‖f x‖ₑ ^ q ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by simp [hq]) (by simp) hf]
  rw [ENNReal.toReal_ofReal hq.le, ← ENNReal.rpow_mul]
  have hexp : (1 / q : ℝ) * q = 1 := by
    field_simp
  rw [hexp, ENNReal.rpow_one]

/-- Almost every time slice of a parabolic `H¹` function is an `H¹` function
on its spatial domain.  The returned representative uses the given value and
gradient slices literally. -/
theorem ae_parH1_slice_h1
    {d : ℕ} {U : Set (Vec d)} {I : Set ℝ}
    (hU : IsOpen U) (u : ParH1Function U I) :
    ∀ᵐ t ∂(volume.restrict I),
      ∃ v : H1Function U,
        v.toFun = parSlice u.toFun t ∧ v.grad = parSlice u.grad t := by
  have hvalue := Energy.ae_slice_memLp hU.measurableSet u.memL2
  have hgrad (i : Fin d) :=
    Energy.ae_slice_memLp hU.measurableSet (u.gradMemL2 i)
  filter_upwards [hvalue, ae_all_iff.2 hgrad, u.sliceWeakGradient] with t ht hg hw
  have ht' : MemLp (parSlice u.toFun t) 2 (volume.restrict U) := by
    have h := (memLp_indicator_iff_restrict hU.measurableSet).1 ht
    exact h
  have hg' (i : Fin d) :
      MemLp (fun x => parSlice u.grad t x i) 2 (volume.restrict U) := by
    have h := (memLp_indicator_iff_restrict hU.measurableSet).1 (hg i)
    exact h
  refine ⟨⟨parSlice u.toFun t, parSlice u.grad t, ?_, ?_, hw⟩, rfl, rfl⟩
  · simpa only [MemL2On, MemLpOn] using ht'
  · intro i
    simpa only [GradMemL2On, GradMemLpOn] using hg' i

/-- Almost every whole-space slice of `ParH1Function` satisfies the powered
spatial Gagliardo--Nirenberg estimate.  The constant depends only on the
dimension. -/
theorem ae_parH1_spatial_gagliardo_nirenberg
    (d : ℕ) (hd : 1 ≤ d) {I : Set ℝ}
    (u : ParH1Function (Set.univ : Set (Vec d)) I) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ᵐ t ∂(volume.restrict I),
        (eLpNorm (parSlice u.toFun t)
          (ENNReal.ofReal (2 * ((d : ℝ) + 2) / d)) volume) ^
            (2 * ((d : ℝ) + 2) / d) ≤
          C * (eLpNorm (parSlice u.toFun t) 2 volume) ^ (4 / (d : ℝ)) *
            (eLpNorm (fun x => vecEuclideanNorm (parSlice u.grad t x)) 2 volume) ^
              (2 : ℝ) := by
  obtain ⟨C, hC, hGN⟩ :=
    exists_spatial_gagliardo_nirenberg_energy_constant d hd
  refine ⟨C, hC, ?_⟩
  filter_upwards [ae_parH1_slice_h1 isOpen_univ u] with t ht
  obtain ⟨v, hv, hgrad⟩ := ht
  rw [← hv, ← hgrad]
  exact hGN v

/-- Local version for a parabolic function whose spatial slices vanish outside
a fixed compact subset of an open cylinder.  The values and gradient are
extended by zero from `U` to the whole space before applying the spatial
inequality; the displayed norms are therefore exactly the cylinder norms. -/
theorem ae_parH1_compactly_supported_spatial_gagliardo_nirenberg
    (d : ℕ) (hd : 1 ≤ d) {U : Set (Vec d)} {I : Set ℝ}
    (hU : IsOpen U) (u : ParH1Function U I)
    {K : Set (Vec d)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hsupp : ∀ᵐ t ∂(volume.restrict I),
      ∀ x ∈ U, x ∉ K → parSlice u.toFun t x = 0) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ᵐ t ∂(volume.restrict I),
        (eLpNorm (Set.indicator U (parSlice u.toFun t))
          (ENNReal.ofReal (2 * ((d : ℝ) + 2) / d)) volume) ^
            (2 * ((d : ℝ) + 2) / d) ≤
          C * (eLpNorm (Set.indicator U (parSlice u.toFun t)) 2 volume) ^
                (4 / (d : ℝ)) *
            (eLpNorm
              (fun x => vecEuclideanNorm (Set.indicator U (parSlice u.grad t) x))
              2 volume) ^ (2 : ℝ) := by
  obtain ⟨C, hC, hGN⟩ :=
    exists_spatial_gagliardo_nirenberg_energy_constant d hd
  refine ⟨C, hC, ?_⟩
  filter_upwards [ae_parH1_slice_h1 hU u, hsupp] with t ht hs
  obtain ⟨v, hv, hgrad⟩ := ht
  let v₀ : H1Function (Set.univ : Set (Vec d)) := {
    toFun := Set.indicator U v.toFun
    grad := Set.indicator U v.grad
    memL2 := by
      simpa only [MemL2On, MemLpOn, volumeOn, Measure.restrict_univ] using
        (memLp_indicator_iff_restrict (μ := volume) hU.measurableSet).2 v.memL2
    gradMemL2 := by
      intro i
      rw [show (fun x => Set.indicator U v.grad x i) =
        Set.indicator U (fun x => v.grad x i) by
          funext x
          by_cases hx : x ∈ U <;> simp [hx]]
      simpa only [GradMemL2On, GradMemLpOn, MemLpOn, volumeOn,
        Measure.restrict_univ] using
        (memLp_indicator_iff_restrict (μ := volume) hU.measurableSet).2
          (v.gradMemL2 i)
    hasWeakGradient := by
      intro i
      have hzero := Ch4Infra.hasWeakPartialDerivOn_univ_zeroExtend
        hU v hKU hK (fun x hxU hxK => by
          rw [hv]
          exact hs x hxU hxK) i
      convert hzero using 1
      funext x
      by_cases hx : x ∈ U <;> simp [hx]
  }
  have hbound := hGN v₀
  simpa [v₀, hv, hgrad] using hbound

/-- The spatial squared-gradient energy of `ParH1Function` slices is
almost-everywhere measurable in time.  The product `L²` hypotheses give the
required Fubini measurability; exceptional representatives at individual
times do not affect this conclusion. -/
theorem aemeasurable_parH1_slice_gradient_energy
    {d : ℕ} {U : Set (Vec d)} {I : Set ℝ}
    (hU : IsOpen U) (u : ParH1Function U I) :
    AEMeasurable
      (fun t =>
        (eLpNorm (fun x => vecEuclideanNorm (parSlice u.grad t x)) 2
          (volume.restrict U)) ^ (2 : ℝ))
      (volume.restrict I) := by
  let μ := (volume.restrict U).prod (volume.restrict I)
  have hgrad : AEMeasurable u.grad (volume.restrict (U ×ˢ I)) :=
    aemeasurable_pi_iff.2 fun i =>
      (u.gradMemL2 i).aestronglyMeasurable.aemeasurable
  have hgrad' : AEMeasurable u.grad μ := by
    simpa only [μ, Energy.volume_restrict_prod] using hgrad
  have hmag : AEMeasurable (fun z => vecEuclideanNorm (u.grad z)) μ :=
    continuous_vecEuclideanNorm.measurable.comp_aemeasurable hgrad'
  let G : Vec d × ℝ → ℝ≥0∞ :=
    fun z => ‖vecEuclideanNorm (u.grad z)‖ₑ ^ (2 : ℝ)
  have hG : AEMeasurable G μ := by
    exact hmag.enorm.pow_const (2 : ℝ)
  let Gslice : ℝ → ℝ≥0∞ := fun t =>
    ∫⁻ x, G (x, t) ∂(volume.restrict U)
  have hGslice : AEMeasurable Gslice (volume.restrict I) := by
    exact hG.lintegral_prod_left'
  have hEq : ∀ᵐ t ∂(volume.restrict I),
      (eLpNorm (fun x => vecEuclideanNorm (parSlice u.grad t x)) 2
        (volume.restrict U)) ^ (2 : ℝ) = Gslice t := by
    filter_upwards [ae_parH1_slice_h1 hU u] with t ht
    obtain ⟨v, hv, hgradv⟩ := ht
    have hmagMem : MemLp (fun x => vecEuclideanNorm (parSlice u.grad t x)) 2
        (volume.restrict U) := by
      rw [← hgradv]
      exact v.gradMemL2.memLp_vecEuclideanNorm
    have hsq := Energy.lintegral_enorm_sq_eq hmagMem.aestronglyMeasurable
    simpa [Gslice, G, parSlice] using hsq.symm
  apply hGslice.congr
  filter_upwards [hEq] with t ht
  exact ht.symm

/-- Integrate an almost-everywhere Gagliardo--Nirenberg inequality when the
energy slices are only almost-everywhere measurable, as is natural for
representative-level parabolic functions. -/
theorem lintegral_le_of_ae_gagliardo_nirenberg_aemeasurable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (d : ℕ) (hd : 1 ≤ d)
    (C S : ℝ≥0∞) {A B D : α → ℝ≥0∞}
    (hD : AEMeasurable D μ)
    (hB : ∀ᵐ t ∂μ, B t ≤ S)
    (hGN : ∀ᵐ t ∂μ,
      A t ≤ C * B t ^ (2 / (d : ℝ)) * D t) :
    ∫⁻ t, A t ∂μ ≤
      C * S ^ (2 / (d : ℝ)) * ∫⁻ t, D t ∂μ := by
  have hδ : 0 ≤ 2 / (d : ℝ) := by
    have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    positivity
  have hpoint : ∀ᵐ t ∂μ,
      A t ≤ (C * S ^ (2 / (d : ℝ))) * D t := by
    filter_upwards [hB, hGN] with t hBt hGNt
    calc
      A t ≤ C * B t ^ (2 / (d : ℝ)) * D t := hGNt
      _ ≤ (C * S ^ (2 / (d : ℝ))) * D t := by
        gcongr
  calc
    ∫⁻ t, A t ∂μ ≤
        ∫⁻ t, (C * S ^ (2 / (d : ℝ))) * D t ∂μ := lintegral_mono_ae hpoint
    _ = C * S ^ (2 / (d : ℝ)) * ∫⁻ t, D t ∂μ :=
      lintegral_const_mul'' _ hD

/-- Whole-space parabolic Gagliardo--Nirenberg inequality for `ParH1Function`.
The `L∞(L²)` hypothesis is the essential bound `S` on the squared spatial
`L²` norm; `hD` records measurability of the spatial gradient energy. -/
theorem parH1_time_integrated_gagliardo_nirenberg
    (d : ℕ) (hd : 1 ≤ d) {I : Set ℝ}
    (u : ParH1Function (Set.univ : Set (Vec d)) I)
    (S : ℝ≥0∞)
    (hS : ∀ᵐ t ∂(volume.restrict I),
      (eLpNorm (parSlice u.toFun t) 2 volume) ^ (2 : ℝ) ≤ S)
    :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∫⁻ t,
          (eLpNorm (parSlice u.toFun t)
            (ENNReal.ofReal (2 * ((d : ℝ) + 2) / d)) volume) ^
              (2 * ((d : ℝ) + 2) / d) ∂(volume.restrict I) ≤
        C * S ^ (2 / (d : ℝ)) *
          ∫⁻ t,
            (eLpNorm
              (fun x => vecEuclideanNorm (parSlice u.grad t x)) 2 volume) ^
                (2 : ℝ) ∂(volume.restrict I) := by
  obtain ⟨C, hC, hspatial⟩ :=
    ae_parH1_spatial_gagliardo_nirenberg d hd u
  let A : ℝ → ℝ≥0∞ := fun t =>
    (eLpNorm (parSlice u.toFun t)
      (ENNReal.ofReal (2 * ((d : ℝ) + 2) / d)) volume) ^
        (2 * ((d : ℝ) + 2) / d)
  let B : ℝ → ℝ≥0∞ := fun t =>
    (eLpNorm (parSlice u.toFun t) 2 volume) ^ (2 : ℝ)
  let D : ℝ → ℝ≥0∞ := fun t =>
    (eLpNorm (fun x => vecEuclideanNorm (parSlice u.grad t x)) 2 volume) ^
      (2 : ℝ)
  have hD : AEMeasurable D (volume.restrict I) := by
    simpa only [D, Measure.restrict_univ] using
      aemeasurable_parH1_slice_gradient_energy isOpen_univ u
  have hGN : ∀ᵐ t ∂(volume.restrict I),
      A t ≤ C * B t ^ (2 / (d : ℝ)) * D t := by
    filter_upwards [hspatial] with t ht
    have hBpow :
        (eLpNorm (parSlice u.toFun t) 2 volume) ^ (4 / (d : ℝ)) =
          B t ^ (2 / (d : ℝ)) := by
      dsimp [B]
      rw [show (4 / (d : ℝ)) = (2 : ℝ) * (2 / (d : ℝ)) by
        have hdne : (d : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt (by omega : 0 < d))
        field_simp
        ring]
      rw [ENNReal.rpow_mul]
    rw [← hBpow]
    simpa only [A, B, D, ENNReal.rpow_natCast] using ht
  refine ⟨C, hC, ?_⟩
  simpa only [A, B, D] using
    lintegral_le_of_ae_gagliardo_nirenberg_aemeasurable
      (volume.restrict I) d hd C S hD hS hGN

/-- Local parabolic Gagliardo--Nirenberg inequality for compactly supported
spatial slices of `ParH1Function`.  All norms are whole-space norms of the
literal zero extensions from `U`, and hence are exactly the cylinder norms.
This is the form used after applying a spatial cutoff in the weak Harnack
power iteration. -/
theorem parH1_compactly_supported_time_integrated_gagliardo_nirenberg
    (d : ℕ) (hd : 1 ≤ d) {U : Set (Vec d)} {I : Set ℝ}
    (hU : IsOpen U) (u : ParH1Function U I)
    {K : Set (Vec d)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hsupp : ∀ᵐ t ∂(volume.restrict I),
      ∀ x ∈ U, x ∉ K → parSlice u.toFun t x = 0)
    (S : ℝ≥0∞)
    (hS : ∀ᵐ t ∂(volume.restrict I),
      (eLpNorm (parSlice u.toFun t) 2 (volume.restrict U)) ^
        (2 : ℝ) ≤ S) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∫⁻ t,
          (eLpNorm (parSlice u.toFun t)
            (ENNReal.ofReal (2 * ((d : ℝ) + 2) / d)) (volume.restrict U)) ^
              (2 * ((d : ℝ) + 2) / d) ∂(volume.restrict I) ≤
        C * S ^ (2 / (d : ℝ)) *
          ∫⁻ t,
            (eLpNorm
              (fun x => vecEuclideanNorm (parSlice u.grad t x))
              2 (volume.restrict U)) ^ (2 : ℝ) ∂(volume.restrict I) := by
  obtain ⟨C, hC, hspatial⟩ :=
    ae_parH1_compactly_supported_spatial_gagliardo_nirenberg
      d hd hU u hK hKU hsupp
  let A : ℝ → ℝ≥0∞ := fun t =>
    (eLpNorm (parSlice u.toFun t)
      (ENNReal.ofReal (2 * ((d : ℝ) + 2) / d)) (volume.restrict U)) ^
        (2 * ((d : ℝ) + 2) / d)
  let B : ℝ → ℝ≥0∞ := fun t =>
    (eLpNorm (parSlice u.toFun t) 2 (volume.restrict U)) ^ (2 : ℝ)
  let D : ℝ → ℝ≥0∞ := fun t =>
    (eLpNorm (fun x => vecEuclideanNorm (parSlice u.grad t x))
      2 (volume.restrict U)) ^ (2 : ℝ)
  have hD : AEMeasurable D (volume.restrict I) :=
    aemeasurable_parH1_slice_gradient_energy hU u
  have hGN : ∀ᵐ t ∂(volume.restrict I),
      A t ≤ C * B t ^ (2 / (d : ℝ)) * D t := by
    filter_upwards [hspatial] with t ht
    have hgradIndicator :
        (fun x => vecEuclideanNorm (Set.indicator U (parSlice u.grad t) x)) =
          Set.indicator U (fun x => vecEuclideanNorm (parSlice u.grad t x)) := by
      funext x
      by_cases hx : x ∈ U <;>
        simp [Set.indicator, hx, PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot]
    rw [hgradIndicator] at ht
    simp only [eLpNorm_indicator_eq_eLpNorm_restrict hU.measurableSet] at ht
    have hBpow :
        (eLpNorm (parSlice u.toFun t) 2 (volume.restrict U)) ^
            (4 / (d : ℝ)) = B t ^ (2 / (d : ℝ)) := by
      dsimp [B]
      rw [show (4 / (d : ℝ)) = (2 : ℝ) * (2 / (d : ℝ)) by
        have hdne : (d : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt (by omega : 0 < d))
        field_simp
        ring]
      rw [ENNReal.rpow_mul]
    rw [← hBpow]
    simpa only [A, B, D, ENNReal.rpow_natCast] using ht
  refine ⟨C, hC, ?_⟩
  simpa only [A, B, D] using
    lintegral_le_of_ae_gagliardo_nirenberg_aemeasurable
      (volume.restrict I) d hd C S hD hS hGN

/-- The whole-space `ParH1Function` estimate written directly as the
space-time integral inequality used in the Nash upper proof. -/
theorem parH1_time_integrated_lintegral_gagliardo_nirenberg
    (d : ℕ) (hd : 1 ≤ d) {I : Set ℝ}
    (u : ParH1Function (Set.univ : Set (Vec d)) I)
    (S : ℝ≥0∞)
    (hS : ∀ᵐ t ∂(volume.restrict I),
      (eLpNorm (parSlice u.toFun t) 2 volume) ^ (2 : ℝ) ≤ S) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∫⁻ t, ∫⁻ x, ‖parSlice u.toFun t x‖ₑ ^
          (2 * ((d : ℝ) + 2) / d) ∂volume ∂(volume.restrict I) ≤
        C * S ^ (2 / (d : ℝ)) *
          ∫⁻ t, ∫⁻ x,
            ‖vecEuclideanNorm (parSlice u.grad t x)‖ₑ ^ (2 : ℝ)
              ∂volume ∂(volume.restrict I) := by
  obtain ⟨C, hC, hmain⟩ := parH1_time_integrated_gagliardo_nirenberg d hd u S hS
  let q : ℝ := 2 * ((d : ℝ) + 2) / d
  have hq : 0 < q := by
    dsimp [q]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    positivity
  have hValue : ∀ᵐ t ∂(volume.restrict I),
      (eLpNorm (parSlice u.toFun t) (ENNReal.ofReal q) volume) ^ q =
        ∫⁻ x, ‖parSlice u.toFun t x‖ₑ ^ q ∂volume := by
    filter_upwards [ae_parH1_slice_h1 isOpen_univ u] with t ht
    obtain ⟨v, hv, _⟩ := ht
    have hsm : AEStronglyMeasurable (parSlice u.toFun t) volume := by
      rw [← hv]
      simpa only [MemL2On, MemLpOn, volumeOn, Measure.restrict_univ] using
        v.memL2.aestronglyMeasurable
    exact eLpNorm_rpow_eq_lintegral_enorm_rpow q hq hsm
  have hGrad : ∀ᵐ t ∂(volume.restrict I),
      (eLpNorm (fun x => vecEuclideanNorm (parSlice u.grad t x)) 2 volume) ^
          (2 : ℝ) =
        ∫⁻ x,
          ‖vecEuclideanNorm (parSlice u.grad t x)‖ₑ ^ (2 : ℝ) ∂volume := by
    filter_upwards [ae_parH1_slice_h1 isOpen_univ u] with t ht
    obtain ⟨v, _, hgrad⟩ := ht
    have hmem : MemLp (fun x => vecEuclideanNorm (parSlice u.grad t x)) 2 volume := by
      rw [← hgrad]
      simpa only [GradMemL2On, GradMemLpOn, MemLpOn, volumeOn,
        Measure.restrict_univ] using v.gradMemL2.memLp_vecEuclideanNorm
    simpa only [ENNReal.ofReal_ofNat] using
      eLpNorm_rpow_eq_lintegral_enorm_rpow 2 (by norm_num)
        hmem.aestronglyMeasurable
  have hLeft :
      (∫⁻ t, ∫⁻ x, ‖parSlice u.toFun t x‖ₑ ^ q ∂volume
          ∂(volume.restrict I)) =
        ∫⁻ t, (eLpNorm (parSlice u.toFun t) (ENNReal.ofReal q) volume) ^ q
          ∂(volume.restrict I) := by
    apply lintegral_congr_ae
    filter_upwards [hValue] with t ht
    exact ht.symm
  have hRight :
      (∫⁻ t, (eLpNorm
          (fun x => vecEuclideanNorm (parSlice u.grad t x)) 2 volume) ^
            (2 : ℝ) ∂(volume.restrict I)) =
        ∫⁻ t, ∫⁻ x,
          ‖vecEuclideanNorm (parSlice u.grad t x)‖ₑ ^ (2 : ℝ) ∂volume
            ∂(volume.restrict I) := by
    apply lintegral_congr_ae
    exact hGrad
  refine ⟨C, hC, ?_⟩
  have hmain' := hmain
  simpa only [q] using
    calc
      ∫⁻ t, ∫⁻ x, ‖parSlice u.toFun t x‖ₑ ^ q ∂volume
          ∂(volume.restrict I) =
          ∫⁻ t, (eLpNorm (parSlice u.toFun t) (ENNReal.ofReal q) volume) ^ q
            ∂(volume.restrict I) := hLeft
      _ ≤ C * S ^ (2 / (d : ℝ)) *
            ∫⁻ t, (eLpNorm
              (fun x => vecEuclideanNorm (parSlice u.grad t x)) 2 volume) ^
                (2 : ℝ) ∂(volume.restrict I) := hmain'
      _ = C * S ^ (2 / (d : ℝ)) *
            ∫⁻ t, ∫⁻ x,
              ‖vecEuclideanNorm (parSlice u.grad t x)‖ₑ ^ (2 : ℝ)
                ∂volume ∂(volume.restrict I) := by rw [hRight]

/-- The compactly supported local estimate written directly as the
space-time integral inequality used after a spatial cutoff in weak Harnack. -/
theorem parH1_compactly_supported_time_integrated_lintegral_gagliardo_nirenberg
    (d : ℕ) (hd : 1 ≤ d) {U : Set (Vec d)} {I : Set ℝ}
    (hU : IsOpen U) (u : ParH1Function U I)
    {K : Set (Vec d)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hsupp : ∀ᵐ t ∂(volume.restrict I),
      ∀ x ∈ U, x ∉ K → parSlice u.toFun t x = 0)
    (S : ℝ≥0∞)
    (hS : ∀ᵐ t ∂(volume.restrict I),
      (eLpNorm (parSlice u.toFun t) 2 (volume.restrict U)) ^
        (2 : ℝ) ≤ S) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∫⁻ t, ∫⁻ x, ‖parSlice u.toFun t x‖ₑ ^
          (2 * ((d : ℝ) + 2) / d) ∂(volume.restrict U)
            ∂(volume.restrict I) ≤
        C * S ^ (2 / (d : ℝ)) *
          ∫⁻ t, ∫⁻ x,
            ‖vecEuclideanNorm (parSlice u.grad t x)‖ₑ ^ (2 : ℝ)
              ∂(volume.restrict U) ∂(volume.restrict I) := by
  obtain ⟨C, hC, hmain⟩ :=
    parH1_compactly_supported_time_integrated_gagliardo_nirenberg
      d hd hU u hK hKU hsupp S hS
  let q : ℝ := 2 * ((d : ℝ) + 2) / d
  have hq : 0 < q := by
    dsimp [q]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    positivity
  have hValue : ∀ᵐ t ∂(volume.restrict I),
      (eLpNorm (parSlice u.toFun t) (ENNReal.ofReal q)
        (volume.restrict U)) ^ q =
        ∫⁻ x, ‖parSlice u.toFun t x‖ₑ ^ q ∂(volume.restrict U) := by
    filter_upwards [ae_parH1_slice_h1 hU u] with t ht
    obtain ⟨v, hv, _⟩ := ht
    have hsm : AEStronglyMeasurable (parSlice u.toFun t) (volume.restrict U) := by
      rw [← hv]
      exact v.memL2.aestronglyMeasurable
    exact eLpNorm_rpow_eq_lintegral_enorm_rpow q hq hsm
  have hGrad : ∀ᵐ t ∂(volume.restrict I),
      (eLpNorm (fun x => vecEuclideanNorm (parSlice u.grad t x)) 2
        (volume.restrict U)) ^ (2 : ℝ) =
        ∫⁻ x,
          ‖vecEuclideanNorm (parSlice u.grad t x)‖ₑ ^ (2 : ℝ)
            ∂(volume.restrict U) := by
    filter_upwards [ae_parH1_slice_h1 hU u] with t ht
    obtain ⟨v, _, hgrad⟩ := ht
    have hmem : MemLp (fun x => vecEuclideanNorm (parSlice u.grad t x)) 2
        (volume.restrict U) := by
      rw [← hgrad]
      exact v.gradMemL2.memLp_vecEuclideanNorm
    simpa only [ENNReal.ofReal_ofNat] using
      eLpNorm_rpow_eq_lintegral_enorm_rpow 2 (by norm_num)
        hmem.aestronglyMeasurable
  have hLeft :
      (∫⁻ t, ∫⁻ x, ‖parSlice u.toFun t x‖ₑ ^ q
          ∂(volume.restrict U) ∂(volume.restrict I)) =
        ∫⁻ t, (eLpNorm (parSlice u.toFun t) (ENNReal.ofReal q)
          (volume.restrict U)) ^ q ∂(volume.restrict I) := by
    apply lintegral_congr_ae
    filter_upwards [hValue] with t ht
    exact ht.symm
  have hRight :
      (∫⁻ t, (eLpNorm
          (fun x => vecEuclideanNorm (parSlice u.grad t x))
          2 (volume.restrict U)) ^ (2 : ℝ) ∂(volume.restrict I)) =
        ∫⁻ t, ∫⁻ x,
          ‖vecEuclideanNorm (parSlice u.grad t x)‖ₑ ^ (2 : ℝ)
            ∂(volume.restrict U) ∂(volume.restrict I) := by
    apply lintegral_congr_ae
    exact hGrad
  refine ⟨C, hC, ?_⟩
  simpa only [q] using
    calc
      ∫⁻ t, ∫⁻ x, ‖parSlice u.toFun t x‖ₑ ^ q
          ∂(volume.restrict U) ∂(volume.restrict I) =
        ∫⁻ t, (eLpNorm (parSlice u.toFun t) (ENNReal.ofReal q)
          (volume.restrict U)) ^ q ∂(volume.restrict I) := hLeft
      _ ≤ C * S ^ (2 / (d : ℝ)) *
            ∫⁻ t, (eLpNorm
              (fun x => vecEuclideanNorm (parSlice u.grad t x))
              2 (volume.restrict U)) ^ (2 : ℝ) ∂(volume.restrict I) := hmain
      _ = C * S ^ (2 / (d : ℝ)) *
            ∫⁻ t, ∫⁻ x,
              ‖vecEuclideanNorm (parSlice u.grad t x)‖ₑ ^ (2 : ℝ)
                ∂(volume.restrict U) ∂(volume.restrict I) := by rw [hRight]

end PDE.Parabolic
