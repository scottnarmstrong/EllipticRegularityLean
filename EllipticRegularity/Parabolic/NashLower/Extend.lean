module

public import EllipticRegularity.Parabolic.NashLower.Restrict
public import EllipticRegularity.Parabolic.Energy.Limits

/-!
# Forward extension of the coefficient field and joint positivity

The Cauchy solution of the Nash-Aronson lower bound lives only on `[s,t]`, while the local Harnack
chain needs the solution slightly past the final time `t`.  Following the adapted manuscript
argument, the coefficients are extended by the identity matrix for times `> t`, a Cauchy solution on a
longer interval is produced, and uniqueness identifies its restriction with the given solution.
This file contains the coefficient extension and the passage from slice positivity to joint
a.e. positivity.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.Parabolic.NashLower

/-- Extension of a coefficient field by the identity matrix for times `> t`. -/
noncomputable def extCoeff {d : ℕ} (a : ParCoeffField d) (t : ℝ) : ParCoeffField d :=
  fun z => if z.2 ≤ t then a z else 1

theorem isEllipticMatrix_one {d : ℕ} {Lam : ℝ} (hLam : 1 ≤ Lam) :
    IsEllipticMatrix 1 Lam (1 : Mat d) := by
  have hmv : ∀ ξ : Vec d, matVecMul (1 : Mat d) ξ = ξ := by
    intro ξ; funext i
    simp [matVecMul, Matrix.one_apply]
  refine ⟨one_pos, hLam, ?_, ?_⟩
  · intro ξ
    rw [hmv]
    exact le_of_eq (by rw [one_mul]; rfl)
  · intro ξ
    rw [inv_one, hmv]
    have hn : 0 ≤ vecNormSq ξ := vecNormSq_nonneg ξ
    have hinv : Lam⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hLam
    calc Lam⁻¹ * vecNormSq ξ ≤ 1 * vecNormSq ξ := mul_le_mul_of_nonneg_right hinv hn
      _ = vecDot ξ ξ := by rw [one_mul]; rfl

/-- The extended coefficient field satisfies the parabolic hypotheses on the longer interval. -/
theorem isParabolicCoeff_ext {d : ℕ} {Lam : ℝ} (hLam : 1 ≤ Lam) {a : ParCoeffField d}
    {s t T : ℝ} (ha : IsParabolicCoeff 1 Lam a univ (Icc s t)) :
    IsParabolicCoeff 1 Lam (extCoeff a t) univ (Icc s T) := by
  have hS : MeasurableSet {z : Vec d × ℝ | z.2 ≤ t} := measurableSet_le measurable_snd measurable_const
  have hmT : MeasurableSet ((univ : Set (Vec d)) ×ˢ Icc s T) := MeasurableSet.univ.prod measurableSet_Icc
  refine ⟨fun i j => ?_, ?_⟩
  · have hpw : (fun z => extCoeff a t z i j) =
        Set.piecewise {z : Vec d × ℝ | z.2 ≤ t} (fun z => a z i j) (fun _ => (1 : Mat d) i j) := by
      funext z
      by_cases hz : z.2 ≤ t <;> simp [extCoeff, Set.piecewise, hz]
    rw [hpw]
    have hsub : {z : Vec d × ℝ | z.2 ≤ t} ∩ ((univ : Set (Vec d)) ×ˢ Icc s T) ⊆
        (univ : Set (Vec d)) ×ˢ Icc s t := by
      intro z hz
      exact ⟨mem_univ _, hz.2.2.1, hz.1⟩
    have hmain : AEMeasurable (fun z => a z i j)
        ((volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s T)).restrict
          {z : Vec d × ℝ | z.2 ≤ t}) := by
      rw [Measure.restrict_restrict hS]
      exact (ha.measurable i j).mono_measure (Measure.restrict_mono hsub le_rfl)
    have hcov : AEMeasurable (Set.piecewise {z : Vec d × ℝ | z.2 ≤ t} (fun z => a z i j)
        (fun _ => (1 : Mat d) i j))
        ((volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s T)).restrict
          ({z : Vec d × ℝ | z.2 ≤ t} ∪ {z : Vec d × ℝ | z.2 ≤ t}ᶜ)) := by
      refine aemeasurable_union_iff.2 ⟨?_, ?_⟩
      · refine AEMeasurable.congr ?_ (piecewise_ae_eq_restrict hS).symm
        exact hmain
      · refine AEMeasurable.congr ?_ (piecewise_ae_eq_restrict_compl hS).symm
        exact aemeasurable_const
    rwa [union_compl_self, Measure.restrict_univ] at hcov
  · have hmt : MeasurableSet ((univ : Set (Vec d)) ×ˢ Icc s t) := MeasurableSet.univ.prod measurableSet_Icc
    have h1 := (ae_restrict_iff' hmt).1 ha.elliptic
    have h2 := ae_restrict_of_ae (s := (univ : Set (Vec d)) ×ˢ Icc s T) h1
    filter_upwards [h2, ae_restrict_mem hmT] with z hz hzT
    by_cases hzt : z.2 ≤ t
    · have hzmem : z ∈ (univ : Set (Vec d)) ×ˢ Icc s t := ⟨mem_univ _, hzT.2.1, hzt⟩
      simpa [extCoeff, hzt] using hz hzmem
    · simpa [extCoeff, hzt] using isEllipticMatrix_one (d := d) hLam

/-- A weak solution for the extended coefficients restricts to a weak solution for `a`. -/
theorem isParabolicWeakSolution_of_ext {d : ℕ} {a : ParCoeffField d} {s t T : ℝ} (htT : t ≤ T)
    {w : ParH1Function (univ : Set (Vec d)) (Icc s T)}
    (hw : IsParabolicWeakSolution (extCoeff a t) univ (Icc s T) w) :
    IsParabolicWeakSolution a univ (Icc s t)
      (restrictParH1 (subset_refl _) (Icc_subset_Icc_right htT) w) := by
  have h := isParabolicWeakSolution_restrict (subset_refl _) (Icc_subset_Icc_right htT) hw
  intro φ
  obtain ⟨hint, hz⟩ := h φ
  have hm : MeasurableSet ((univ : Set (Vec d)) ×ˢ Icc s t) := MeasurableSet.univ.prod measurableSet_Icc
  have hfeq : EqOn (parWeakIntegrand (extCoeff a t) (restrictParH1 (subset_refl _)
      (Icc_subset_Icc_right htT) w) φ.toFun)
      (parWeakIntegrand a (restrictParH1 (subset_refl _) (Icc_subset_Icc_right htT) w) φ.toFun)
      ((univ : Set (Vec d)) ×ˢ Icc s t) := by
    intro z hzmem
    have hzt : z.2 ≤ t := hzmem.2.2
    simp [parWeakIntegrand, extCoeff, hzt]
  exact ⟨hint.congr_fun hfeq hm, by rw [← setIntegral_congr_fun hm hfeq]; exact hz⟩

/-- A Cauchy solution for the extended coefficients restricts to one for `a`. -/
theorem isCauchySolution_of_ext {d : ℕ} {a : ParCoeffField d} {s t T : ℝ} (htT : t ≤ T)
    {f : Vec d → ℝ} {w : ParH1Function (univ : Set (Vec d)) (Icc s T)}
    (hw : IsCauchySolution (extCoeff a t) s T f w) :
    IsCauchySolution a s t f (restrictParH1 (subset_refl _) (Icc_subset_Icc_right htT) w) :=
  ⟨isParabolicWeakSolution_of_ext htT hw.1, hw.2⟩

/-- Slice-wise a.e. nonnegativity gives joint a.e. nonnegativity on a product with measurable
time factor. -/
theorem ae_nonneg_of_ae_slices {d : ℕ} {B : Set (Vec d)} {J : Set ℝ} (hJ : MeasurableSet J)
    {F : Vec d × ℝ → ℝ} (hF : AEStronglyMeasurable F (volume.restrict (B ×ˢ J)))
    (hpos : ∀ τ ∈ J, ∀ᵐ x : Vec d, 0 ≤ F (x, τ)) :
    ∀ᵐ z ∂(volume.restrict (B ×ˢ J)), 0 ≤ F z := by
  have hprod : (volume : Measure (Vec d × ℝ)).restrict (B ×ˢ J) =
      (volume.restrict B).prod (volume.restrict J) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  rw [hprod] at hF ⊢
  set g := hF.mk F with hg
  have hFg : F =ᵐ[(volume.restrict B).prod (volume.restrict J)] g := hF.ae_eq_mk
  have hmeas : MeasurableSet {z : Vec d × ℝ | 0 ≤ g z} :=
    measurableSet_le measurable_const hF.stronglyMeasurable_mk.measurable
  have hslice : ∀ᵐ τ ∂(volume.restrict J), ∀ᵐ x ∂(volume.restrict B), 0 ≤ g (x, τ) := by
    have h1 := PDE.Parabolic.Energy.ae_ae_swap hFg
    filter_upwards [h1, ae_restrict_mem hJ] with τ hτ hτJ
    have h2 := hpos τ hτJ
    filter_upwards [hτ, ae_restrict_of_ae h2] with x hx hx2
    rw [← hx]; exact hx2
  have hswap : ∀ᵐ w ∂(volume.restrict J).prod (volume.restrict B), 0 ≤ g w.swap :=
    (Measure.ae_prod_iff_ae_ae (p := fun w : ℝ × Vec d => 0 ≤ g w.swap)
      (hmeas.preimage measurable_swap)).2 hslice
  have hg0 : ∀ᵐ z ∂(volume.restrict B).prod (volume.restrict J), 0 ≤ g z := by
    have := (Measure.measurePreserving_swap (μ := volume.restrict B)
      (ν := volume.restrict J)).quasiMeasurePreserving.ae hswap
    simpa using this
  filter_upwards [hFg, hg0] with z h1 h2
  rw [h1]; exact h2

end PDE.Parabolic.NashLower
