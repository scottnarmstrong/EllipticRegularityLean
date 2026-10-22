module

public import EllipticRegularity.Parabolic.Cauchy.Lions.JointRepresentative
public import EllipticRegularity.Parabolic.Energy.Slab

/-! # Global space-time bounds for spatial mollifications -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.Lions

/-- Spatial mollification is an `L²` contraction on the whole Cauchy slab. The proof applies
the whole-space contraction on almost every time slice and integrates the resulting inequality. -/
theorem cauchyMollT_memLp {d : ℕ} {s T a : ℝ} {F : Vec d × ℝ → ℝ}
    (ha : 0 < a) (hF : MemLp F 2 (slabMeasure d s T)) :
    MemLp (PDE.Parabolic.Energy.mollT a univ F) 2 (slabMeasure d s T) ∧
      eLpNorm (PDE.Parabolic.Energy.mollT a univ F) 2 (slabMeasure d s T) ≤
        eLpNorm F 2 (slabMeasure d s T) := by
  let μx : Measure (Vec d) := volume
  let μt : Measure ℝ := volume.restrict (Icc s T)
  have hprod : μx.prod μt = slabMeasure d s T := by
    change (volume : Measure (Vec d)).prod (volume.restrict (Icc s T)) = _
    calc
      (volume : Measure (Vec d)).prod (volume.restrict (Icc s T)) =
          (volume.restrict (univ : Set (Vec d))).prod (volume.restrict (Icc s T)) := by simp
      _ = (volume : Measure (Vec d × ℝ)).restrict (univ ×ˢ Icc s T) :=
        (PDE.Parabolic.Energy.volume_restrict_prod univ (Icc s T)).symm
      _ = slabMeasure d s T := rfl
  have hprodRest : μx.prod μt =
      (volume : Measure (Vec d × ℝ)).restrict (univ ×ˢ Icc s T) := by
    change (volume : Measure (Vec d)).prod (volume.restrict (Icc s T)) = _
    calc
      (volume : Measure (Vec d)).prod (volume.restrict (Icc s T)) =
          (volume.restrict (univ : Set (Vec d))).prod (volume.restrict (Icc s T)) := by simp
      _ = (volume : Measure (Vec d × ℝ)).restrict (univ ×ˢ Icc s T) :=
        (PDE.Parabolic.Energy.volume_restrict_prod univ (Icc s T)).symm
  have hFp : MemLp F 2 (μx.prod μt) := by
    rw [hprod]
    exact hF
  have hFrest : MemLp F 2
      ((volume : Measure (Vec d × ℝ)).restrict (univ ×ˢ Icc s T)) := by
    rw [← hprodRest]
    exact hFp
  have hFm := hFp.aestronglyMeasurable
  have hMoll : AEStronglyMeasurable (PDE.Parabolic.Energy.mollT a univ F)
      (μx.prod μt) := by
    rw [hprodRest]
    exact PDE.Parabolic.Energy.aestronglyMeasurable_mollT MeasurableSet.univ
      univ hFrest.aestronglyMeasurable a
  have hFslice := PDE.Parabolic.Energy.ae_slice_memLp MeasurableSet.univ hFrest
  have hsq : ∫⁻ z, ‖PDE.Parabolic.Energy.mollT a univ F z‖ₑ ^ (2 : ℝ)
        ∂(μx.prod μt) ≤
      ∫⁻ z, ‖F z‖ₑ ^ (2 : ℝ) ∂(μx.prod μt) := by
    rw [lintegral_prod_symm _ (hMoll.aemeasurable.enorm.pow_const _),
      lintegral_prod_symm _ (hFm.aemeasurable.enorm.pow_const _)]
    apply lintegral_mono_ae
    filter_upwards [hFslice] with t ht
    have hm := PDE.Parabolic.Energy.eLpNorm_moll_le ha ht
    have hleft : ∫⁻ x, ‖PDE.Parabolic.Energy.mollT a univ F (x, t)‖ₑ ^ (2 : ℝ)
          ∂μx = eLpNorm (PDE.wholeSpaceMollify a (univ.indicator fun y => F (y, t)))
            2 volume ^ (2 : ℝ) := by
      have heq : (fun x : Vec d => PDE.Parabolic.Energy.mollT a univ F (x, t)) =
          PDE.wholeSpaceMollify a (univ.indicator fun y => F (y, t)) := by
        funext x
        rfl
      calc
        ∫⁻ x, ‖PDE.Parabolic.Energy.mollT a univ F (x, t)‖ₑ ^ (2 : ℝ) ∂μx =
            ∫⁻ x, ‖PDE.wholeSpaceMollify a (univ.indicator fun y => F (y, t)) x‖ₑ ^
              (2 : ℝ) ∂μx := by
                apply lintegral_congr_ae
                filter_upwards [] with x
                exact congrArg (fun q : ℝ => ‖q‖ₑ ^ (2 : ℝ)) (congrFun heq x)
        _ = eLpNorm (PDE.wholeSpaceMollify a
            (univ.indicator fun y => F (y, t))) 2 volume ^ (2 : ℝ) := by
              exact PDE.Parabolic.Energy.lintegral_enorm_sq_eq hm.1.aestronglyMeasurable
    have hslice : MemLp (fun y : Vec d => F (y, t)) 2 volume := by
      simpa using ht
    have hright : ∫⁻ x, ‖F (x, t)‖ₑ ^ (2 : ℝ) ∂μx =
        eLpNorm (fun y : Vec d => F (y, t)) 2 volume ^ (2 : ℝ) := by
      rw [PDE.Parabolic.Energy.lintegral_enorm_sq_eq hslice.aestronglyMeasurable]
    rw [hleft, hright]
    have hindicator : (univ.indicator fun y : Vec d => F (y, t)) = fun y => F (y, t) := by
      funext y
      simp
    exact ENNReal.rpow_le_rpow (by simpa only [hindicator] using hm.2)
      (show 0 ≤ (2 : ℝ) by norm_num)
  have hMollS : AEStronglyMeasurable (PDE.Parabolic.Energy.mollT a univ F)
      (slabMeasure d s T) := by
    rw [← hprod]
    exact hMoll
  have hsqS : ∫⁻ z, ‖PDE.Parabolic.Energy.mollT a univ F z‖ₑ ^ (2 : ℝ)
        ∂(slabMeasure d s T) ≤
      ∫⁻ z, ‖F z‖ₑ ^ (2 : ℝ) ∂(slabMeasure d s T) := by
    rw [hprod] at hsq
    exact hsq
  have hmem : MemLp (PDE.Parabolic.Energy.mollT a univ F) 2 (slabMeasure d s T) := by
    rw [memLp_iff,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hMollS]
    simp only [ENNReal.toReal_ofNat]
    refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
    refine ne_of_lt (lt_of_le_of_lt hsqS ?_)
    rw [PDE.Parabolic.Energy.lintegral_enorm_sq_eq hF.aestronglyMeasurable]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hF.eLpNorm_lt_top.ne
  have hnorm : eLpNorm (PDE.Parabolic.Energy.mollT a univ F) 2 (slabMeasure d s T) ≤
      eLpNorm F 2 (slabMeasure d s T) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hMollS,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        hF.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat]
    exact ENNReal.rpow_le_rpow hsqS (by norm_num)
  exact ⟨hmem, hnorm⟩

/-- The value, spatial-gradient, and coefficient-flux fields mollified in space retain global
space-time `L²` bounds. The gradient and flux components are stated coordinatewise to match the
native `Vec d` representation. -/
theorem cauchyMollifiedEnergyFields_memLp {d : ℕ} {lam Lam s T ε : ℝ}
    {A : ParCoeffField d} (ha : IsParabolicCoeff lam Lam A univ (Icc s T))
    (hε : 0 < ε) (u : CauchyX d s T) :
    MemLp (PDE.Parabolic.Energy.mollT ε univ (cauchyEnergyValue u)) 2
        (slabMeasure d s T) ∧
      (∀ i : Fin d, MemLp
        (PDE.Parabolic.Energy.mollT ε univ
          (fun z => cauchyEnergyGradient u z i)) 2 (slabMeasure d s T)) ∧
      (∀ i : Fin d, MemLp
        (PDE.Parabolic.Energy.mollT ε univ
          (fun z => matVecMul (A z) (cauchyEnergyGradient u z) i)) 2
        (slabMeasure d s T)) := by
  refine ⟨(cauchyMollT_memLp hε (cauchyEnergyValue_memLp u)).1, ?_, ?_⟩
  · intro i
    exact (cauchyMollT_memLp hε (cauchyEnergyGradient_coord_memLp u i)).1
  · intro i
    exact (cauchyMollT_memLp hε (cauchyEnergyFlux_coord_memLp ha u i)).1

end PDE.Parabolic.Lions
