module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.Lions.MollifiedBallEstimate

/-! # Uniform global slice bounds for fixed-scale mollifications -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.Lions

theorem cauchy_mollified_cutoff_ball_bound
    {d : ℕ} {lam Lam s T ε : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (hε : 0 < ε) (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : CauchyX d s T) {u₀ : CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    {w : Vec d × ℝ → ℝ}
    (hwcont : ∀ x, ContinuousOn (fun τ => w (x, τ)) (Icc s T))
    (hwsec : ∀ x, (fun τ => PDE.Parabolic.Energy.mollT ε univ
      (cauchyEnergyValue u) (x, τ)) =ᵐ[volume.restrict (Icc s T)]
        (fun τ => w (x, τ)))
    {t : ℝ} (hst : s < t) (htT : t ≤ T) (n : ℕ) :
    (∫ x in euclideanClosedBall (0 : Vec d) ((n : ℝ) + 1), w (x, t) ^ 2) ≤
      (eLpNorm f 2 volume).toReal ^ 2 +
        2 * ∑ i : Fin d,
          ((eLpNorm (fun z => matVecMul (a z) (cauchyEnergyGradient u z) i)
              2 (slabMeasure d s T)).toReal *
              (eLpNorm (fun z => cauchyEnergyGradient u z i)
                2 (slabMeasure d s T)).toReal +
            64 * (eLpNorm (fun z => matVecMul (a z)
              (cauchyEnergyGradient u z) i) 2 (slabMeasure d s T)).toReal *
              (eLpNorm (cauchyEnergyValue u) 2 (slabMeasure d s T)).toReal) := by
  let R : ℝ := (n : ℝ) + 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hRone : 1 ≤ R := by dsimp [R]; have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _; linarith
  obtain ⟨E, hEs, hEt, _hδ, hEK, hEφ, hEu, hEDu, hEG, hEcont, hEsec,
    hEinit⟩ := exists_cauchy_mollified_energyData hsT ha hε f hf u hclose hrep
      hst htT hR
  let χ := PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff (d := d) s T R hR
  have hrepE : ∀ x, E.u (x, t) = w (x, t) := by
    intro x
    exact cauchyMollified_continuous_rep_unique hsT hEcont hwcont hEsec hwsec x t
      ⟨hst.le, htT⟩
  have hinitE : ∀ x, E.u (x, E.s) = PDE.wholeSpaceMollify ε f x := by
    intro x
    simpa only [hEs] using hEinit x
  have hμ : E.μP ≤ slabMeasure d s T := by
    change volume.restrict (E.K ×ˢ Ioc E.s E.t) ≤
      volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s T)
    apply Measure.restrict_mono
    · rw [hEs, hEt]
      apply prod_mono (subset_univ _)
      intro τ hτ
      exact ⟨hτ.1.le, hτ.2.trans htT⟩
    · exact le_rfl
  let V : ℝ := (eLpNorm (cauchyEnergyValue u) 2 (slabMeasure d s T)).toReal
  let H : Fin d → ℝ := fun i =>
    (eLpNorm (fun z => cauchyEnergyGradient u z i) 2 (slabMeasure d s T)).toReal
  let G : Fin d → ℝ := fun i =>
    (eLpNorm (fun z => matVecMul (a z) (cauchyEnergyGradient u z) i)
      2 (slabMeasure d s T)).toReal
  let F : ℝ := (eLpNorm f 2 volume).toReal ^ 2
  have hrawV : MemLp (cauchyEnergyValue u) 2 (slabMeasure d s T) :=
    cauchyEnergyValue_memLp u
  have hnormV : (eLpNorm E.u 2 E.μP).toReal ≤ V := by
    apply ENNReal.toReal_mono hrawV.eLpNorm_ne_top
    exact (eLpNorm_local_ae_le_global E hμ hEu).trans
      (cauchyMollT_memLp hε hrawV).2
  have hnormH : ∀ i, (eLpNorm (fun z => E.Du z i) 2 E.μP).toReal ≤ H i := by
    intro i
    have hraw := cauchyEnergyGradient_coord_memLp u i
    apply ENNReal.toReal_mono hraw.eLpNorm_ne_top
    exact (eLpNorm_local_ae_le_global E hμ (hEDu i)).trans
      (cauchyMollT_memLp hε hraw).2
  have hnormG : ∀ i, (eLpNorm (fun z => E.G z i) 2 E.μP).toReal ≤ G i := by
    intro i
    have hraw := cauchyEnergyFlux_coord_memLp ha u i
    apply ENNReal.toReal_mono hraw.eLpNorm_ne_top
    exact (eLpNorm_local_ae_le_global E hμ (hEG i)).trans
      (cauchyMollT_memLp hε hraw).2
  have hphi : ∀ z, |E.φ z| ≤ 1 := by
    intro z
    rw [hEφ]
    rcases PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff_nonneg_le_one
      s T R hR z with ⟨h0, h1⟩
    rw [abs_le]
    exact ⟨by linarith, h1⟩
  have htime : ∀ z, parTimeDeriv E.φ z = 0 := by
    intro z
    rw [hEφ]
    exact PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff_timeDeriv_eq_zero
      s T R hR z.1 z.2
  have hcross : ∀ z i, |2 * E.φ z * parSpaceGrad E.φ z i| ≤ 64 / R := by
    intro z i
    rw [hEφ]
    have hφabs : |χ.toFun z| ≤ 1 := by
      rcases PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff_nonneg_le_one
        s T R hR z with ⟨h0, h1⟩
      exact abs_le.mpr ⟨by linarith, h1⟩
    have hgrad : |parSpaceGrad χ.toFun z i| ≤ 32 / R := by
      exact (abs_apply_le_vecEuclideanNorm (parSpaceGrad χ.toFun z) i).trans
        (PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff_spatialGrad_bound
          s T R hR z.1 z.2)
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
    calc
      2 * |χ.toFun z| * |parSpaceGrad χ.toFun z i| ≤
          2 * 1 * (32 / R) := by
            exact mul_le_mul (mul_le_mul_of_nonneg_left hφabs (by norm_num))
              hgrad (abs_nonneg _) (by positivity)
      _ = 64 / R := by ring
  have hinitBound := cauchyEnergyData_initial_cutoff_le E hε hf hphi hinitE
  have hcut := cauchyEnergyData_cutoff_slice_bound_of_norms E hR hRone
    htime hphi hcross hinitBound hnormV hnormH hnormG (fun i => ENNReal.toReal_nonneg)
  have hballInner : ∀ x ∈ euclideanClosedBall (0 : Vec d) ((n : ℝ) + 1),
      x ∈ euclideanBall (0 : Vec d) R := by
    intro x hx
    have hnorm := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).1 hx
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).2
    rw [sub_zero] at hnorm ⊢
    dsimp [R]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith
  have hballSub : euclideanClosedBall (0 : Vec d) ((n : ℝ) + 1) ⊆ E.K := by
    rw [hEK]
    intro x hx
    by_contra hnot
    have hzero := image_eq_zero_of_notMem_tsupport hnot
    have hone : (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).toFun x = 1 :=
      (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).eq_one_on_inner x
        (hballInner x hx)
    have hne : (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).toFun x ≠ 0 := by
      rw [hone]
      norm_num
    exact hne hzero
  have hχone : ∀ x ∈ euclideanClosedBall (0 : Vec d) ((n : ℝ) + 1),
      E.φ (x, E.t) = 1 := by
    intro x hx
    rw [hEφ, hEt]
    exact PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff_eq_one
      s T R hR (hballInner x hx)
  have hslice : MemLp (fun x => E.u (x, E.t)) 2 (volume.restrict E.K1) := by
    apply E.hus E.t
    rw [hEs, hEt]
    exact ⟨hst.le, le_rfl⟩
  have hKsub : E.K ⊆ E.K1 := PDE.Parabolic.Energy.Data.K_subset_K1 E
  have hball := cauchyEnergyData_ball_slice_bound E
    (measurableSet_euclideanClosedBall 0 ((n : ℝ) + 1)) hballSub
    (by simpa only [hEt] using hχone) (by simpa only [hEt] using hrepE)
    hphi hslice hKsub hcut
  simpa only [hEt, F, V, H, G] using hball

end PDE.Parabolic.Lions
