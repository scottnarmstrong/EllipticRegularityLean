module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.LionsBound.MollifiedBallBound
public import PDEFoundation.Sobolev.Inequalities.SobolevWholeSpaceMollify

/-! # Uniform global spatial slice bounds for the Lions energy field -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace PDE.Parabolic.Lions

private def exhaustionBall {d : ℕ} (n : ℕ) : Set (Vec d) :=
  euclideanClosedBall 0 ((n : ℝ) + 1)

private theorem exhaustionBall_measurable {d : ℕ} (n : ℕ) :
    MeasurableSet (exhaustionBall (d := d) n) := by
  exact measurableSet_euclideanClosedBall 0 ((n : ℝ) + 1)

private theorem exhaustionBall_mono {d : ℕ} {m n : ℕ} (hmn : m ≤ n) :
    exhaustionBall (d := d) m ⊆ exhaustionBall n := by
  intro x hx
  have hnorm := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).1 hx
  apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
  rw [sub_zero] at hnorm ⊢
  have hcast : (m : ℝ) ≤ n := by exact_mod_cast hmn
  linarith

/-- Local `L²` control on an exhausting family of Euclidean balls, together with a uniform bound
on their squared integrals, gives the corresponding global `L²` bound. -/
private theorem memLp_of_exhaustionBall_sq_bound
    {d : ℕ} {g : Vec d → ℝ} {C : ℝ}
    (hg : Measurable g)
    (hloc : ∀ n, MemLp g 2 (volume.restrict (exhaustionBall (d := d) n)))
    (hball : ∀ n, (∫ x in exhaustionBall (d := d) n, g x ^ 2) ≤ C)
    (hC : 0 ≤ C) :
    MemLp g 2 (volume : Measure (Vec d)) ∧
      (eLpNorm g 2 volume).toReal ^ 2 ≤ C := by
  let q : Vec d → ℝ≥0∞ := fun x => ENNReal.ofReal (g x ^ 2)
  let F : ℕ → Vec d → ℝ≥0∞ := fun n =>
    (exhaustionBall (d := d) n).indicator q
  have hqmeas : Measurable q := by
    exact ENNReal.continuous_ofReal.measurable.comp (hg.pow_const 2)
  have hFmeas : ∀ n, Measurable (F n) := by
    intro n
    exact hqmeas.indicator (exhaustionBall_measurable n)
  have hFmono : Monotone F := by
    intro m n hmn x
    by_cases hx : x ∈ exhaustionBall (d := d) m
    · have hxn : x ∈ exhaustionBall (d := d) n :=
        exhaustionBall_mono hmn hx
      simp [F, hx, hxn]
    · simp [F, hx]
  have hFbound : ∀ n, (∫⁻ x, F n x ∂(volume : Measure (Vec d))) ≤ ENNReal.ofReal C := by
    intro n
    have hnonneg : 0 ≤ᵐ[volume.restrict (exhaustionBall (d := d) n)]
        (fun x : Vec d => g x ^ 2) := by
      filter_upwards [] with x
      exact sq_nonneg (g x)
    have hlocal := hloc n
    have hset :
        (∫⁻ x, F n x ∂(volume : Measure (Vec d))) =
          ∫⁻ x, ENNReal.ofReal (g x ^ 2)
            ∂(volume.restrict (exhaustionBall (d := d) n)) := by
      rw [← lintegral_indicator (exhaustionBall_measurable n)]
    rw [hset]
    rw [← ofReal_integral_eq_lintegral_ofReal hlocal.integrable_sq hnonneg]
    exact ENNReal.ofReal_le_ofReal (hball n)
  have hq_eq_iSup : (fun x => ⨆ n, F n x) = q := by
    funext x
    apply le_antisymm
    · apply iSup_le
      intro n
      by_cases hx : x ∈ exhaustionBall (d := d) n
      · simp [F, hx]
      · simp [F, hx]
    · obtain ⟨N, hN⟩ := exists_nat_gt (vecEuclideanNorm x)
      apply le_iSup_of_le N
      have hx : x ∈ exhaustionBall (d := d) N := by
        apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
        rw [sub_zero]
        linarith
      simp [F, hx]
  have hqint : (∫⁻ x, q x ∂(volume : Measure (Vec d))) ≤ ENNReal.ofReal C := by
    calc
      ∫⁻ x, q x ∂(volume : Measure (Vec d)) =
          ∫⁻ x, ⨆ n, F n x ∂(volume : Measure (Vec d)) := by rw [hq_eq_iSup]
      _ = ⨆ n, ∫⁻ x, F n x ∂(volume : Measure (Vec d)) :=
        lintegral_iSup hFmeas hFmono
      _ ≤ ENNReal.ofReal C := iSup_le fun n => hFbound n
  have hqtop : (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂(volume : Measure (Vec d))) ≠ ⊤ := by
    have hqeq : (fun x : Vec d => ‖g x‖ₑ ^ (2 : ℝ)) = q := by
      funext x
      simp only [q, Real.enorm_eq_ofReal_abs]
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (g x)) (by norm_num : 0 ≤ (2 : ℝ)),
        Real.rpow_two, sq_abs]
    rw [show (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂(volume : Measure (Vec d))) =
        ∫⁻ x, q x ∂(volume : Measure (Vec d)) by rw [hqeq]]
    exact ne_top_of_le_ne_top (ENNReal.ofReal_ne_top) hqint
  have hmem : MemLp g 2 (volume : Measure (Vec d)) := by
    rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      hg.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hqtop
  have hglobalInt : (∫ x, g x ^ 2 ∂(volume : Measure (Vec d))) ≤ C := by
    have hnonneg : 0 ≤ᵐ[volume] (fun x : Vec d => g x ^ 2) := by
      filter_upwards [] with x
      exact sq_nonneg (g x)
    have hreal : ENNReal.ofReal (∫ x, g x ^ 2 ∂(volume : Measure (Vec d))) ≤
        ENNReal.ofReal C := by
      calc
        ENNReal.ofReal (∫ x, g x ^ 2 ∂(volume : Measure (Vec d))) =
            ∫⁻ x, q x ∂(volume : Measure (Vec d)) :=
          ofReal_integral_eq_lintegral_ofReal hmem.integrable_sq hnonneg
        _ ≤ ENNReal.ofReal C := hqint
    exact (ENNReal.ofReal_le_ofReal_iff hC).1 hreal
  refine ⟨hmem, ?_⟩
  rw [PDE.toReal_eLpNorm_two_sq_eq_integral_sq hmem]
  exact hglobalInt

/-- The rescaled Lions energy field has an almost-every-time global spatial `L²` bound. The
constant is explicit and depends only on the initial datum and the space-time `L²` norms of the
value, gradient, and coefficient flux. -/
theorem cauchyEnergyValue_ae_slice_norm_bound
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 (volume : Measure (Vec d)))
    (u : CauchyX d s T) {u₀ : CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u) :
    ∀ᵐ t ∂(volume.restrict (Icc s T)),
      MemLp (fun x : Vec d => cauchyEnergyValue u (x, t)) 2
          (volume : Measure (Vec d)) ∧
        eLpNorm (fun x : Vec d => cauchyEnergyValue u (x, t)) 2 volume ≤
          ENNReal.ofReal (Real.sqrt (
            (eLpNorm f 2 volume).toReal ^ 2 +
              2 * ∑ i : Fin d,
                ((eLpNorm (fun z => matVecMul (a z) (cauchyEnergyGradient u z) i)
                    2 (slabMeasure d s T)).toReal *
                    (eLpNorm (fun z => cauchyEnergyGradient u z i)
                      2 (slabMeasure d s T)).toReal +
                  64 * (eLpNorm (fun z => matVecMul (a z)
                    (cauchyEnergyGradient u z) i) 2 (slabMeasure d s T)).toReal *
                    (eLpNorm (cauchyEnergyValue u) 2 (slabMeasure d s T)).toReal))) := by
  let C : ℝ := (eLpNorm f 2 volume).toReal ^ 2 +
      2 * ∑ i : Fin d,
        ((eLpNorm (fun z => matVecMul (a z) (cauchyEnergyGradient u z) i)
            2 (slabMeasure d s T)).toReal *
            (eLpNorm (fun z => cauchyEnergyGradient u z i)
              2 (slabMeasure d s T)).toReal +
          64 * (eLpNorm (fun z => matVecMul (a z)
            (cauchyEnergyGradient u z) i) 2 (slabMeasure d s T)).toReal *
            (eLpNorm (cauchyEnergyValue u) 2 (slabMeasure d s T)).toReal)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  let ε : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hε : ∀ n, 0 < ε n := by
    intro n
    dsimp [ε]
    positivity
  have hεle : ∀ n, ε n ≤ 1 := by
    intro n
    dsimp [ε]
    apply (inv_le_one₀ (by positivity)).2
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith
  have hεtendsto : Tendsto ε atTop (𝓝 0) := by
    simpa [ε, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let RepOK (n : ℕ) (w : Vec d × ℝ → ℝ) : Prop :=
    Measurable w ∧
      (∀ x, ContinuousOn (fun τ => w (x, τ)) (Icc s T)) ∧
      (∀ x, (fun τ => PDE.Parabolic.Energy.mollT (ε n) univ
        (cauchyEnergyValue u) (x, τ)) =ᵐ[volume.restrict (Icc s T)]
          (fun τ => w (x, τ))) ∧
      (∀ t, t ∈ Icc s T → ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun x => w (x, t)) 2 (volume.restrict K)) ∧
      (∀ᵐ z ∂(slabMeasure d s T),
        w z = PDE.Parabolic.Energy.mollT (ε n) univ (cauchyEnergyValue u) z)
  have hRepExists : ∀ n, ∃ w, RepOK n w := by
    intro n
    obtain ⟨w, D, G, hwm, _hDm, _hGm, hwcont, hwsec, hloc, _hWmem,
      _hDmem, _hGmem, hwae, _hDae, _hGae, _hWgrad, _hB⟩ :=
      exists_cauchy_mollified_energy_representatives hsT ha (hε n) f hf u hclose hrep
    exact ⟨w, hwm, hwcont, hwsec, hloc, hwae⟩
  choose w hw using hRepExists
  have hball : ∀ n m t, s < t → t ≤ T →
      (∫ x in exhaustionBall (d := d) m, w n (x, t) ^ 2) ≤ C := by
    intro n m t hst htT
    rcases hw n with ⟨hwm, hwcont, hwsec, _hloc, _hwae⟩
    exact cauchy_mollified_cutoff_ball_bound hsT ha (hε n) f hf u hclose hrep
      hwcont hwsec hst htT m
  have hscaleProd : ∀ n, ∀ᵐ z ∂((volume : Measure (Vec d)).prod
      (volume.restrict (Icc s T))),
        w n z = PDE.Parabolic.Energy.mollT (ε n) univ (cauchyEnergyValue u) z := by
    intro n
    rcases hw n with ⟨_hwm, _hwcont, _hwsec, _hloc, hwae⟩
    have hmeasure : (volume : Measure (Vec d)).prod
        (volume.restrict (Icc s T)) = slabMeasure d s T := by
      change (volume : Measure (Vec d)).prod (volume.restrict (Icc s T)) =
        (volume : Measure (Vec d × ℝ)).restrict (univ ×ˢ Icc s T)
      calc
        _ = (volume.restrict (univ : Set (Vec d))).prod
            (volume.restrict (Icc s T)) := by simp
        _ = (volume : Measure (Vec d × ℝ)).restrict (univ ×ˢ Icc s T) :=
          (PDE.Parabolic.Energy.volume_restrict_prod univ (Icc s T)).symm
    have hwae' := hwae
    rw [← hmeasure] at hwae'
    exact hwae'
  have hscaleSlice : ∀ n, ∀ᵐ t ∂(volume.restrict (Icc s T)),
      ∀ᵐ x ∂(volume : Measure (Vec d)),
        w n (x, t) = PDE.Parabolic.Energy.mollT (ε n) univ
          (cauchyEnergyValue u) (x, t) := by
    intro n
    exact PDE.Parabolic.Energy.ae_ae_swap (hscaleProd n)
  have hallScaleSlice : ∀ᵐ t ∂(volume.restrict (Icc s T)), ∀ n,
      ∀ᵐ x ∂(volume : Measure (Vec d)),
        w n (x, t) = PDE.Parabolic.Energy.mollT (ε n) univ
          (cauchyEnergyValue u) (x, t) := by
    exact ae_all_iff.2 hscaleSlice
  have hnotS : ∀ᵐ t ∂(volume.restrict (Icc s T)), t ≠ s := by
    rw [ae_iff]
    have hnull : (volume.restrict (Icc s T)) {s} = 0 := by
      refine le_antisymm ?_ bot_le
      have hrestrict : volume.restrict (Icc s T) ≤ (volume : Measure ℝ) :=
        Measure.restrict_le_self
      calc
        (volume.restrict (Icc s T)) {s} ≤ volume {s} := hrestrict {s}
        _ = 0 := measure_singleton s
    have hset : {t : ℝ | ¬ t ≠ s} = {s} := by
      ext t
      simp
    rw [hset]
    exact hnull
  have hrawSlice := cauchyEnergyValue_ae_sliceMemLp u
  filter_upwards [hrawSlice, hallScaleSlice, hnotS,
    ae_restrict_mem (measurableSet_Icc : MeasurableSet (Icc s T))]
    with t hrawL2 hscaleEq hts ht
  have hst : s < t := by
    rcases lt_or_eq_of_le ht.1 with hlt | heq
    · exact hlt
    · exact (hts heq.symm).elim
  let g : Vec d → ℝ := fun x => cauchyEnergyValue u (x, t)
  have hεconv : Tendsto (fun n =>
      eLpNorm (PDE.wholeSpaceMollify (ε n) g - g) 2 volume) atTop (𝓝 0) :=
    tendsto_eLpNorm_wholeSpaceMollify_sub (p := 2) (by norm_num) (by norm_num)
      (by simpa [g] using hrawL2) hε hεle hεtendsto
  have hmollEq (n : ℕ) :
      (fun x : Vec d => PDE.Parabolic.Energy.mollT (ε n) univ
        (cauchyEnergyValue u) (x, t)) = PDE.wholeSpaceMollify (ε n) g := by
    funext x
    simp [PDE.Parabolic.Energy.mollT, g]
  let moll : ℕ → Vec d → ℝ := fun n x =>
    PDE.Parabolic.Energy.mollT (ε n) univ (cauchyEnergyValue u) (x, t)
  have hmollEq' (n : ℕ) : moll n = PDE.wholeSpaceMollify (ε n) g := by
    exact hmollEq n
  have hεconv' : Tendsto (fun n =>
      eLpNorm (moll n - g) 2 volume) atTop (𝓝 0) := by
    simpa only [← hmollEq'] using hεconv
  have hmollBound : ∀ n, eLpNorm
      (moll n) 2 volume ≤ ENNReal.ofReal (Real.sqrt C) := by
    intro n
    rcases hw n with ⟨hwm, _hwcont, _hwsec, hloc, _hwae⟩
    have hglobal := memLp_of_exhaustionBall_sq_bound
      (g := fun x : Vec d => w n (x, t)) (C := C)
      (hwm.comp (measurable_id.prodMk measurable_const))
      (fun m => hloc t ht (exhaustionBall (d := d) m)
        (isCompact_euclideanClosedBall 0 (by positivity)))
      (fun m => hball n m t hst ht.2) hC
    have hroot : Real.sqrt C ^ 2 = C := Real.sq_sqrt hC
    have hrootBound : (eLpNorm (fun x : Vec d => w n (x, t)) 2 volume).toReal ≤
        Real.sqrt C := by
      have hnormNonneg : 0 ≤
          (eLpNorm (fun x : Vec d => w n (x, t)) 2 volume).toReal := ENNReal.toReal_nonneg
      have hsqrtNonneg : 0 ≤ Real.sqrt C := Real.sqrt_nonneg C
      nlinarith [hglobal.2]
    have hrootBoundENN : eLpNorm (fun x : Vec d => w n (x, t)) 2 volume ≤
        ENNReal.ofReal (Real.sqrt C) := by
      rw [← ENNReal.ofReal_toReal hglobal.1.eLpNorm_ne_top]
      exact ENNReal.ofReal_le_ofReal hrootBound
    have hsliceEq : (fun x : Vec d => w n (x, t)) =ᵐ[volume] moll n := by
      filter_upwards [hscaleEq n] with x hx
      exact hx
    calc
      eLpNorm (moll n) 2 volume =
          eLpNorm (fun x : Vec d => w n (x, t)) 2 volume :=
        eLpNorm_congr_ae hsliceEq.symm
      _ ≤ ENNReal.ofReal (Real.sqrt C) := hrootBoundENN
  have hneg (n : ℕ) : g - moll n = -(moll n - g) := by
    funext x
    simp only [Pi.sub_apply, Pi.neg_apply]
    ring
  have htri : ∀ n, eLpNorm g 2 volume ≤
      eLpNorm (g - moll n) 2 volume + eLpNorm (moll n) 2 volume := by
    intro n
    have hdecomp : g = (g - moll n) + moll n := by
      funext x
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    calc
      eLpNorm g 2 volume = eLpNorm ((g - moll n) + moll n) 2 volume := by rw [← hdecomp]
      _ ≤ eLpNorm (g - moll n) 2 volume + eLpNorm (moll n) 2 volume :=
        eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hdiffConv : Tendsto (fun n => eLpNorm (g - moll n) 2 volume) atTop (𝓝 0) := by
    have hEq : (fun n => eLpNorm (g - moll n) 2 volume) =
        (fun n => eLpNorm (moll n - g) 2 volume) := by
      funext n
      rw [hneg n, eLpNorm_neg]
    rw [hEq]
    exact hεconv'
  have hsumConv : Tendsto (fun n =>
      eLpNorm (g - moll n) 2 volume + ENNReal.ofReal (Real.sqrt C)) atTop
        (𝓝 (ENNReal.ofReal (Real.sqrt C))) := by
    simpa using hdiffConv.add tendsto_const_nhds
  have hlimitBound : eLpNorm g 2 volume ≤ ENNReal.ofReal (Real.sqrt C) := by
    exact ge_of_tendsto hsumConv (Eventually.of_forall fun n =>
      (htri n).trans
        (add_le_add_right (hmollBound n) (eLpNorm (g - moll n) 2 volume)))
  exact ⟨hrawL2, by simpa [g, C] using hlimitBound⟩

end PDE.Parabolic.Lions
