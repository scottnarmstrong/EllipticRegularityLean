module

public import EllipticRegularity.Parabolic.LocalMax.Energy
public import EllipticRegularity.Parabolic.LocalMax.PowerFamilyStruct
public import EllipticRegularity.Parabolic.LocalMax.PowerStepCore
public import EllipticRegularity.Parabolic.LocalMax.Cutoff
public import EllipticRegularity.Parabolic.LocalMax.LocalMax
public import PDEFoundation.Measure.BallVolume

/-!
# The Moser power step for nonnegative parabolic solutions

For a nonnegative weak solution `u` on `B₁ × (-1,0]`, `ε > 0`, `p > 1` and nested cylinders
`B_r × (T', t_top) ⊂ B_ρ × (T, t_top)`,

`∫∫_{B_r × (T',t_top)} (u+ε)^{pχ} ≤ (C₀ Λ K² ((ρ-r)⁻² + (T'-T)⁻¹))^χ (∫∫_{B_ρ × (T,t_top)} (u+ε)^p)^χ`

with `χ = (d+2)/d`, `K = 2 + p/(p-1)` and `C₀ = C₀(d)`.  The proof tests the renormalized
equation with the truncated powers of `PowerFamily`, applies the energy estimate and the
parabolic Sobolev step with the product cutoff of `Cutoff`, and removes the truncation by
Fatou's lemma.  This discharges `PowerStepProp`, giving the parabolic local maximum estimate.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.LocalMax

open MeasureTheory Set Filter Topology

/-- The final scalar bookkeeping of the power step. -/
theorem power_step_arith {d : ℕ} (hd : 0 < d) {Cs : ℝ≥0∞} (hCs : Cs ≠ ⊤) {K Y : ℝ}
    (hK : 1 ≤ K) (I : ℝ≥0∞) :
    Cs * (ENNReal.ofReal K * (ENNReal.ofReal Y * I)) ^ (2 / (d : ℝ)) *
        (ENNReal.ofReal (5 * K) * (ENNReal.ofReal Y * I)) ≤
      ENNReal.ofReal (max 1 (5 * Cs.toReal) * (K * Y)) ^ (((d : ℝ) + 2) / d) *
        I ^ (((d : ℝ) + 2) / d) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hK0 : 0 ≤ K := by linarith
  set x : ℝ≥0∞ := ENNReal.ofReal (K * Y) * I with hx
  have h1 : ENNReal.ofReal K * (ENNReal.ofReal Y * I) = x := by
    rw [hx, ENNReal.ofReal_mul hK0, mul_assoc]
  have h2 : ENNReal.ofReal (5 * K) * (ENNReal.ofReal Y * I) = 5 * x := by
    rw [hx, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5), ENNReal.ofReal_mul hK0]
    simp [mul_assoc]
  rw [h1, h2]
  have hχ : ((d : ℝ) + 2) / d = 2 / d + 1 := by field_simp; ring
  have hxχ : x ^ (2 / (d : ℝ)) * x = x ^ (((d : ℝ) + 2) / d) := by
    rw [hχ, ENNReal.rpow_add_of_nonneg _ _ (by positivity) zero_le_one, ENNReal.rpow_one]
  have hm1 : (1 : ℝ) ≤ max 1 (5 * Cs.toReal) := le_max_left _ _
  have h5C : 5 * Cs ≤ ENNReal.ofReal (max 1 (5 * Cs.toReal)) := by
    calc 5 * Cs = ENNReal.ofReal (5 * Cs.toReal) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hCs]
          norm_num
      _ ≤ _ := ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hχ1 : (1 : ℝ) ≤ ((d : ℝ) + 2) / d := by
    rw [hχ]
    have : 0 ≤ 2 / (d : ℝ) := by positivity
    linarith
  have hmχ : ENNReal.ofReal (max 1 (5 * Cs.toReal)) ≤
      ENNReal.ofReal (max 1 (5 * Cs.toReal)) ^ (((d : ℝ) + 2) / d) := by
    calc _ = ENNReal.ofReal (max 1 (5 * Cs.toReal)) ^ (1 : ℝ) := (ENNReal.rpow_one _).symm
      _ ≤ _ := ENNReal.rpow_le_rpow_of_exponent_le (ENNReal.one_le_ofReal.2 hm1) hχ1
  have hχ0 : (0 : ℝ) ≤ ((d : ℝ) + 2) / d := by positivity
  calc Cs * x ^ (2 / (d : ℝ)) * (5 * x) = 5 * Cs * (x ^ (2 / (d : ℝ)) * x) := by ring
    _ = 5 * Cs * x ^ (((d : ℝ) + 2) / d) := by rw [hxχ]
    _ ≤ ENNReal.ofReal (max 1 (5 * Cs.toReal)) ^ (((d : ℝ) + 2) / d) *
          x ^ (((d : ℝ) + 2) / d) := by
        gcongr
        exact h5C.trans hmχ
    _ = _ := by
        rw [hx, ENNReal.mul_rpow_of_nonneg _ _ hχ0, ← mul_assoc,
          ← ENNReal.mul_rpow_of_nonneg _ _ hχ0, ← ENNReal.ofReal_mul (by linarith)]

/-- The energy bound is controlled by the `L^p` integral of `u + ε` on the support cylinder. -/
theorem energyBound_le_of_support {d : ℕ} {I : Set ℝ}
    (u : ParH1Function (euclideanBall (0 : Vec d) 1) I)
    {Lam K ε p T tTop ρ Bη : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hε : 0 < ε) (hp : 0 ≤ p) (hBη : 0 ≤ Bη)
    (hLK : 0 ≤ Lam * K)
    (hpos : ∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioo T tTop)),
      0 ≤ u.toFun z)
    {F : ℝ → ℝ} (hFle : ∀ s, 0 ≤ s → F s ≤ (s + ε) ^ p)
    {η : Vec d × ℝ → ℝ}
    (hsupp : ∀ z : Vec d × ℝ, z.1 ∉ euclideanBall (0 : Vec d) ρ →
      2 * |η z| * |parTimeDeriv η z| + 2 * Lam * K * vecNormSq (parSpaceGrad η z) = 0)
    (hb : ∀ z, 2 * |η z| * |parTimeDeriv η z| + 2 * Lam * K * vecNormSq (parSpaceGrad η z) ≤ Bη) :
    energyBound Lam K F u η T tTop ≤ ENNReal.ofReal Bη *
      ∫⁻ z in euclideanBall (0 : Vec d) ρ ×ˢ Ioo T tTop, ENNReal.ofReal (u.toFun z + ε) ^ p := by
  unfold energyBound
  set S := euclideanBall (0 : Vec d) ρ ×ˢ Ioo T tTop with hS
  have hSm : MeasurableSet S := (measurableSet_euclideanBall _ _).prod measurableSet_Ioo
  have hbnn : ∀ z, 0 ≤ 2 * |η z| * |parTimeDeriv η z| +
      2 * Lam * K * vecNormSq (parSpaceGrad η z) := fun z => by
    have h1 : 0 ≤ 2 * |η z| * |parTimeDeriv η z| := by positivity
    have h2 : 0 ≤ 2 * Lam * K * vecNormSq (parSpaceGrad η z) := by
      have := vecNormSq_nonneg (parSpaceGrad η z)
      have : 0 ≤ 2 * Lam * K := by linarith
      positivity
    linarith
  calc ∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioo T tTop, ENNReal.ofReal (F (u.toFun z) *
        (2 * |η z| * |parTimeDeriv η z| + 2 * Lam * K * vecNormSq (parSpaceGrad η z)))
      ≤ ∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioo T tTop,
          S.indicator (fun z => ENNReal.ofReal Bη * ENNReal.ofReal (u.toFun z + ε) ^ p) z := by
        refine lintegral_mono_ae ?_
        filter_upwards [hpos, ae_restrict_mem
          ((measurableSet_euclideanBall (0 : Vec d) 1).prod measurableSet_Ioo)] with z hz hzmem
        by_cases hzS : z ∈ S
        · rw [indicator_of_mem hzS, ENNReal.ofReal_rpow_of_nonneg (by linarith) hp,
            ← ENNReal.ofReal_mul hBη]
          refine ENNReal.ofReal_le_ofReal ?_
          calc F (u.toFun z) * (2 * |η z| * |parTimeDeriv η z| +
                2 * Lam * K * vecNormSq (parSpaceGrad η z))
              ≤ (u.toFun z + ε) ^ p * Bη :=
                mul_le_mul (hFle _ hz) (hb z) (hbnn z) (Real.rpow_nonneg (by linarith) _)
            _ = Bη * (u.toFun z + ε) ^ p := mul_comm _ _
        · have hz1 : z.1 ∉ euclideanBall (0 : Vec d) ρ := fun h => hzS ⟨h, hzmem.2⟩
          rw [indicator_of_notMem hzS, hsupp z hz1, mul_zero, ENNReal.ofReal_zero]
    _ = ∫⁻ z in S, ENNReal.ofReal Bη * ENNReal.ofReal (u.toFun z + ε) ^ p := by
        rw [lintegral_indicator hSm, Measure.restrict_restrict hSm,
          inter_eq_left.2 (prod_mono (euclideanBall_mono hρ0 hρ1) subset_rfl)]
    _ = ENNReal.ofReal Bη * ∫⁻ z in S, ENNReal.ofReal (u.toFun z + ε) ^ p :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- `(w^{p/2})^{2(d+2)/d} = w^{p(d+2)/d}` in `ℝ≥0∞`. -/
theorem ofReal_half_pow_rpow {d : ℕ} {w p : ℝ} (hw : 0 ≤ w) (hp : 0 ≤ p) :
    ENNReal.ofReal |w ^ (p / 2)| ^ (2 * ((d : ℝ) + 2) / d) =
      ENNReal.ofReal w ^ (p * (((d : ℝ) + 2) / d)) := by
  have he : 0 ≤ 2 * ((d : ℝ) + 2) / d := by positivity
  rw [abs_of_nonneg (Real.rpow_nonneg hw _), ENNReal.ofReal_rpow_of_nonneg
    (Real.rpow_nonneg hw _) he, ← Real.rpow_mul hw, ENNReal.ofReal_rpow_of_nonneg hw
    (by positivity)]
  congr 2
  ring

/-- **Moser power step** for nonnegative parabolic solutions; `C₀` depends only on `d`. -/
theorem power_step (d : ℕ) (hd : 0 < d) : ∃ C₀ : ℝ, 0 < C₀ ∧ PowerStepProp d C₀ := by
  obtain ⟨Cs, hCs, hcore⟩ := cutoff_comp_energy_sobolev d hd
  obtain ⟨Bst, hBst0, hBst⟩ := exists_abs_deriv_smoothTransition_le
  refine ⟨max 1 (5 * Cs.toReal) * (4 * Bst + 2048), by positivity, ?_⟩
  intro Lam hLam a ha u hu hpos ε hε p hp r ρ T T' tTop hr hrρ hρ1 hT hTT' hT't htTop
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set K : ℝ := 2 + p / (p - 1) with hKdef
  have hp1 : 0 < p - 1 := by linarith
  have hK1 : 1 ≤ K := by
    have : 0 ≤ p / (p - 1) := div_nonneg (by linarith) hp1.le
    linarith
  have hK0 : 0 ≤ K := by linarith
  have hLam0 : 0 ≤ Lam := by linarith
  set J := Ioo T tTop with hJ
  set η := cylCutoff (d := d) r ρ T T' with hηdef
  set Kx := tsupport (canonicalBallCutoff (0 : Vec d) r ρ) with hKxdef
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := cylCutoff_contDiff hr.le hrρ T T'
  have hKx : IsCompact Kx := (canonicalBallCutoff_hasCompactSupport hr.le hrρ).isCompact
  have hKxρ : Kx ⊆ euclideanBall (0 : Vec d) ρ := canonicalBallCutoff_tsupport_subset_outer hr.le hrρ
  have hρ0 : 0 ≤ ρ := by linarith
  have hKxΩ : Kx ⊆ euclideanBall (0 : Vec d) 1 := hKxρ.trans (euclideanBall_mono hρ0 hρ1)
  have hηx : ∀ x t, x ∉ Kx → η (x, t) = 0 := fun x t hx => cylCutoff_eq_zero_of_notMem hx t
  have hδ : 0 < (T' - T) / 2 := by linarith
  have hηt : ∀ x t, t ≤ T + (T' - T) / 2 → η (x, t) = 0 :=
    fun x t ht => cylCutoff_eq_zero_of_le hTT' x ht
  have hJI : J ⊆ Ioc (-1 : ℝ) 0 := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hposJ : ∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ J)), 0 ≤ u.toFun z :=
    ae_restrict_of_ae_restrict_of_subset (prod_mono subset_rfl hJI) hpos
  -- the cutoff bound
  set Bη : ℝ := 2 * (2 * Bst / (T' - T)) + 2 * Lam * K * (1024 / (ρ - r) ^ 2) with hBηdef
  have hgap : 0 < T' - T := by linarith
  have hgapr : 0 < ρ - r := by linarith
  have hBη0 : 0 ≤ Bη := by positivity
  have hb : ∀ z, 2 * |η z| * |parTimeDeriv η z| + 2 * Lam * K * vecNormSq (parSpaceGrad η z) ≤
      Bη := by
    intro z
    have h1 : |η z| ≤ 1 := by
      rw [abs_of_nonneg (cylCutoff_nonneg _ _ _ _ z)]; exact cylCutoff_le_one _ _ _ _ z
    have h2 := abs_parTimeDeriv_cylCutoff_le hBst hr.le hrρ hTT' z
    have h3 := vecNormSq_parSpaceGrad_cylCutoff_le (d := d) hr.le hrρ T T' z
    have h4 : 2 * |η z| * |parTimeDeriv η z| ≤ 2 * (2 * Bst / (T' - T)) := by
      have := abs_nonneg (parTimeDeriv η z)
      calc 2 * |η z| * |parTimeDeriv η z| ≤ 2 * 1 * (2 * Bst / (T' - T)) := by gcongr
        _ = _ := by ring
    have h5 : 2 * Lam * K * vecNormSq (parSpaceGrad η z) ≤ 2 * Lam * K * (1024 / (ρ - r) ^ 2) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  have hsupp : ∀ z : Vec d × ℝ, z.1 ∉ euclideanBall (0 : Vec d) ρ →
      2 * |η z| * |parTimeDeriv η z| + 2 * Lam * K * vecNormSq (parSpaceGrad η z) = 0 := by
    rintro ⟨x, t⟩ hx
    have hxK : x ∉ Kx := fun h => hx (hKxρ h)
    have hξ : canonicalBallCutoff (0 : Vec d) r ρ x = 0 := image_eq_zero_of_notMem_tsupport hxK
    have hgradξ : classicalGradient (canonicalBallCutoff (0 : Vec d) r ρ) x = 0 := by
      funext i
      rw [classicalGradient_apply, fderiv_of_notMem_tsupport ℝ hxK]
      rfl
    rw [hηx x t hxK, parTimeDeriv_cylCutoff r ρ T T' x t hr.le hrρ rfl, hξ,
      parSpaceGrad_cylCutoff hr.le hrρ, hgradξ, smul_zero]
    simp [vecNormSq, vecDot]
  set I0 := ∫⁻ z in euclideanBall (0 : Vec d) ρ ×ˢ J, ENNReal.ofReal (u.toFun z + ε) ^ p
    with hI0
  -- the truncated family
  choose F G hF2 hF''b hG1 hG'b hstr using
    fun n : ℕ => exists_truncatedPower hp hε (n : ℝ) n.cast_nonneg
  set q : ℝ := 2 * ((d : ℝ) + 2) / d with hq
  have hN : ∀ n : ℕ, ∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ J,
      ENNReal.ofReal |η z * G n (u.toFun z)| ^ q ≤
        Cs * (ENNReal.ofReal K * (ENNReal.ofReal Bη * I0)) ^ (2 / (d : ℝ)) *
          (ENNReal.ofReal (5 * K) * (ENNReal.ofReal Bη * I0)) := by
    intro n
    have hFs : ∀ s, 0 ≤ s → 0 ≤ F n s ∧ 0 ≤ deriv (deriv (F n)) s ∧
        deriv (F n) s ^ 2 ≤ K * deriv (deriv (F n)) s * F n s := fun s hs =>
      ⟨(hstr n s hs).1, (hstr n s hs).2.1, (hstr n s hs).2.2.1⟩
    obtain ⟨hE1, hE2⟩ := power_energy_estimate (isOpen_euclideanBall _ _) ha u hu hpos (F n)
      (hF2 n) (hF''b n) hK0 hFs η hη hKx hKxΩ hηx hT (hTT'.trans hT't) htTop hδ hηt
    have hE3 : ∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ J, ENNReal.ofReal
        (F n (u.toFun z) * (2 * Lam * K * vecNormSq (parSpaceGrad η z))) ≤
          energyBound Lam K (F n) u η T tTop := by
      refine lintegral_mono_ae ?_
      filter_upwards [hposJ] with z hz
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (hstr n _ hz).1)
      have : 0 ≤ 2 * |η z| * |parTimeDeriv η z| := by positivity
      linarith
    have hR : energyBound Lam K (F n) u η T tTop ≤ ENNReal.ofReal Bη * I0 :=
      energyBound_le_of_support u hρ0 hρ1 hε (by linarith) hBη0 (by positivity) hposJ
        (fun s hs => (hstr n s hs).2.2.2.2.2.1) hsupp hb
    obtain ⟨M, hM, hGM⟩ := hG'b n
    have hcore' := hcore (isOpen_euclideanBall _ _) (volume_euclideanBall_ne_top _ zero_le_one)
      measurableSet_Ioo hJI u hposJ (F n) (G n) (hG1 n) M hM hGM hK1 hLam
      (fun s hs => ⟨(hstr n s hs).1, (hstr n s hs).2.1, (hstr n s hs).2.2.2.1,
        (hstr n s hs).2.2.2.2.1⟩) η hη Kx hKx hKxΩ hηx (energyBound Lam K (F n) u η T tTop)
        hE1 hE2 hE3
    refine hcore'.trans ?_
    gcongr
  -- Fatou in the truncation level
  set S' := euclideanBall (0 : Vec d) r ×ˢ Ioo T' tTop with hS'
  have hS'm : MeasurableSet S' := (measurableSet_euclideanBall _ _).prod measurableSet_Ioo
  have hS'sub : S' ⊆ euclideanBall (0 : Vec d) 1 ×ˢ J :=
    prod_mono (euclideanBall_mono hr.le (hrρ.le.trans hρ1))
      (Ioo_subset_Ioo_left hTT'.le)
  have hposS' : ∀ᵐ z ∂(volume.restrict S'), 0 ≤ u.toFun z :=
    ae_restrict_of_ae_restrict_of_subset hS'sub hposJ
  have huS' : AEMeasurable u.toFun (volume.restrict S') :=
    (u.memL2.aestronglyMeasurable.mono_measure (Measure.restrict_mono
      (hS'sub.trans (prod_mono subset_rfl hJI)) le_rfl)).aemeasurable
  have hlim : ∀ᵐ z ∂(volume.restrict S'),
      liminf (fun n : ℕ => ENNReal.ofReal |G n (u.toFun z)| ^ q) atTop =
        ENNReal.ofReal (u.toFun z + ε) ^ (p * (((d : ℝ) + 2) / d)) := by
    filter_upwards [hposS'] with z hz
    refine Tendsto.liminf_eq (tendsto_const_nhds.congr' ?_)
    obtain ⟨n₀, hn₀⟩ := exists_nat_ge (u.toFun z)
    filter_upwards [eventually_ge_atTop n₀] with n hn
    have hle : u.toFun z ≤ (n : ℝ) := hn₀.trans (by exact_mod_cast hn)
    rw [(hstr n _ hz).2.2.2.2.2.2.2 hle]
    exact (ofReal_half_pow_rpow (by linarith) (by linarith)).symm
  have hmeas : ∀ n : ℕ, AEMeasurable (fun z => ENNReal.ofReal |G n (u.toFun z)| ^ q)
      (volume.restrict S') := fun n =>
    (ENNReal.measurable_ofReal.comp_aemeasurable
      (((hG1 n).continuous.measurable.comp_aemeasurable huS').abs)).pow_const q
  have hset : ∀ n : ℕ, ∫⁻ z in S', ENNReal.ofReal |G n (u.toFun z)| ^ q ≤
      ∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ J, ENNReal.ofReal |η z * G n (u.toFun z)| ^ q := by
    intro n
    calc ∫⁻ z in S', ENNReal.ofReal |G n (u.toFun z)| ^ q
        = ∫⁻ z in S', ENNReal.ofReal |η z * G n (u.toFun z)| ^ q := by
          refine setLIntegral_congr_fun hS'm fun z hz => ?_
          obtain ⟨x, t⟩ := z
          rw [show η (x, t) = 1 from cylCutoff_eq_one hr.le hrρ hTT' hz.1 hz.2.1.le, one_mul]
      _ ≤ _ := lintegral_mono_set hS'sub
  calc ∫⁻ z in S', ENNReal.ofReal (u.toFun z + ε) ^ (p * (((d : ℝ) + 2) / d))
      = ∫⁻ z in S', liminf (fun n : ℕ => ENNReal.ofReal |G n (u.toFun z)| ^ q) atTop :=
        (lintegral_congr_ae hlim).symm
    _ ≤ liminf (fun n : ℕ => ∫⁻ z in S', ENNReal.ofReal |G n (u.toFun z)| ^ q) atTop :=
        lintegral_liminf_le' hmeas
    _ ≤ Cs * (ENNReal.ofReal K * (ENNReal.ofReal Bη * I0)) ^ (2 / (d : ℝ)) *
          (ENNReal.ofReal (5 * K) * (ENNReal.ofReal Bη * I0)) :=
        Filter.liminf_le_of_frequently_le'
          (Filter.Eventually.frequently (Filter.Eventually.of_forall fun n =>
            (hset n).trans (hN n)))
    _ ≤ ENNReal.ofReal (max 1 (5 * Cs.toReal) * (K * Bη)) ^ (((d : ℝ) + 2) / d) *
          I0 ^ (((d : ℝ) + 2) / d) := power_step_arith hd hCs hK1 (Y := Bη) I0
    _ ≤ _ := by
        refine mul_le_mul' (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) (by positivity))
          le_rfl
        -- `K Bη ≤ (4B + 2048) Λ K² ((ρ-r)⁻² + (T'-T)⁻¹)`
        have hg1 : 0 ≤ 1 / (ρ - r) ^ 2 := by positivity
        have hg2 : 0 ≤ 1 / (T' - T) := by positivity
        have hKK : K ≤ Lam * K ^ 2 := by
          have h1 := mul_le_mul_of_nonneg_left hK1 (by linarith : 0 ≤ K)
          have h2 := mul_le_mul_of_nonneg_right hLam (sq_nonneg K)
          linarith
        have e1 : K * Bη = 4 * Bst * K * (1 / (T' - T)) + 2048 * (Lam * K ^ 2) * (1 / (ρ - r) ^ 2) := by
          rw [hBηdef]; field_simp; ring
        rw [e1]
        have hm : 0 ≤ max 1 (5 * Cs.toReal) := le_trans zero_le_one (le_max_left _ _)
        have key : 4 * Bst * K * (1 / (T' - T)) + 2048 * (Lam * K ^ 2) * (1 / (ρ - r) ^ 2) ≤
            (4 * Bst + 2048) * Lam * K ^ 2 * (1 / (ρ - r) ^ 2 + 1 / (T' - T)) := by
          have a1 : 4 * Bst * K * (1 / (T' - T)) ≤ 4 * Bst * (Lam * K ^ 2) * (1 / (T' - T)) := by
            gcongr
          linarith [mul_nonneg (mul_nonneg hBst0 (by positivity : (0 : ℝ) ≤ Lam * K ^ 2)) hg1,
            mul_nonneg (by positivity : (0 : ℝ) ≤ Lam * K ^ 2) hg2]
        calc max 1 (5 * Cs.toReal) * (4 * Bst * K * (1 / (T' - T)) +
              2048 * (Lam * K ^ 2) * (1 / (ρ - r) ^ 2))
            ≤ max 1 (5 * Cs.toReal) * ((4 * Bst + 2048) * Lam * K ^ 2 *
                (1 / (ρ - r) ^ 2 + 1 / (T' - T))) := mul_le_mul_of_nonneg_left key hm
          _ = _ := by ring

/-- **Parabolic local maximum estimate** (Moser, `x.localmaxMoser`): for a nonnegative weak
solution on `B₁ × (-1,0]`, `esssup_{Q⁻_*} u ≤ C(d,Λ) ‖u‖_{\underline L^{(d+1)/d}(Q⁻)}` with
`Q⁻_* = B_{3/8} × (-11/16,-1/2)`, `Q⁻ = B_{1/2} × (-3/4,-1/2)`; the exponent is written as
`q(d+2)/d` with `q = (d+1)/(d+2)`, as in the weak Harnack inequality. -/
theorem parabolic_local_max (d : ℕ) (hd : 0 < d) (Lam : ℝ) (hLam : 1 ≤ Lam) (q : ℝ)
    (hq : q = ((d : ℝ) + 1) / ((d : ℝ) + 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ParCoeffField d),
      IsParabolicCoeff 1 Lam a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
      ∀ u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
      IsParabolicWeakSolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u →
      (∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)), 0 ≤ u.toFun z) →
      essSup (fun z => ENNReal.ofReal (u.toFun z))
          (volume.restrict (euclideanBall (0 : Vec d) (3 / 8) ×ˢ Ioo (-11 / 16 : ℝ) (-1 / 2))) ≤
        ENNReal.ofReal C *
          ((volume (euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioo (-3 / 4 : ℝ) (-1 / 2)))⁻¹ *
            ∫⁻ z in euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioo (-3 / 4 : ℝ) (-1 / 2),
              ENNReal.ofReal (u.toFun z) ^ (q * ((d : ℝ) + 2) / d)) ^
            (1 / (q * ((d : ℝ) + 2) / d)) := by
  obtain ⟨C₀, hC₀, hstep⟩ := power_step d hd
  exact parabolic_local_max_of_powerStep d hd hC₀ hstep Lam hLam q hq

end PDE.Parabolic.LocalMax
