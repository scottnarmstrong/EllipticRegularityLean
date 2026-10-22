module

public import EllipticRegularity.Ch4.GreenFunction.Tail
public import EllipticRegularity.Ch4.GreenFunction.LayerCake
public import EllipticRegularity.Ch4.GreenFunction.Positivity

/-!
# Stampacchia's bound for the Green function (Step 5 of Proposition 4.40, part (ii))

`∫_E G ≤ C₀ |E|^{2/d}` for every measurable `E ⊆ B_R`, with `C₀ = C₀(d)` independent of `Λ` and
`R`; hence `G ∈ L¹(B_R)` and `|{G > t}| ≤ (C₀/t)^{d/(d-2)}`.
-/

@[expose] public section

open scoped Topology ENNReal

namespace PDE.Ch4Green

open MeasureTheory PDE Filter

variable {d : ℕ}

/-- The layer-cake bound for the approximate Green functions. -/
theorem stampacchia_approx (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ {Λ R : ℝ} {a : CoeffField d} (S : ApproxSetting d Λ R a) (n : ℕ)
      (E : Set (Vec d)), MeasurableSet E → E ⊆ euclideanBall (0 : Vec d) R →
      ∫⁻ x in E, ENNReal.ofReal ((S.G n).toH1Function.toFun x) ≤
        ENNReal.ofReal (C₀ * (volume E).toReal ^ ((2 : ℝ) / d)) := by
  obtain ⟨A, hA, hlevel⟩ := volume_level_le (d := d) hd
  have hd2 : (2 : ℝ) < d := by exact_mod_cast (show 2 < d by omega)
  set γ : ℝ := (d : ℝ) / ((d : ℝ) - 2) with hγ
  have hγ1 : 1 < γ := by rw [hγ, one_lt_div (by linarith)]; linarith
  have hexp : 1 - 1 / γ = (2 : ℝ) / d := by
    rw [hγ]; field_simp; ring
  refine ⟨γ / (γ - 1) * A ^ (1 / γ),
    mul_pos (div_pos (by linarith) (by linarith)) (Real.rpow_pos_of_pos hA _), ?_⟩
  intro Λ R a S n E hE hEB
  set f : Vec d → ℝ := fun x => max ((S.G n).toH1Function.toFun x) 0
  have hofReal : ∀ x, ENNReal.ofReal ((S.G n).toH1Function.toFun x) = ENNReal.ofReal (f x) := by
    intro x
    simp only [f]
    rcases le_total ((S.G n).toH1Function.toFun x) 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
    · rw [max_eq_left h]
  simp_rw [hofReal]
  have hfin : volume E ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_euclideanBall_ne_top _ S.hR.le) (measure_mono hEB)
  have hmeas : AEMeasurable f (volume.restrict E) :=
    ((S.G n).toH1Function.memL2.aestronglyMeasurable.aemeasurable.mono_measure
      (Measure.restrict_mono hEB le_rfl)).max aemeasurable_const
  have h := lintegral_ofReal_le_of_tail (ν := volume.restrict E) hmeas
    (Eventually.of_forall fun x => le_max_right _ _)
    (by rwa [Measure.restrict_apply_univ]) hA hγ1 (fun t ht => ?_)
  · rwa [Measure.restrict_apply_univ, hexp] at h
  · rw [Measure.restrict_apply' hE]
    refine le_trans (measure_mono ?_) (hlevel S n t ht)
    intro x ⟨hx, hxE⟩
    refine ⟨hEB hxE, ?_⟩
    have hx' : t < max ((S.G n).toH1Function.toFun x) 0 := hx
    rcases le_total ((S.G n).toH1Function.toFun x) 0 with h | h
    · rw [max_eq_right h] at hx'; linarith
    · rw [max_eq_left h] at hx'; exact hx'.le

namespace ApproxSetting

variable {Λ R : ℝ} {a : CoeffField d}

/-- Stampacchia's bound passes to every nonnegative-approximated Green function. -/
theorem isGreen_lintegral_le (S : ApproxSetting d Λ R a) (hd : 3 ≤ d)
    (hGnn : ∀ n, ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), 0 ≤ (S.G n).toH1Function.toFun x)
    {C₀ : ℝ} (hC₀0 : 0 ≤ C₀)
    (hC₀ : ∀ n (E : Set (Vec d)), MeasurableSet E → E ⊆ euclideanBall (0 : Vec d) R →
      ∫⁻ x in E, ENNReal.ofReal ((S.G n).toH1Function.toFun x) ≤
        ENNReal.ofReal (C₀ * (volume E).toReal ^ ((2 : ℝ) / d)))
    {G : Vec d → ℝ} (hG : IsGreenFunction a R G) (E : Set (Vec d)) (hE : MeasurableSet E)
    (hEB : E ⊆ euclideanBall (0 : Vec d) R) :
    ∫⁻ x in E, ENNReal.ofReal (G x) ≤ ENNReal.ofReal (C₀ * (volume E).toReal ^ ((2 : ℝ) / d)) := by
  have hR := S.hR
  have hGnonneg := S.isGreen_nonneg hd hGnn hG
  have hfinB : volume (euclideanBall (0 : Vec d) R) ≠ ⊤ := volume_euclideanBall_ne_top _ hR.le
  -- Step A: sets away from the pole
  have stepA : ∀ ε : ℝ, 0 < ε → ε < R → ∀ F : Set (Vec d), MeasurableSet F →
      F ⊆ euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε →
      ∫⁻ x in F, ENNReal.ofReal (G x) ≤ ENNReal.ofReal (C₀ * (volume F).toReal ^ ((2 : ℝ) / d)) :=
          by
    intro ε hε hεR F hF hFT
    set T := euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε
    have hTB : T ⊆ euclideanBall (0 : Vec d) R := Set.sdiff_subset
    have hFB : F ⊆ euclideanBall (0 : Vec d) R := hFT.trans hTB
    have hFfin : volume F ≠ ⊤ := ne_top_of_le_ne_top hfinB (measure_mono hFB)
    have hind : MemL2On T (F.indicator (fun _ => (1 : ℝ))) := by
      unfold MemL2On MemLpOn
      refine memLp_indicator_const 2 hF _ (Or.inr ?_)
      rw [Measure.restrict_apply hF]
      exact ne_top_of_le_ne_top hFfin (measure_mono Set.inter_subset_left)
    have hlim := S.weakLimitOn_of_isGreen hd hG hε hεR _ hind
    have key : ∀ h : Vec d → ℝ, ∫ x in euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε,
        h x * F.indicator (fun _ => (1 : ℝ)) x = ∫ x in F, h x := fun h => by
      rw [integral_mul_indicator (T' := euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε)
        hF hFT]
      simp
    simp only [key] at hlim
    have hGF : IntegrableOn G F := by
      have hGT : MemL2On T G := hG.2.1 ε hε hεR
      have : IsFiniteMeasure (volume.restrict T) :=
        ⟨by rw [Measure.restrict_apply_univ]
            exact (ne_top_of_le_ne_top hfinB (measure_mono hTB)).lt_top⟩
      exact (show IntegrableOn G T volume from hGT.integrable one_le_two).mono_set hFT
    have hbound : ∫ x in F, G x ≤ C₀ * (volume F).toReal ^ ((2 : ℝ) / d) := by
      refine le_of_tendsto' hlim fun n => ?_
      have hint : IntegrableOn (S.G n).toH1Function.toFun F := by
        have : IsFiniteMeasure (volume.restrict (euclideanBall (0 : Vec d) R)) :=
          isFiniteMeasure_volumeOn_euclideanBall _ hR.le
        exact (show IntegrableOn _ (euclideanBall (0 : Vec d) R) volume from
          (S.G n).toH1Function.memL2.integrable one_le_two).mono_set hFB
      calc ∫ x in F, (S.G n).toH1Function.toFun x
          ≤ ∫ x in F, max ((S.G n).toH1Function.toFun x) 0 :=
            integral_mono hint hint.pos_part fun x => le_max_left _ _
        _ = (∫⁻ x in F, ENNReal.ofReal ((S.G n).toH1Function.toFun x)).toReal := by
            rw [integral_eq_lintegral_of_nonneg_ae
              (f := fun x => max ((S.G n).toH1Function.toFun x) 0)
              (Eventually.of_forall fun x => le_max_right _ _)
              hint.pos_part.aestronglyMeasurable]
            congr 1
            refine lintegral_congr fun x => ?_
            rcases le_total ((S.G n).toH1Function.toFun x) 0 with h | h
            · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
            · rw [max_eq_left h]
        _ ≤ C₀ * (volume F).toReal ^ ((2 : ℝ) / d) := by
            exact ENNReal.toReal_le_of_le_ofReal
              (mul_nonneg hC₀0 (Real.rpow_nonneg ENNReal.toReal_nonneg _)) (hC₀ n F hF hFB)
    have hGnnF : 0 ≤ᵐ[volume.restrict F] G := ae_restrict_of_ae_restrict_of_subset hFB hGnonneg
    rw [← ofReal_integral_eq_lintegral_ofReal hGF hGnnF]
    exact ENNReal.ofReal_le_ofReal hbound
  -- Step B: exhaustion
  set Ek : ℕ → Set (Vec d) := fun k => E \ euclideanBall (0 : Vec d) (dyadicRadius R k)
  have hEkmono : Monotone Ek := by
    intro j k hjk x hx
    exact ⟨hx.1, fun h => hx.2 (euclideanBall_mono (dyadicRadius_pos hR k).le
      (dyadicRadius_anti hR hjk) h)⟩
  have hunion : E \ {0} ⊆ ⋃ k, Ek k := by
    intro x ⟨hxE, hx0⟩
    obtain ⟨k, hk⟩ := exists_dyadicRadius_le hR (vecEuclideanNorm_pos_iff.mpr hx0)
    refine Set.mem_iUnion.2 ⟨k, hxE, fun hin => ?_⟩
    have := (mem_euclideanBall_iff_vecEuclideanNorm_lt (dyadicRadius_pos hR k)).1 hin
    rw [sub_zero] at this
    linarith
  have hnull : volume ({0} : Set (Vec d)) = 0 := by
    have : NeZero d := ⟨by omega⟩
    exact measure_singleton _
  have hEsub : E ⊆ (⋃ k, Ek k) ∪ {0} := by
    intro x hx
    by_cases h0 : x = 0
    · exact Or.inr h0
    · exact Or.inl (hunion ⟨hx, h0⟩)
  have hEfin : volume E ≠ ⊤ := ne_top_of_le_ne_top hfinB (measure_mono hEB)
  calc ∫⁻ x in E, ENNReal.ofReal (G x)
      ≤ ∫⁻ x in (⋃ k, Ek k) ∪ {0}, ENNReal.ofReal (G x) := lintegral_mono_set hEsub
    _ ≤ (∫⁻ x in ⋃ k, Ek k, ENNReal.ofReal (G x)) + ∫⁻ x in {0}, ENNReal.ofReal (G x) :=
        lintegral_union_le _ _ _
    _ = ⨆ k, ∫⁻ x in Ek k, ENNReal.ofReal (G x) := by
        rw [setLIntegral_measure_zero _ _ hnull, add_zero,
          setLIntegral_iUnion_of_directed _ hEkmono.directed_le]
    _ ≤ ENNReal.ofReal (C₀ * (volume E).toReal ^ ((2 : ℝ) / d)) := by
        refine iSup_le fun k => ?_
        have hlt : dyadicRadius R k < R := by
          unfold dyadicRadius
          rw [div_lt_iff₀ (by positivity)]
          have : (1 : ℝ) < 2 ^ (k + 1) := one_lt_pow₀ (by norm_num) (by omega)
          nlinarith
        refine (stepA _ (dyadicRadius_pos hR k) hlt (Ek k)
          (hE.diff (measurableSet_euclideanBall _ _))
          (fun x hx => ⟨hEB hx.1, hx.2⟩)).trans ?_
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ hC₀0
        apply Real.rpow_le_rpow ENNReal.toReal_nonneg _ (by positivity)
        exact ENNReal.toReal_mono hEfin (measure_mono Set.sdiff_subset)

end ApproxSetting

/-- A nonnegative measurable function with finite integral on `B` is integrable there. -/
theorem integrableOn_of_lintegral_ofReal_lt_top {B : Set (Vec d)} {G : Vec d → ℝ}
    (hGm : Measurable G) (hG0 : ∀ᵐ x ∂(volumeOn B), 0 ≤ G x)
    (hfin : ∫⁻ x in B, ENNReal.ofReal (G x) < ⊤) : IntegrableOn G B :=
  ⟨hGm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hG0).2 hfin⟩

/-- **Weak-type bound** from Stampacchia's estimate: `|{G > t}| ≤ (C₀/t)^{d/(d-2)}`. -/
theorem volume_lt_le_of_lintegral (hd : 3 ≤ d) {B : Set (Vec d)} (hB : MeasurableSet B)
    (hBfin : volume B ≠ ⊤) {G : Vec d → ℝ} (hGm : Measurable G) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hbound : ∀ E : Set (Vec d), MeasurableSet E → E ⊆ B →
      ∫⁻ x in E, ENNReal.ofReal (G x) ≤ ENNReal.ofReal (C₀ * (volume E).toReal ^ ((2 : ℝ) / d)))
    {t : ℝ} (ht : 0 < t) :
    volume {x | x ∈ B ∧ t < G x} ≤ ENNReal.ofReal ((C₀ / t) ^ ((d : ℝ) / ((d : ℝ) - 2))) := by
  set E := {x | x ∈ B ∧ t < G x} with hEdef
  have hEm : MeasurableSet E := hB.inter (measurableSet_lt measurable_const hGm)
  have hEB : E ⊆ B := fun x hx => hx.1
  have hEfin : volume E ≠ ⊤ := ne_top_of_le_ne_top hBfin (measure_mono hEB)
  set m := (volume E).toReal with hm
  have hd2 : (2 : ℝ) < d := by exact_mod_cast (show 2 < d by omega)
  have hlow : ENNReal.ofReal (t * m) ≤ ENNReal.ofReal (C₀ * m ^ ((2 : ℝ) / d)) := by
    calc ENNReal.ofReal (t * m) = ∫⁻ _ in E, ENNReal.ofReal t := by
          rw [setLIntegral_const, ENNReal.ofReal_mul ht.le, hm, ENNReal.ofReal_toReal hEfin]
      _ ≤ ∫⁻ x in E, ENNReal.ofReal (G x) :=
          setLIntegral_mono' hEm fun x hx => ENNReal.ofReal_le_ofReal hx.2.le
      _ ≤ _ := hbound E hEm hEB
  have hineq : t * m ≤ C₀ * m ^ ((2 : ℝ) / d) :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC₀ (Real.rpow_nonneg ENNReal.toReal_nonneg _))).1
      hlow
  rw [← ENNReal.ofReal_toReal hEfin]
  apply ENNReal.ofReal_le_ofReal
  rcases (ENNReal.toReal_nonneg : 0 ≤ m).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact Real.rpow_nonneg (div_nonneg hC₀ ht.le) _
  · have hsplit : m = m ^ ((2 : ℝ) / d) * m ^ (((d : ℝ) - 2) / d) := by
      rw [← Real.rpow_add hpos]
      rw [show (2 : ℝ) / d + ((d : ℝ) - 2) / d = 1 by field_simp; ring, Real.rpow_one]
    have hp : 0 < m ^ ((2 : ℝ) / d) := Real.rpow_pos_of_pos hpos _
    have h1 : m ^ (((d : ℝ) - 2) / d) ≤ C₀ / t := by
      rw [le_div_iff₀ ht]
      have : m ^ ((2 : ℝ) / d) * (m ^ (((d : ℝ) - 2) / d) * t) ≤ m ^ ((2 : ℝ) / d) * C₀ := by
        calc m ^ ((2 : ℝ) / d) * (m ^ (((d : ℝ) - 2) / d) * t)
              = (m ^ ((2 : ℝ) / d) * m ^ (((d : ℝ) - 2) / d)) * t := by ring
          _ = t * m := by rw [← hsplit]; ring
          _ ≤ C₀ * m ^ ((2 : ℝ) / d) := hineq
          _ = m ^ ((2 : ℝ) / d) * C₀ := by ring
      exact le_of_mul_le_mul_left this hp
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hpos.le _) h1
      (div_nonneg (by linarith : (0 : ℝ) ≤ d) (by linarith : (0 : ℝ) ≤ d - 2))
    have hd2' : (d : ℝ) - 2 ≠ 0 := by linarith
    rw [← Real.rpow_mul hpos.le, show ((d : ℝ) - 2) / d * (d / (d - 2)) = 1 by
      field_simp, Real.rpow_one] at h2
    rw [← hm]
    exact h2

end PDE.Ch4Green
