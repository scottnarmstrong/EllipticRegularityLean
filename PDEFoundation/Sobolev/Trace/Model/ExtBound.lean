module

public import PDEFoundation.Sobolev.Trace.Model.ExtIntegral

/-!
# The `W^{1,p}` bound for the extension (measurable data)

Steps 1-3 of the proof of the surjectivity of the trace: for a measurable locally integrable `g`
the energy of `E g` on the half-space is bounded by `C (‖g‖_p^p + [g]^p)`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {n : ℕ}

theorem restrict_upperHalf (n : ℕ) :
    (volume : Measure (Vec n × ℝ)).restrict (upperHalf n) =
      (volume : Measure (Vec n)).prod ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))) := by
  rw [upperHalf, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

theorem lintegral_psi_part (p : ℝ) {g : Vec n → ℝ} (hgm : Measurable g) (C₂ : ℝ) :
    ∫⁻ x, ∫⁻ t in Ioi (0 : ℝ), (Ioc (0 : ℝ) 1).indicator
        (fun t => ENNReal.ofReal C₂ * extPsi n p g x t) t ≤ ENNReal.ofReal C₂ * ∫⁻ y, ENNReal.ofReal (|g y| ^ p) := by
  have hmeas : Measurable (Function.uncurry fun (x : Vec n) (t : ℝ) =>
      (Ioc (0 : ℝ) 1).indicator (fun t => ENNReal.ofReal C₂ * extPsi n p g x t) t) := by
    have : Measurable ({q : Vec n × ℝ | q.2 ∈ Ioc (0 : ℝ) 1}.indicator
        fun q => ENNReal.ofReal C₂ * extPsi n p g q.1 q.2) :=
      Measurable.indicator (measurable_const.mul (measurable_extPsi p hgm))
        (measurableSet_Ioc.preimage measurable_snd)
    convert this using 1
    funext q
    change (Ioc (0 : ℝ) 1).indicator (fun t => ENNReal.ofReal C₂ * extPsi n p g q.1 t) q.2 = _
    by_cases h : q.2 ∈ Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show q ∈ {q : Vec n × ℝ | q.2 ∈ Ioc (0 : ℝ) 1} from h)]
    · rw [Set.indicator_of_notMem h,
        Set.indicator_of_notMem (show q ∉ {q : Vec n × ℝ | q.2 ∈ Ioc (0 : ℝ) 1} from h)]
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  calc ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, (Ioc (0 : ℝ) 1).indicator (fun t => ENNReal.ofReal C₂ * extPsi n p g x t) t
      = ∫⁻ t in Ioi (0 : ℝ), (Ioc (0 : ℝ) 1).indicator
          (fun _ => ENNReal.ofReal C₂ * ∫⁻ y, ENNReal.ofReal (|g y| ^ p)) t := by
        refine lintegral_congr fun t => ?_
        by_cases h : t ∈ Ioc (0 : ℝ) 1
        · simp only [Set.indicator_of_mem h]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_extPsi p hgm h.1]
        · simp [h]
    _ ≤ ∫⁻ t, (Ioc (0 : ℝ) 1).indicator
          (fun _ => ENNReal.ofReal C₂ * ∫⁻ y, ENNReal.ofReal (|g y| ^ p)) t := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal C₂ * ∫⁻ y, ENNReal.ofReal (|g y| ^ p) := by
        rw [lintegral_indicator_const measurableSet_Ioc, Real.volume_Ioc]
        simp

theorem enn_final (a b G F : ℝ≥0∞) : a * F + b * G ≤ (a + b) * (G + F) :=
  calc a * F + b * G ≤ (a * F + a * G) + (b * G + b * F) :=
        add_le_add le_self_add le_self_add
    _ = (a + b) * (G + F) := by ring

theorem modelExt_bound_aux {p : ℝ} (hp : 1 < p) (n : ℕ) :
    ∃ C : ℝ≥0, ∀ g : Vec n → ℝ, Measurable g → LocallyIntegrable g volume →
      ∫⁻ z in upperHalf n, (ENNReal.ofReal (|modelExt n g z| ^ p) +
        ENNReal.ofReal (modelGradNorm (modelExt n g) z ^ p)) ≤
        C * ((∫⁻ x', ENNReal.ofReal (|g x'| ^ p)) + flatGagliardo n ((n : ℝ) + p - 1) p g) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hpt⟩ := exists_pointwise_bound hp n
  have hq : 0 < (n : ℝ) + p - 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  refine ⟨(C₁ * (1 / ((n : ℝ) + p - 1)) + C₂).toNNReal, ?_⟩
  intro g hgm hg
  rw [restrict_upperHalf n]
  refine (lintegral_prod_le _).trans ?_
  have hm1 : ∀ x : Vec n, Measurable fun t : ℝ => ENNReal.ofReal C₁ * extPhi n p g x t :=
    fun x => measurable_const.mul ((measurable_extPhi p hgm).comp measurable_prodMk_left)
  have hm2 : Measurable fun x : Vec n =>
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal C₁ * extPhi n p g x t :=
    (measurable_const.mul (measurable_extPhi p hgm)).lintegral_prod_right'
      (ν := (volume : Measure ℝ).restrict (Ioi (0 : ℝ)))
  calc ∫⁻ x, ∫⁻ t in Ioi (0 : ℝ), (ENNReal.ofReal (|modelExt n g (x, t)| ^ p) +
          ENNReal.ofReal (modelGradNorm (modelExt n g) (x, t) ^ p))
      ≤ ∫⁻ x, ∫⁻ t in Ioi (0 : ℝ), (ENNReal.ofReal C₁ * extPhi n p g x t +
          (Ioc (0 : ℝ) 1).indicator (fun t => ENNReal.ofReal C₂ * extPsi n p g x t) t) := by
        refine lintegral_mono fun x => setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        refine (hpt g hgm hg x t ht).trans ?_
        by_cases h : t ∈ Ioc (0 : ℝ) 1
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
          simp
    _ = ∫⁻ x, ((∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal C₁ * extPhi n p g x t) +
          ∫⁻ t in Ioi (0 : ℝ), (Ioc (0 : ℝ) 1).indicator
            (fun t => ENNReal.ofReal C₂ * extPsi n p g x t) t) :=
        lintegral_congr fun x => lintegral_add_left (hm1 x) _
    _ = (∫⁻ x, ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal C₁ * extPhi n p g x t) +
          ∫⁻ x, ∫⁻ t in Ioi (0 : ℝ), (Ioc (0 : ℝ) 1).indicator
            (fun t => ENNReal.ofReal C₂ * extPsi n p g x t) t :=
        lintegral_add_left hm2 _
    _ ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal (1 / ((n : ℝ) + p - 1)) *
            flatGagliardo n ((n : ℝ) + p - 1) p g) +
          ENNReal.ofReal C₂ * ∫⁻ y, ENNReal.ofReal (|g y| ^ p) := by
        refine add_le_add ?_ (lintegral_psi_part p hgm C₂)
        calc ∫⁻ x, ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal C₁ * extPhi n p g x t
            = ∫⁻ x, ENNReal.ofReal C₁ * ∫⁻ t in Ioi (0 : ℝ), extPhi n p g x t :=
              lintegral_congr fun x => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
          _ ≤ ∫⁻ x, ENNReal.ofReal C₁ * (ENNReal.ofReal (1 / ((n : ℝ) + p - 1)) *
                ∫⁻ y, ENNReal.ofReal
                  (|g x - g y| ^ p / vecEuclideanNorm (x - y) ^ ((n : ℝ) + p - 1))) :=
              lintegral_mono fun x => mul_le_mul_right (lintegral_Ioi_extPhi_le hp hgm x) _
          _ = _ := by
              unfold flatGagliardo
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
                lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := by
        have h1 : ENNReal.ofReal C₁ * ENNReal.ofReal (1 / ((n : ℝ) + p - 1)) =
            ENNReal.ofReal (C₁ * (1 / ((n : ℝ) + p - 1))) :=
          (ENNReal.ofReal_mul hC₁).symm
        have h2 : ((C₁ * (1 / ((n : ℝ) + p - 1)) + C₂).toNNReal : ℝ≥0∞) =
            ENNReal.ofReal (C₁ * (1 / ((n : ℝ) + p - 1))) + ENNReal.ofReal C₂ := by
          rw [← ENNReal.ofReal_add (mul_nonneg hC₁ (by positivity)) hC₂]
          rfl
        rw [h2, ← mul_assoc, h1]
        exact enn_final _ _ _ _

end PDE.TraceLane
