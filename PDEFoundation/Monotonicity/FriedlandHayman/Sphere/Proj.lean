module

public import PDEFoundation.Monotonicity.FriedlandHayman.Sphere.ProjSetup
public import PDEFoundation.Monotonicity.FriedlandHayman.Sphere.ProjQuadrant

/-!
# Friedland--Hayman: the projection formula for sphere integrals

For `D = n + N` with `n, N ≥ 1` and a bounded measurable `G` on `Vec n`,
`∫_{S^{D-1}} G(x') dσ = σ(S^{N-1}) ∫_0^{π/2} sin^{N-1} θ · (∫_{∂B_{cos θ}} G dσ) dθ`.
The proof computes `∫_{ℝ^D} exp(-|x|²/2) G(x'/|x|) dx` in two ways: polar coordinates in `ℝ^D`,
and Fubini over `ℝ^n × ℝ^N` followed by polar coordinates in each factor and then in the
`(r, ρ)`-quarter plane.
-/

@[expose] public section

open MeasureTheory

namespace PDE.FHLane

noncomputable section

section Fubini

variable {n N : ℕ} (G : Vec n → ℝ)

/-- The kernel after Fubini. -/
def kap (a : HilbertVec n) (t : ℝ) : ℝ :=
  Real.exp (-((‖a‖ ^ 2 + t ^ 2) / 2)) * G ((Real.sqrt (‖a‖ ^ 2 + t ^ 2))⁻¹ • a.toVec)

/-- The weighted integrand on the product. -/
def prodKer (N : ℕ) (a : HilbertVec n) (b : HilbertVec N) : ℝ := kap G a ‖b‖

variable {G}

theorem homExt_splitEquiv (a : HilbertVec n) (b : HilbertVec N) :
    homExt (fun z : HilbertVec (n + N) => G (projFst z.toVec)) (splitEquiv n N (a, b)) =
      prodKer (N := N) G a b := by
  have hn : ‖splitEquiv n N (a, b)‖ = Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    rw [← norm_splitEquiv_sq n N (a, b), Real.sqrt_sq (norm_nonneg _)]
  unfold homExt prodKer kap
  rw [hn]
  have hsq : Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 :=
    Real.sq_sqrt (by positivity)
  rw [hsq]
  congr 2
  show G (projFst ((Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2))⁻¹ • (splitEquiv n N (a, b)).toVec)) = _
  congr 1
  ext i
  have h := congrFun (projFst_splitEquiv n N (a, b)) i
  simp only [projFst, Pi.smul_apply, smul_eq_mul] at h ⊢
  rw [h]


theorem measurable_toVec {d : ℕ} : Measurable (HilbertVec.toVec : HilbertVec d → Vec d) :=
  continuous_toVec.measurable

theorem measurable_kap (hG : Measurable G) :
    Measurable (fun p : HilbertVec n × ℝ => kap G p.1 p.2) := by
  unfold kap
  have hv : Measurable (fun p : HilbertVec n × ℝ =>
      (Real.sqrt (‖p.1‖ ^ 2 + p.2 ^ 2))⁻¹ • p.1.toVec) := by
    refine Measurable.fun_smul ?_ (measurable_toVec.comp measurable_fst)
    fun_prop
  exact Measurable.mul (by fun_prop) (hG.comp hv)

theorem abs_kap_le (a : HilbertVec n) (t : ℝ) {C : ℝ} (hb : ∀ y, |G y| ≤ C) :
    |kap G a t| ≤ C * Real.exp (-(t ^ 2 / 2)) := by
  unfold kap
  rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
  have h1 : Real.exp (-((‖a‖ ^ 2 + t ^ 2) / 2)) ≤ Real.exp (-(t ^ 2 / 2)) := by
    apply Real.exp_le_exp.2
    have : 0 ≤ ‖a‖ ^ 2 := by positivity
    linarith
  exact mul_le_mul (hb _) h1 (Real.exp_pos _).le ((abs_nonneg _).trans (hb 0))

theorem integral_prodKer_eq [NeZero N] (hG : Measurable G) {C : ℝ} (hb : ∀ y, |G y| ≤ C)
    (a : HilbertVec n) :
    ∫ b : HilbertVec N, prodKer (N := N) G a b =
      sphereArea N * ∫ t in Set.Ioi (0 : ℝ), t ^ (N - 1) * kap G a t := by
  have hint : Integrable (fun b : HilbertVec N => prodKer (N := N) G a b) := by
    refine ((integrable_gauss N).const_mul C).mono' ?_ (ae_of_all _ fun b => ?_)
    · exact ((measurable_kap hG).comp (measurable_const.prodMk measurable_norm)).aestronglyMeasurable
    · exact (abs_kap_le a ‖b‖ hb)
  rw [Internal.integral_eq_integral_Ioi_sphere hint, sphereArea, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) < t := ht
  have h1 : ∀ η : Metric.sphere (0 : HilbertVec N) 1,
      prodKer (N := N) G a (t • (η : HilbertVec N)) = kap G a t := by
    intro η
    have hη : ‖(η : HilbertVec N)‖ = 1 := by simp
    unfold prodKer
    rw [norm_smul, hη, Real.norm_eq_abs, abs_of_pos ht', mul_one]
  simp only [h1, smul_eq_mul, integral_const, smul_eq_mul]
  ring

theorem measurable_projFst : Measurable (projFst : Vec (n + N) → Vec n) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

theorem integrable_prodKer (hG : Measurable G) {C : ℝ} (hb : ∀ y, |G y| ≤ C) :
    Integrable (fun p : HilbertVec n × HilbertVec N => prodKer (N := N) G p.1 p.2)
      (volume.prod volume) := by
  have hH : Measurable (fun z : HilbertVec (n + N) => G (projFst z.toVec)) :=
    hG.comp (measurable_projFst.comp measurable_toVec)
  have h := integrable_homExt hH (fun z => hb _)
  have h2 := ((mp_splitEquiv n N).integrable_comp_emb
    (splitEquiv n N).measurableEmbedding).2 h
  refine h2.congr (ae_of_all _ fun p => ?_)
  exact homExt_splitEquiv p.1 p.2

theorem integral_homExt_split (hG : Measurable G) {C : ℝ} (hb : ∀ y, |G y| ≤ C) :
    ∫ z : HilbertVec (n + N), homExt (fun z : HilbertVec (n + N) => G (projFst z.toVec)) z =
      ∫ a : HilbertVec n, ∫ b : HilbertVec N, prodKer (N := N) G a b := by
  calc _ = ∫ p : HilbertVec n × HilbertVec N,
        homExt (fun z : HilbertVec (n + N) => G (projFst z.toVec)) (splitEquiv n N p) :=
        ((mp_splitEquiv n N).integral_comp' _).symm
    _ = ∫ p : HilbertVec n × HilbertVec N, prodKer (N := N) G p.1 p.2 :=
        integral_congr_ae (ae_of_all _ fun p => homExt_splitEquiv p.1 p.2)
    _ = _ := integral_prod _ (integrable_prodKer hG hb)

/-- The spherical average of `G` against dilations. -/
def gfun (G : Vec n → ℝ) (c : ℝ) : ℝ :=
  ∫ ω : Metric.sphere (0 : HilbertVec n) 1, G (c • (ω : HilbertVec n).toVec)
    ∂(Internal.sphereMeasure n)


theorem kap_smul {s : ℝ} (hs : 0 < s) (ω : Metric.sphere (0 : HilbertVec n) 1) (t : ℝ) :
    kap G (s • (ω : HilbertVec n)) t =
      Real.exp (-((s ^ 2 + t ^ 2) / 2)) * G (wfac s t • (ω : HilbertVec n).toVec) := by
  have hω : ‖(ω : HilbertVec n)‖ = 1 := by simp
  unfold kap wfac
  rw [norm_smul, hω, Real.norm_eq_abs, abs_of_pos hs, mul_one]
  congr 2
  rw [mul_smul]
  rfl

theorem integral_phi_sphere [NeZero N] (hG : Measurable G) {C : ℝ} (hb : ∀ y, |G y| ≤ C)
    {s : ℝ} (hs : 0 < s) :
    ∫ ω : Metric.sphere (0 : HilbertVec n) 1,
        (∫ b : HilbertVec N, prodKer (N := N) G (s • (ω : HilbertVec n)) b)
          ∂(Internal.sphereMeasure n) =
      sphereArea N * ∫ t in Set.Ioi (0 : ℝ),
        t ^ (N - 1) * (Real.exp (-((s ^ 2 + t ^ 2) / 2)) * gfun G (wfac s t)) := by
  simp_rw [integral_prodKer_eq hG hb]
  rw [integral_const_mul]
  congr 1
  simp_rw [kap_smul hs]
  have hmeas : Measurable (fun q : Metric.sphere (0 : HilbertVec n) 1 × ℝ =>
      q.2 ^ (N - 1) * (Real.exp (-((s ^ 2 + q.2 ^ 2) / 2)) *
        G (wfac s q.2 • (q.1 : HilbertVec n).toVec))) := by
    have hw : Measurable (wfac s) := by unfold wfac; fun_prop
    have hv : Measurable (fun q : Metric.sphere (0 : HilbertVec n) 1 × ℝ =>
        wfac s q.2 • (q.1 : HilbertVec n).toVec) :=
      Measurable.fun_smul (hw.comp measurable_snd)
        (measurable_toVec.comp (measurable_subtype_coe.comp measurable_fst))
    exact Measurable.mul (by fun_prop) (Measurable.mul (by fun_prop) (hG.comp hv))
  have hint : Integrable (Function.uncurry fun (ω : Metric.sphere (0 : HilbertVec n) 1) (t : ℝ) =>
      t ^ (N - 1) * (Real.exp (-((s ^ 2 + t ^ 2) / 2)) * G (wfac s t • (ω : HilbertVec n).toVec)))
      ((Internal.sphereMeasure n).prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    have hbd := Integrable.mul_prod (μ := Internal.sphereMeasure n)
      (ν := volume.restrict (Set.Ioi (0 : ℝ))) (integrable_const (1 : ℝ))
      ((integrableOn_radialGauss N).const_mul C)
    have h2 : ∀ᵐ q ∂((Internal.sphereMeasure n).prod (volume.restrict (Set.Ioi (0 : ℝ)))),
        q.2 ∈ Set.Ioi (0 : ℝ) :=
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)
    refine hbd.mono' hmeas.aestronglyMeasurable (h2.mono fun q hq => ?_)
    have hq' : (0 : ℝ) < q.2 := hq
    simp only [one_mul, Real.norm_eq_abs]
    change |q.2 ^ (N - 1) * (Real.exp (-((s ^ 2 + q.2 ^ 2) / 2)) *
        G (wfac s q.2 • (q.1 : HilbertVec n).toVec))| ≤ _
    rw [abs_mul, abs_mul, abs_of_pos (pow_pos hq' _), abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp (-((s ^ 2 + q.2 ^ 2) / 2)) ≤ Real.exp (-(q.2 ^ 2 / 2)) := by
      apply Real.exp_le_exp.2
      have : 0 ≤ s ^ 2 := by positivity
      linarith
    have h3 := mul_le_mul (hb ((wfac s q.2) • (q.1 : HilbertVec n).toVec)) h1 (Real.exp_pos _).le
      ((abs_nonneg _).trans (hb 0))
    have h4 := mul_le_mul_of_nonneg_left h3 (pow_pos hq' (N - 1)).le
    calc _ = q.2 ^ (N - 1) * (|G (wfac s q.2 • (q.1 : HilbertVec n).toVec)| *
          Real.exp (-((s ^ 2 + q.2 ^ 2) / 2))) := by ring
      _ ≤ _ := h4
      _ = _ := by ring
  rw [integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [integral_const_mul]
  rfl

theorem measurable_gfun (hG : Measurable G) : Measurable (gfun G) := by
  have hm : Measurable (fun p : ℝ × Metric.sphere (0 : HilbertVec n) 1 =>
      G (p.1 • (p.2 : HilbertVec n).toVec)) :=
    hG.comp (Measurable.fun_smul measurable_fst
      (measurable_toVec.comp (measurable_subtype_coe.comp measurable_snd)))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem abs_gfun_le {C : ℝ} (hb : ∀ y, |G y| ≤ C) (c : ℝ) :
    |gfun G c| ≤ C * (Internal.sphereMeasure n).real Set.univ := by
  have := norm_integral_le_of_norm_le_const (μ := Internal.sphereMeasure n)
    (f := fun ω : Metric.sphere (0 : HilbertVec n) 1 => G (c • (ω : HilbertVec n).toVec))
    (C := C) (ae_of_all _ fun ω => by simpa using hb _)
  simpa [gfun] using this

theorem integrableOn_quadIntegrand (hG : Measurable G) {C : ℝ} (hb : ∀ y, |G y| ≤ C) (a b : ℕ) :
    IntegrableOn (quadIntegrand a b (gfun (n := n) G)) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
  set M : ℝ := C * (Internal.sphereMeasure n).real Set.univ with hM
  have hmeas : Measurable (quadIntegrand a b (gfun (n := n) G)) := by
    unfold quadIntegrand wfac
    have := measurable_gfun hG
    fun_prop
  have hA : ∀ k : ℕ, IntegrableOn (fun r : ℝ => r ^ k * Real.exp (-(r ^ 2 / 2))) (Set.Ioi 0) := by
    intro k
    simpa using integrableOn_radialGauss (k + 1)
  have hbd : Integrable (fun z : ℝ × ℝ => (M * (z.1 ^ a * Real.exp (-(z.1 ^ 2 / 2)))) *
      (z.2 ^ b * Real.exp (-(z.2 ^ 2 / 2))))
      ((volume.prod volume : Measure (ℝ × ℝ)).restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))) := by
    rw [← Measure.prod_restrict]
    exact Integrable.mul_prod ((hA a).const_mul M) (hA b)
  rw [IntegrableOn, Measure.volume_eq_prod]
  refine hbd.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with z hz
  obtain ⟨hz1, hz2⟩ : 0 < z.1 ∧ 0 < z.2 := hz
  have hg := abs_gfun_le (n := n) hb (wfac z.1 z.2)
  have he : Real.exp (-((z.1 ^ 2 + z.2 ^ 2) / 2)) =
      Real.exp (-(z.1 ^ 2 / 2)) * Real.exp (-(z.2 ^ 2 / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold quadIntegrand
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (pow_pos hz1 _),
    abs_of_pos (pow_pos hz2 _), abs_of_pos (Real.exp_pos _), he]
  have h2 := mul_le_mul_of_nonneg_left hg
    (mul_nonneg (mul_nonneg (pow_pos hz1 a).le (pow_pos hz2 b).le)
      (mul_pos (Real.exp_pos (-(z.1 ^ 2 / 2))) (Real.exp_pos (-(z.2 ^ 2 / 2)))).le)
  calc _ = (z.1 ^ a * z.2 ^ b * (Real.exp (-(z.1 ^ 2 / 2)) * Real.exp (-(z.2 ^ 2 / 2)))) *
        |gfun G (wfac z.1 z.2)| := by ring
    _ ≤ _ := h2
    _ = _ := by rw [hM]; ring


theorem integral_outer [NeZero n] [NeZero N] (hG : Measurable G) {C : ℝ} (hb : ∀ y, |G y| ≤ C) :
    ∫ a : HilbertVec n, ∫ b : HilbertVec N, prodKer (N := N) G a b =
      sphereArea N * ∫ z in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ),
        quadIntegrand (n - 1) (N - 1) (gfun (n := n) G) z := by
  have hφ : Integrable (fun a : HilbertVec n => ∫ b : HilbertVec N, prodKer (N := N) G a b) :=
    (integrable_prodKer hG hb).integral_prod_left
  rw [Internal.integral_eq_integral_Ioi_sphere hφ]
  have hs : ∀ s ∈ Set.Ioi (0 : ℝ),
      s ^ (n - 1) • ∫ ω : Metric.sphere (0 : HilbertVec n) 1,
          (∫ b : HilbertVec N, prodKer (N := N) G (s • (ω : HilbertVec n)) b)
            ∂(Internal.sphereMeasure n) =
        sphereArea N * ∫ t in Set.Ioi (0 : ℝ),
          quadIntegrand (n - 1) (N - 1) (gfun (n := n) G) (s, t) := by
    intro s hs
    rw [integral_phi_sphere hG hb hs, smul_eq_mul, ← mul_assoc, mul_comm (s ^ (n - 1)), mul_assoc,
      ← integral_const_mul]
    congr 1
  rw [setIntegral_congr_fun measurableSet_Ioi hs, integral_const_mul, Measure.volume_eq_prod,
    setIntegral_prod _ (by simpa [Measure.volume_eq_prod] using
      integrableOn_quadIntegrand hG hb (n - 1) (N - 1))]

/-- **Projection formula.**  For `D = n + N` with `n, N ≥ 1` and `G` bounded measurable,
`∫_{S^{D-1}} G(x') dσ = σ(S^{N-1}) ∫_0^{π/2} sin^{N-1} θ · (∫_{∂B_{cos θ}} G dσ) dθ`. -/
theorem sphereIntegral_comp_projFst [NeZero n] [NeZero N] (G : Vec n → ℝ)
    (hG : Measurable G) (hb : ∃ C, ∀ y, |G y| ≤ C) :
    sphereIntegral (0 : Vec (n + N)) 1 (fun x => G (projFst x)) =
      sphereArea N * ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.sin θ ^ (N - 1) * sphereIntegral (0 : Vec n) (Real.cos θ) G := by
  obtain ⟨C, hb⟩ := hb
  have : NeZero (n + N) := ⟨by have := NeZero.ne n; omega⟩
  set H : HilbertVec (n + N) → ℝ := fun z => G (projFst z.toVec) with hH
  have hHm : Measurable H := hG.comp (measurable_projFst.comp measurable_toVec)
  have h1 := integral_homExt hHm (fun z => hb _)
  have h2 := integral_homExt_split (N := N) hG hb
  have h3 := integral_outer (N := N) hG hb
  have h4 := integral_quadrant (n - 1) (N - 1) (gfun (n := n) G)
  have hexp : n - 1 + (N - 1) + 1 = n + N - 1 := by
    have := NeZero.pos n; have := NeZero.pos N; omega
  rw [hexp] at h4
  change _ = radialGauss (n + N) * _ at h4
  have hL : sphereIntegral (0 : Vec (n + N)) 1 (fun x => G (projFst x)) =
      ∫ ω : Metric.sphere (0 : HilbertVec (n + N)) 1, H ω ∂(Internal.sphereMeasure (n + N)) := by
    simp only [sphereIntegral, one_pow, one_mul, zero_add, one_smul, hH]
    rfl
  have hR : ∫ θ in (0 : ℝ)..(Real.pi / 2),
      Real.sin θ ^ (N - 1) * sphereIntegral (0 : Vec n) (Real.cos θ) G =
        ∫ θ in Set.Ioo 0 (Real.pi / 2), angProfile (n - 1) (N - 1) (gfun (n := n) G) θ := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
    simp only [sphereIntegral, zero_add, angProfile, gfun, Internal.sphereMeasure]
  rw [hL, hR]
  have hpos := radialGauss_pos (n + N)
  have key := h1
  rw [h2, h3, h4] at key
  refine mul_left_cancel₀ hpos.ne' ?_
  rw [← key]
  ring
end Fubini

end

end PDE.FHLane
