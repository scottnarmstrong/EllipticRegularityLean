module

public import EllipticRegularity.Ch4.GreenFunction.Riesz

/-!
# Weak limits of bounded sequences in `L²(U)` tested against smooth functions

Smooth compactly supported functions are dense in `L²(U)` (their orthogonal complement is trivial
by the fundamental lemma of the calculus of variations).  Hence a sequence bounded in `L²(U)`
whose pairings with all such test functions converge has convergent pairings with every
`f ∈ L²(U)`; by the Riesz representation theorem it has a weak limit in `L²(U)`.
-/

@[expose] public section

open scoped Topology ENNReal InnerProductSpace

namespace PDE.Ch4Green

open MeasureTheory PDE Filter

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A bounded sequence whose inner products converge on a dense submodule has convergent inner
products with every vector. -/
theorem exists_tendsto_inner_of_dense {H : ℕ → E} {M : ℝ} (hM : ∀ n, ‖H n‖ ≤ M)
    {K : Submodule ℝ E} (hK : K.topologicalClosure = ⊤)
    (hconv : ∀ F ∈ K, ∃ L : ℝ, Tendsto (fun n => ⟪H n, F⟫_ℝ) atTop (𝓝 L)) (F : E) :
    ∃ L : ℝ, Tendsto (fun n => ⟪H n, F⟫_ℝ) atTop (𝓝 L) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hF : F ∈ closure (K : Set E) := by
    rw [← Submodule.topologicalClosure_coe, hK]; trivial
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.2 fun ε hε => ?_)
  obtain ⟨F', hF'K, hdist⟩ := Metric.mem_closure_iff.1 hF (ε / (4 * (M + 1)))
    (by positivity)
  obtain ⟨L, hL⟩ := hconv F' hF'K
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff'.1 hL.cauchySeq) (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hb : ∀ m, |⟪H m, F⟫_ℝ - ⟪H m, F'⟫_ℝ| ≤ M * (ε / (4 * (M + 1))) := by
    intro m
    rw [← inner_sub_right]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [← dist_eq_norm]
    exact mul_le_mul (hM m) hdist.le dist_nonneg hM0
  have hMε : M * (ε / (4 * (M + 1))) < ε / 4 := by
    rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h1 := hN n hn
  rw [Real.dist_eq] at h1 ⊢
  have e1 := hb n
  have e2 := hb N
  have a1 := abs_le.1 e1
  have a2 := abs_le.1 e2
  have a3 := abs_lt.1 h1
  rw [abs_lt]
  constructor <;> linarith

end Hilbert

variable {d : ℕ}

/-- The `L²(U)` pairing as an integral. -/
theorem inner_toLp_eq_integral {U : Set (Vec d)} {f g : Vec d → ℝ} (hf : MemL2On U f)
    (hg : MemL2On U g) :
    ⟪hf.toLp f, hg.toLp g⟫_ℝ = ∫ x in U, f x * g x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  simp only [RCLike.inner_apply', conj_trivial, h1, h2]

/-- Cauchy–Schwarz for the `L²(U)` pairing. -/
theorem abs_integral_mul_le {U : Set (Vec d)} {f g : Vec d → ℝ} (hf : MemL2On U f)
    (hg : MemL2On U g) :
    |∫ x in U, f x * g x| ≤
      (eLpNorm f 2 (volumeOn U)).toReal * (eLpNorm g 2 (volumeOn U)).toReal := by
  rw [← inner_toLp_eq_integral hf hg]
  refine (abs_real_inner_le_norm _ _).trans (le_of_eq ?_)
  rw [Lp.norm_toLp, Lp.norm_toLp]

/-- A smooth compactly supported function is in `L²(U)`. -/
theorem memL2On_of_contDiff {U : Set (Vec d)} {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) : MemL2On U ψ :=
  (hψ.continuous.memLp_of_hasCompactSupport hc).restrict U

/-- **Fundamental lemma in `L²(U)`**: an `L²(U)` function orthogonal to all smooth compactly
supported test functions in `U` vanishes a.e. on `U`. -/
theorem ae_eq_zero_of_forall_test {U : Set (Vec d)} (hU : IsOpen U) {f : Vec d → ℝ}
    (hf : MemL2On U f)
    (h : ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ x in U, ψ x * f x = 0) :
    f =ᵐ[volumeOn U] 0 := by
  have hloc : LocallyIntegrableOn f U volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hf.locallyIntegrable one_le_two)
  have := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgc hgU => by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U)]
    · simpa [smul_eq_mul] using h g hg hgc hgU
    · intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun h' => hx (hgU h')), zero_smul]
  exact (ae_restrict_iff' hU.measurableSet).2 this

/-- **Weak convergence from test functions.**  A sequence bounded in `L²(U)` whose pairings with
all smooth compactly supported test functions converge has a weak limit in `L²(U)`. -/
theorem exists_weakLimit_of_test {U : Set (Vec d)} (hU : IsOpen U) {h : ℕ → Vec d → ℝ}
    (hh : ∀ n, MemL2On U (h n)) {M : ℝ} (hM : ∀ n, (eLpNorm (h n) 2 (volumeOn U)).toReal ≤ M)
    (htest : ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∃ L : ℝ, Tendsto (fun n => ∫ x in U, h n x * ψ x) atTop (𝓝 L)) :
    ∃ F : Vec d → ℝ, MemL2On U F ∧ ∀ f : Vec d → ℝ, MemL2On U f →
      Tendsto (fun n => ∫ x in U, h n x * f x) atTop (𝓝 (∫ x in U, F x * f x)) := by
  set E := Lp ℝ 2 (volumeOn U)
  let H : ℕ → E := fun n => (hh n).toLp (h n)
  have hHnorm : ∀ n, ‖H n‖ ≤ M := fun n => by
    simp only [H]
    rw [Lp.norm_toLp]
    exact hM n
  -- the span of test classes
  let T : Set E := {F | ∃ ψ : Vec d → ℝ, ∃ (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ), tsupport ψ ⊆ U ∧ F = (memL2On_of_contDiff hψ hc).toLp ψ}
  let K := Submodule.span ℝ T
  have hKorth : Kᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro F hF
    rw [Submodule.mem_orthogonal] at hF
    have hzero : (⇑F : Vec d → ℝ) =ᵐ[volumeOn U] 0 := by
      refine ae_eq_zero_of_forall_test hU (Lp.memLp F) fun ψ hψ hc hsub => ?_
      have := hF _ (Submodule.subset_span ⟨ψ, hψ, hc, hsub, rfl⟩)
      rw [← this, L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [(memL2On_of_contDiff (U := U) hψ hc).coeFn_toLp] with x hx
      simp only [RCLike.inner_apply', conj_trivial, hx]
    exact (Lp.eq_zero_iff_ae_eq_zero).2 hzero
  have hK : K.topologicalClosure = ⊤ := Submodule.topologicalClosure_eq_top_iff.2 hKorth
  let V : Submodule ℝ E :=
    { carrier := {F | ∃ L : ℝ, Tendsto (fun n => ⟪H n, F⟫_ℝ) atTop (𝓝 L)}
      add_mem' := by
        rintro F F' ⟨L1, hL1⟩ ⟨L2, hL2⟩
        exact ⟨L1 + L2, (hL1.add hL2).congr fun n => (inner_add_right _ _ _).symm⟩
      zero_mem' := ⟨0, (tendsto_const_nhds (x := (0 : ℝ))).congr fun n =>
        (inner_zero_right _).symm⟩
      smul_mem' := by
        rintro c F ⟨L1, hL1⟩
        exact ⟨c * L1, (hL1.const_mul c).congr fun n => (real_inner_smul_right _ _ _).symm⟩ }
  have hTV : T ⊆ V := by
    rintro F ⟨ψ, hψ, hc, hsub, rfl⟩
    obtain ⟨L, hL⟩ := htest ψ hψ hc hsub
    refine ⟨L, hL.congr fun n => ?_⟩
    exact (inner_toLp_eq_integral (hh n) (memL2On_of_contDiff hψ hc)).symm
  have hconv : ∀ F ∈ K, ∃ L : ℝ, Tendsto (fun n => ⟪H n, F⟫_ℝ) atTop (𝓝 L) :=
    fun F hF => (Submodule.span_le.2 hTV) hF
  have hall : ∀ f : Vec d → ℝ, MemL2On U f →
      ∃ L : ℝ, Tendsto (fun n => ∫ x in U, h n x * f x) atTop (𝓝 L) := by
    intro f hf
    obtain ⟨L, hL⟩ := exists_tendsto_inner_of_dense hHnorm hK hconv (hf.toLp f)
    exact ⟨L, hL.congr fun n => inner_toLp_eq_integral (hh n) hf⟩
  obtain ⟨F, -, hFL, hFlim⟩ := exists_rep_of_tendsto_integral (μ := volumeOn U) hh hall
    (K := M) fun f hf L hL => by
      refine le_of_tendsto' hL.abs fun n => ?_
      exact (abs_integral_mul_le (hh n) hf).trans
        (mul_le_mul_of_nonneg_right (hM n) ENNReal.toReal_nonneg)
  exact ⟨F, hFL, hFlim⟩

end PDE.Ch4Green
