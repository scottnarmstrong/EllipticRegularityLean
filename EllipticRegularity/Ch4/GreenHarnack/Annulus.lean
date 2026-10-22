module

public import EllipticRegularity.Ch4.GreenHarnack.OneBall
public import EllipticRegularity.Ch4.GreenHarnack.ChainEss
public import EllipticRegularity.Ch4.GreenHarnack.ChainAnnulus

/-!
# Harnack inequality in annuli (manuscript Lemma 4.41)

Let `V = B_{2r} ∖ \bar B_{r/8}` and `D_r = B_{3r/2} ∖ B_{r/4}`. A nonnegative solution `u ∈ H¹(V)`
of `-∇·(a∇u) = 0` in `V` satisfies `m ≤ u ≤ exp(C √Λ) m` almost everywhere in `D_r` for some
constant `m ≥ 0`, where `C = 415 C_H` and `C_H` is the constant of the Harnack inequality (Theorem 4.18).

The proof follows the manuscript: Harnack on the balls `B_s(y)`, `s = r/16`, `y` in the closed annulus
(`harnack_one_ball`), propagation along chains of `414` steps (`annulus_chain`,
`chain_propagate`), and a countable cover of `D_r` by such balls.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4GreenHarnack

open PDE MeasureTheory

variable {d : ℕ}

/-- The set `V = B_{2r} ∖ \bar B_{r/8}` of the manuscript. -/
def annulusV (d : ℕ) (r : ℝ) : Set (Vec d) :=
  euclideanBall (0 : Vec d) (2 * r) \ euclideanClosedBall (0 : Vec d) (r / 8)

/-- The set `D_r = B_{3r/2} ∖ B_{r/4}` of the manuscript. -/
def annulusD (d : ℕ) (r : ℝ) : Set (Vec d) :=
  euclideanBall (0 : Vec d) (3 * r / 2) \ euclideanBall (0 : Vec d) (r / 4)

theorem isOpen_annulusV (r : ℝ) : IsOpen (annulusV d r) :=
  (isOpen_euclideanBall _ _).sdiff (isClosed_euclideanClosedBall _ _)

theorem annulusD_subset_annulusSet {r : ℝ} (hr : 0 < r) : annulusD d r ⊆ annulusSet d r := by
  intro x ⟨h1, h2⟩
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith), sub_zero] at h1
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith), sub_zero, not_lt] at h2
  exact ⟨h2, h1.le⟩

theorem annulusD_subset_annulusV {r : ℝ} (hr : 0 < r) : annulusD d r ⊆ annulusV d r := by
  intro x ⟨h1, h2⟩
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith), sub_zero] at h1
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith), sub_zero, not_lt] at h2
  refine ⟨?_, ?_⟩
  · rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith), sub_zero]; linarith
  · rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by linarith), sub_zero]; intro h; linarith

/-- The balls `B_{2s}(y)`, `s = r/16`, centered in the closed annulus lie in `V`. -/
theorem ball_subset_annulusV {r : ℝ} (hr : 0 < r) {y : Vec d} (hy : y ∈ annulusSet d r) :
    euclideanBall y (2 * (r / 16)) ⊆ annulusV d r := by
  intro z hz
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)] at hz
  have h1 := vecEuclideanNorm_add_le (z - y) y
  rw [sub_add_cancel] at h1
  have h2 := vecEuclideanNorm_add_le (y - z) z
  rw [sub_add_cancel, vecEuclideanNorm_sub_comm y z] at h2
  obtain ⟨hy1, hy2⟩ := hy
  refine ⟨?_, ?_⟩
  · rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith), sub_zero]; linarith
  · rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by linarith), sub_zero]
    intro h; linarith

theorem harnack_annulus (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField d) (r : ℝ), 0 < r →
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j)
        (volumeOn (euclideanBall (0 : Vec d) (2 * r) \ euclideanClosedBall (0 : Vec d) (r / 8)))) →
      (∀ x ∈ euclideanBall (0 : Vec d) (2 * r) \ euclideanClosedBall (0 : Vec d) (r / 8),
        IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function
          (euclideanBall (0 : Vec d) (2 * r) \ euclideanClosedBall (0 : Vec d) (r / 8)),
        (∀ᵐ x ∂volumeOn
          (euclideanBall (0 : Vec d) (2 * r) \ euclideanClosedBall (0 : Vec d) (r / 8)),
          0 ≤ u.toFun x) →
        IsWeakDivergenceFormSolutionOn a
          (euclideanBall (0 : Vec d) (2 * r) \ euclideanClosedBall (0 : Vec d) (r / 8)) u
          (0 : Vec d → ℝ) 0 →
        ∃ m : ℝ, 0 ≤ m ∧
          ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) (3 * r / 2) \ euclideanBall (0 : Vec d) (r / 4)),
            m ≤ u.toFun x ∧ u.toFun x ≤ Real.exp (C * Real.sqrt Λ) * m := by
  obtain ⟨CH, hCH, hOne⟩ := harnack_one_ball d hd
  refine ⟨415 * CH, by positivity, ?_⟩
  intro Λ a r hr ha hEll u hu0 hsol
  change ∀ᵐ x ∂volumeOn (annulusV d r), 0 ≤ u.toFun x at hu0
  change ∃ m : ℝ, 0 ≤ m ∧ ∀ᵐ x ∂volumeOn (annulusD d r), _
  set s : ℝ := r / 16 with hsdef
  have hs : 0 < s := by positivity
  set f : Vec d → ℝ≥0∞ := fun x => ENNReal.ofReal (u.toFun x) with hf
  set M : Vec d → ℝ≥0∞ := fun y => essSup f (volumeOn (euclideanBall y s)) with hM
  set m : Vec d → ℝ≥0∞ := fun y => essInf f (volumeOn (euclideanBall y s)) with hm
  set Hr : ℝ := Real.exp (CH * Real.sqrt Λ) with hHr
  have hHpos : 0 < Hr := Real.exp_pos _
  set H : ℝ≥0∞ := ENNReal.ofReal Hr with hH
  have hA : ∀ y ∈ annulusSet d r, M y ≤ H * m y := fun y hy =>
    hOne Λ a (annulusV d r) (isOpen_annulusV r) ha hEll u hu0 hsol y s hs
      (ball_subset_annulusV hr hy)
  have hB : ∀ y ∈ annulusSet d r, ∀ y' ∈ annulusSet d r,
      vecEuclideanNorm (y' - y) < s → m y ≤ M y' := fun y _ y' _ h =>
    essInf_le_essSup_of_close f hs h
  have hglob : ∀ x ∈ annulusSet d r, ∀ y ∈ annulusSet d r, M x ≤ H ^ 415 * m y := fun x hx y hy =>
    chain_propagate hA hB (annulus_chain (by omega) hr hx hy)
  have hDK := annulusD_subset_annulusSet (d := d) hr
  -- finiteness of `m y`
  have hmfin : ∀ y ∈ annulusSet d r, m y ≠ ∞ := by
    intro y hy
    have hopen := isOpen_euclideanBall y s
    have := neZero_volumeOn_of_isOpen hopen ⟨y, center_mem_euclideanBall y hs⟩
    have h1 : ∀ᵐ x ∂volumeOn (euclideanBall y s), m y ≤ f x := ae_essInf_le
    obtain ⟨x, hx⟩ := h1.exists
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx
  -- countable cover of `D_r`
  obtain ⟨t, htc, htD, hDt⟩ := TopologicalSpace.exists_countable_dense_subset (annulusD d r)
  have hcover : ∀ x ∈ annulusD d r, ∃ y ∈ t, x ∈ euclideanBall y s := by
    intro x hx
    obtain ⟨y, hyo, hyt⟩ := mem_closure_iff.mp (hDt hx) _ (isOpen_euclideanBall x s)
      (center_mem_euclideanBall x hs)
    refine ⟨y, hyt, ?_⟩
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hs] at hyo ⊢
    rwa [vecEuclideanNorm_sub_comm]
  have hDne : (annulusD d r).Nonempty := by
    refine ⟨r • basisVec (⟨0, by omega⟩ : Fin d), ?_, ?_⟩
    · rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith), sub_zero, vecEuclideanNorm_smul,
        vecEuclideanNorm_basisVec, abs_of_pos hr]; linarith
    · rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith), sub_zero, vecEuclideanNorm_smul,
        vecEuclideanNorm_basisVec, abs_of_pos hr]; intro h; linarith
  obtain ⟨x₀, hx₀⟩ := hDne
  obtain ⟨y₀, hy₀t, -⟩ := hcover x₀ hx₀
  have htne : Nonempty t := ⟨⟨y₀, hy₀t⟩⟩
  set m0 : ℝ≥0∞ := ⨅ y : t, m y with hm0
  have hm0fin : m0 ≠ ∞ :=
    ne_top_of_le_ne_top (hmfin y₀ (hDK (htD hy₀t))) (iInf_le (fun y : t => m y) ⟨y₀, hy₀t⟩)
  have hae1 : ∀ᵐ x ∂volumeOn (annulusD d r), ∀ y ∈ t, x ∈ euclideanBall y s →
      m y ≤ f x ∧ f x ≤ M y := by
    rw [ae_ball_iff htc]
    intro y _
    have h1a : ∀ᵐ x ∂volumeOn (euclideanBall y s), m y ≤ f x := ae_essInf_le
    have h1b : ∀ᵐ x ∂volumeOn (euclideanBall y s), f x ≤ M y := ENNReal.ae_le_essSup f
    have h1 := h1a.and h1b
    exact ae_restrict_of_ae ((ae_restrict_iff' (measurableSet_euclideanBall y s)).1 h1)
  have hu0D : ∀ᵐ x ∂volumeOn (annulusD d r), 0 ≤ u.toFun x :=
    ae_restrict_of_ae_restrict_of_subset (annulusD_subset_annulusV hr) hu0
  refine ⟨m0.toReal, ENNReal.toReal_nonneg, ?_⟩
  have hDmeas : MeasurableSet (annulusD d r) :=
    (measurableSet_euclideanBall _ _).diff (measurableSet_euclideanBall _ _)
  filter_upwards [hae1, hu0D, ae_restrict_mem hDmeas] with x hx hx0 hxD
  obtain ⟨y, hyt, hxy⟩ := hcover x hxD
  have hmy : m0 ≤ m y := iInf_le (fun y : t => m y) ⟨y, hyt⟩
  have hlow : m0 ≤ f x := hmy.trans (hx y hyt hxy).1
  have hyK : y ∈ annulusSet d r := hDK (htD hyt)
  have hup : f x ≤ H ^ 415 * m0 := by
    rw [hm0, ENNReal.mul_iInf_of_ne (by simp [hH, hHpos]) (by simp [hH])]
    exact le_iInf fun y' => (hx y hyt hxy).2.trans (hglob y hyK y' (hDK (htD y'.2)))
  have hm0eq : ENNReal.ofReal m0.toReal = m0 := ENNReal.ofReal_toReal hm0fin
  refine ⟨?_, ?_⟩
  · have : ENNReal.ofReal m0.toReal ≤ ENNReal.ofReal (u.toFun x) := by rw [hm0eq]; exact hlow
    exact (ENNReal.ofReal_le_ofReal_iff hx0).1 this
  · have hpow : H ^ 415 = ENNReal.ofReal (Hr ^ 415) := by rw [hH, ENNReal.ofReal_pow hHpos.le]
    have h1 : ENNReal.ofReal (u.toFun x) ≤ ENNReal.ofReal (Hr ^ 415 * m0.toReal) := by
      rw [ENNReal.ofReal_mul (by positivity), ← hpow]
      rw [hm0eq]; exact hup
    have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
    have h3 : Hr ^ 415 = Real.exp (415 * CH * Real.sqrt Λ) := by
      rw [hHr, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    rwa [← h3]

end PDE.Ch4GreenHarnack
