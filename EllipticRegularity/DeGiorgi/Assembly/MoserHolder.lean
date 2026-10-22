module

public import EllipticRegularity.DeGiorgi.Assembly.PointwiseHarnack
public import EllipticRegularity.DeGiorgi.Assembly.OscDecay
public import EllipticRegularity.DeGiorgi.Assembly.MoserAlpha

/-!
# Moser's interior Hölder estimate (assembly)

Theorem 4.21, from the Harnack inequality, Moser's `L^∞` estimate and De Giorgi's
continuity (which supplies a continuous representative).
-/

@[expose] public section

open scoped ENNReal Pointwise

namespace PDE.DGNMAssembly

open MeasureTheory Filter

variable {d : ℕ}

/-- Hölder seminorm bound with the oscillation decay hypotheses (core of Theorem 4.21). -/
theorem moser_core (d : ℕ) (hDG : DeGiorgiHolderConcl d) (hSol : SolAffineTransfer d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {a : CoeffField d}
    (hmeas : ∀ i j : Fin d, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function (euclideanBall (0 : Vec d) 1)}
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) 0)
    {H α : ℝ} (hH3 : 3 ≤ H) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hαeq : (1 / 2 : ℝ) ^ α = (H - 1) / (H + 1))
    (hpw : ∀ v : Vec d → ℝ, ContinuousOn v (euclideanBall (0 : Vec d) (3 / 4)) →
      v =ᵐ[volumeOn (euclideanBall (0 : Vec d) (3 / 4))] u.toFun →
      ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ, 0 < r → r ≤ 1 / 4 →
      ∀ s c : ℝ, (s = 1 ∨ s = -1) → (∀ y ∈ euclideanBall x r, 0 < c + s * v y) →
      ∀ y ∈ euclideanBall x (r / 2), ∀ z ∈ euclideanBall x (r / 2),
        c + s * v y ≤ H * (c + s * v z))
    {Kc : ℝ} (hKc : 0 ≤ Kc) {N : ℝ≥0∞} (hN : N ≠ ⊤)
    (hsup : ∀ z ∈ euclideanBall (0 : Vec d) (3 / 4), ∀ s : ℝ, (s = 1 ∨ s = -1) →
        essSup (fun x => ENNReal.ofReal (s * u.toFun x)) (volumeOn (euclideanBall z (1 / 8))) ≤
          ENNReal.ofReal Kc * N) :
    ∃ (v : Vec d → ℝ) (M₀ M₁ : ℝ), v =ᵐ[volumeOn (euclideanBall (0 : Vec d) (1 / 2))] u.toFun ∧
      0 ≤ M₀ ∧ 0 ≤ M₁ ∧ (∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), |v x| ≤ M₀) ∧
      EuclideanHolderSeminormLE (euclideanBall (0 : Vec d) (1 / 2)) v α M₁ ∧
      M₀ + M₁ = 33 * (Kc * N.toReal) := by
  obtain ⟨v, hvc, hvu⟩ := glue_continuous_rep (isOpen_euclideanBall (0 : Vec d) (3 / 4))
    (local_cont_rep hDG hSol hΛ hmeas hell hsol)
  set B34 : Set (Vec d) := euclideanBall (0 : Vec d) (3 / 4) with hB34
  have hB34open : IsOpen B34 := isOpen_euclideanBall _ _
  set Kv : ℝ := Kc * N.toReal with hKv
  have hKvnn : 0 ≤ Kv := mul_nonneg hKc ENNReal.toReal_nonneg
  have hKvENN : ENNReal.ofReal Kc * N = ENNReal.ofReal Kv := by
    rw [hKv, ENNReal.ofReal_mul hKc, ENNReal.ofReal_toReal hN]
  -- the pointwise bound `|v| ≤ Kv` on `B_{3/4}`
  have hbd : ∀ y ∈ B34, |v y| ≤ Kv := by
    intro y hy
    have hsign : ∀ s : ℝ, (s = 1 ∨ s = -1) → s * v y ≤ Kv := by
      intro s hs
      have hW : IsOpen (euclideanBall y (1 / 8) ∩ B34) := (isOpen_euclideanBall _ _).inter hB34open
      have hWU : euclideanBall y (1 / 8) ∩ B34 ⊆ euclideanBall y (1 / 8) := Set.inter_subset_left
      have hcont : ContinuousOn (fun x => s * v x) (euclideanBall y (1 / 8) ∩ B34) :=
        continuousOn_const.mul (hvc.mono Set.inter_subset_right)
      have hae : (fun x => ENNReal.ofReal (s * v x)) =ᵐ[volumeOn (euclideanBall y (1 / 8) ∩ B34)]
          fun x => ENNReal.ofReal (s * u.toFun x) := by
        filter_upwards [ae_mono (Measure.restrict_mono Set.inter_subset_right le_rfl) hvu] with x hx
        rw [hx]
      have hymem : y ∈ euclideanBall y (1 / 8) ∩ B34 :=
        ⟨center_mem_euclideanBall _ (by norm_num), hy⟩
      have h1 := ofReal_le_essSup_of_cont hW hWU hcont hae hymem
      have h2 := h1.trans (hsup y hy s hs)
      rw [hKvENN] at h2
      exact (ENNReal.ofReal_le_ofReal_iff hKvnn).1 h2
    rw [abs_le]
    constructor
    · have := hsign (-1) (Or.inr rfl); linarith
    · have := hsign 1 (Or.inl rfl); linarith
  -- one-step oscillation decay
  have hstep : ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ, 0 < r → r ≤ 1 / 4 →
      ∀ ω : ℝ, OscLE (euclideanBall x r) v ω →
        OscLE (euclideanBall x (r / 2)) v ((1 / 2 : ℝ) ^ α * ω) := by
    intro x hx r hr hr4 ω hω
    rw [hαeq]
    exact osc_step hr (by linarith)
      (fun y hy => hbd y (ball_subset_three_quarters hx hr hr4 hy))
      (fun s c hs hpos => hpw v hvc hvu x hx r hr hr4 s c hs hpos) hω
  have hHolder := holder_of_osc hKvnn hα0 hα1 rfl hbd hstep
  refine ⟨v, Kv, 32 * Kv, ?_, hKvnn, by positivity, ?_, hHolder, by ring⟩
  · exact ae_mono (Measure.restrict_mono (euclideanBall_mono (by norm_num) (by norm_num)) le_rfl) hvu
  · intro x hx
    exact hbd x (euclideanBall_mono (by norm_num) (by norm_num) hx)

theorem rpow_root_bound {x p : ℝ} (hx : 0 ≤ x) (hp : 1 < p) :
    x ^ (1 / p) ≤ max 1 x := by
  by_cases h : x ≤ 1
  · exact (Real.rpow_le_one hx h (by positivity)).trans (le_max_left _ _)
  · rw [not_le] at h
    calc x ^ (1 / p) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h.le (by rw [div_le_one (by linarith)]; exact hp.le)
      _ = x := Real.rpow_one x
      _ ≤ max 1 x := le_max_right _ _

/-- **Moser's interior Hölder estimate** (Theorem 4.21). -/
theorem exists_moser_holder_constant_full (d : ℕ) (hd : 3 ≤ d) (hH : HarnackConcl d)
    (hMax : MoserLocalMaxConcl d) (hDG : DeGiorgiHolderConcl d) (hSol : SolAffineTransfer d) :
    ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∃ α : ℝ, Real.exp (-(C * Real.sqrt Λ)) ≤ α ∧ α ≤ 1 ∧
      ∀ (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) 0 →
      ∀ p : ℝ, 1 < p →
        ∃ (v : Vec d → ℝ) (M₀ M₁ : ℝ), v =ᵐ[volumeOn (euclideanBall (0 : Vec d) (1 / 2))] u.toFun ∧
          0 ≤ M₀ ∧ 0 ≤ M₁ ∧ (∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), |v x| ≤ M₀) ∧
          EuclideanHolderSeminormLE (euclideanBall (0 : Vec d) (1 / 2)) v α M₁ ∧
          ENNReal.ofReal (M₀ + M₁) ≤
            ENNReal.ofReal (C * Λ ^ ((d : ℝ) / (2 * p)) * (p / (p - 1)) ^ ((d : ℝ) / p)) *
              eLpNorm u.toFun (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1)) := by
  obtain ⟨CH, hpwall⟩ := harnack_pointwise d hH hSol
  obtain ⟨CM, hCM, hsupall⟩ := sup_bound_ess d hMax hSol
  have hd0 : (0 : ℝ) < d := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set C : ℝ := max (max 2 CH) (33 * max 1 (4 ^ (d : ℝ) * CM)) with hC
  have hC2 : 2 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCH : CH ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hC33 : 33 * max 1 (4 ^ (d : ℝ) * CM) ≤ C := le_max_right _ _
  refine ⟨C, by linarith, ?_⟩
  intro Λ hΛ
  have hΛ0 : 0 < Λ := by linarith
  have hs1 : 1 ≤ Real.sqrt Λ := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hΛ
  set H : ℝ := max 3 (Real.exp (CH * Real.sqrt Λ)) with hHdef
  have hH3 : 3 ≤ H := le_max_left _ _
  have hHexp : H ≤ Real.exp (C * Real.sqrt Λ) := by
    refine max_le ?_ ?_
    · have h2 : 2 ≤ C * Real.sqrt Λ := by nlinarith
      have := Real.add_one_le_exp (C * Real.sqrt Λ)
      linarith
    · exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hCH (by linarith))
  obtain ⟨α, hα0, hα1, hαH, hαeq⟩ := alpha_facts hH3
  refine ⟨α, ?_, hα1, ?_⟩
  · calc Real.exp (-(C * Real.sqrt Λ)) = (Real.exp (C * Real.sqrt Λ))⁻¹ := Real.exp_neg _
      _ ≤ H⁻¹ := inv_anti₀ (by linarith) hHexp
      _ = 1 / H := (one_div H).symm
      _ ≤ α := hαH
  intro a hmeas hell u hsol p hp
  -- the Harnack input in pointwise form
  have hpw : ∀ v : Vec d → ℝ, ContinuousOn v (euclideanBall (0 : Vec d) (3 / 4)) →
      v =ᵐ[volumeOn (euclideanBall (0 : Vec d) (3 / 4))] u.toFun →
      ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ, 0 < r → r ≤ 1 / 4 →
      ∀ s c : ℝ, (s = 1 ∨ s = -1) → (∀ y ∈ euclideanBall x r, 0 < c + s * v y) →
      ∀ y ∈ euclideanBall x (r / 2), ∀ z ∈ euclideanBall x (r / 2),
        c + s * v y ≤ H * (c + s * v z) := by
    intro v hvc hvu x hx r hr hr4 s c hs hpos y hy z hz
    have h1 := hpwall Λ a hmeas hell u hsol v hvc hvu x hx r hr hr4 s c hs hpos y hy z hz
    have hzpos : 0 < c + s * v z :=
      hpos z (euclideanBall_mono (by positivity) (by linarith) hz)
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hzpos.le)
  -- the constant for exponent `q`
  have hcore : ∀ q : ℝ, 1 < q → eLpNorm u.toFun (ENNReal.ofReal q)
      (volumeOn (euclideanBall (0 : Vec d) 1)) ≠ ⊤ →
      ∃ (v : Vec d → ℝ) (M₀ M₁ : ℝ), v =ᵐ[volumeOn (euclideanBall (0 : Vec d) (1 / 2))] u.toFun ∧
        0 ≤ M₀ ∧ 0 ≤ M₁ ∧ (∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), |v x| ≤ M₀) ∧
        EuclideanHolderSeminormLE (euclideanBall (0 : Vec d) (1 / 2)) v α M₁ ∧
        ENNReal.ofReal (M₀ + M₁) ≤
          ENNReal.ofReal (C * Λ ^ ((d : ℝ) / (2 * q)) * (q / (q - 1)) ^ ((d : ℝ) / q)) *
            eLpNorm u.toFun (ENNReal.ofReal q) (volumeOn (euclideanBall (0 : Vec d) 1)) := by
    intro q hq hNq
    set Kc : ℝ := (4 ^ (d : ℝ) * CM * Λ ^ ((d : ℝ) / 2) * (q / (q - 1)) ^ (d : ℝ)) ^ (1 / q)
      with hKc
    have hqq : 0 < q / (q - 1) := div_pos (by linarith) (by linarith)
    have hKcnn : 0 ≤ Kc := Real.rpow_nonneg (by positivity) _
    obtain ⟨v, M₀, M₁, hv1, hM₀, hM₁, hM₀b, hHold, hsum⟩ := moser_core d hDG hSol hΛ hmeas hell
      hsol hH3 hα0 hα1 hαeq hpw hKcnn hNq
      (fun z hz s hs => hsupall Λ a hmeas hell u hsol q hq z hz s hs)
    refine ⟨v, M₀, M₁, hv1, hM₀, hM₁, hM₀b, hHold, ?_⟩
    have hKcle : Kc ≤ max 1 (4 ^ (d : ℝ) * CM) * Λ ^ ((d : ℝ) / (2 * q)) *
        (q / (q - 1)) ^ ((d : ℝ) / q) := by
      have e1 : Kc = (4 ^ (d : ℝ) * CM) ^ (1 / q) * Λ ^ ((d : ℝ) / (2 * q)) *
          (q / (q - 1)) ^ ((d : ℝ) / q) := by
        rw [hKc, Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hΛ0.le,
          ← Real.rpow_mul hqq.le]
        congr 3 <;> field_simp
      rw [e1]
      have := rpow_root_bound (x := 4 ^ (d : ℝ) * CM) (by positivity) hq
      gcongr
    rw [hsum]
    have hq0 : 0 ≤ Λ ^ ((d : ℝ) / (2 * q)) * (q / (q - 1)) ^ ((d : ℝ) / q) := by positivity
    calc ENNReal.ofReal (33 * (Kc * (eLpNorm u.toFun (ENNReal.ofReal q)
          (volumeOn (euclideanBall (0 : Vec d) 1))).toReal))
        ≤ ENNReal.ofReal ((C * Λ ^ ((d : ℝ) / (2 * q)) * (q / (q - 1)) ^ ((d : ℝ) / q)) *
            (eLpNorm u.toFun (ENNReal.ofReal q)
              (volumeOn (euclideanBall (0 : Vec d) 1))).toReal) := by
          apply ENNReal.ofReal_le_ofReal
          have hT : 0 ≤ (eLpNorm u.toFun (ENNReal.ofReal q)
              (volumeOn (euclideanBall (0 : Vec d) 1))).toReal := ENNReal.toReal_nonneg
          have h33 : 33 * Kc ≤ C * Λ ^ ((d : ℝ) / (2 * q)) * (q / (q - 1)) ^ ((d : ℝ) / q) := by
            calc 33 * Kc ≤ 33 * (max 1 (4 ^ (d : ℝ) * CM) * Λ ^ ((d : ℝ) / (2 * q)) *
                (q / (q - 1)) ^ ((d : ℝ) / q)) := by linarith
              _ = (33 * max 1 (4 ^ (d : ℝ) * CM)) * (Λ ^ ((d : ℝ) / (2 * q)) *
                    (q / (q - 1)) ^ ((d : ℝ) / q)) := by ring
              _ ≤ C * (Λ ^ ((d : ℝ) / (2 * q)) * (q / (q - 1)) ^ ((d : ℝ) / q)) :=
                    mul_le_mul_of_nonneg_right hC33 hq0
              _ = _ := by ring
          nlinarith
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hNq]
  by_cases hN : eLpNorm u.toFun (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1)) = ⊤
  · have h2 : eLpNorm u.toFun (ENNReal.ofReal 2) (volumeOn (euclideanBall (0 : Vec d) 1)) ≠ ⊤ := by
      have := u.memL2.eLpNorm_ne_top
      simpa using this
    obtain ⟨v, M₀, M₁, h1, h2', h3, h4, h5, _⟩ := hcore 2 (by norm_num) h2
    refine ⟨v, M₀, M₁, h1, h2', h3, h4, h5, ?_⟩
    rw [hN]
    have hpos : 0 < C * Λ ^ ((d : ℝ) / (2 * p)) * (p / (p - 1)) ^ ((d : ℝ) / p) := by
      have : 0 < p / (p - 1) := div_pos (by linarith) (by linarith)
      have : 0 < C := by linarith
      positivity
    rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne']
    exact le_top
  · exact hcore p hp hN

end PDE.DGNMAssembly
