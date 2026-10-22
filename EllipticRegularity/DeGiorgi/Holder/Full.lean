module

public import EllipticRegularity.DeGiorgi.Holder.Main

/-!
# The De Giorgi Hölder statement

`exists_deGiorgi_holder_constant_of_stability` is the statement of Theorem 4.8, proved
from the expansion-of-positivity statement (`hEoP`) and the two class-stability
facts `hAff`, `hScale` (see `EllipticRegularity.DeGiorgi.Holder.Interface`).
-/

@[expose] public section

namespace PDE.DGNMHolder

open PDE MeasureTheory

theorem ball_subset_unit {d : ℕ} {z : Vec d} {s r : ℝ} (hs : 0 < s) (hr : 0 < r) (hsr : s + r ≤ 1)
    (hz : z ∈ euclideanBall (0 : Vec d) s) :
    euclideanBall z r ⊆ euclideanBall (0 : Vec d) 1 := by
  apply euclideanBall_subset_of_center_norm_add_le hr one_pos
  have := (mem_euclideanBall_iff_vecEuclideanNorm_lt hs).1 hz
  simp only [sub_zero] at this ⊢
  linarith

/-- **De Giorgi's interior Hölder estimate** (Theorem 4.8), from expansion of
positivity and class stability. -/
theorem exists_deGiorgi_holder_constant_of_stability (d : ℕ) (hd : 3 ≤ d)
    (hEoP : ∃ C : ℝ, 0 < C ∧ EoPStatement d C)
    (hAff : AffineStability d) (hScale : ScaleStability d) :
    ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
      Real.exp (-(C * Λ ^ (((d : ℝ) + 2) / 4))) ≤ α ∧
      ∀ (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) 0 →
        ∃ (v : Vec d → ℝ) (M₀ M₁ : ℝ), v =ᵐ[volumeOn (euclideanBall (0 : Vec d) (1 / 2))] u.toFun ∧
          0 ≤ M₀ ∧ 0 ≤ M₁ ∧ (∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), |v x| ≤ M₀) ∧
          EuclideanHolderSeminormLE (euclideanBall (0 : Vec d) (1 / 2)) v α M₁ ∧
          ENNReal.ofReal (M₀ + M₁) ≤ ENNReal.ofReal (C * Λ ^ ((d : ℝ) / 4)) *
            eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1)) := by
  obtain ⟨CL, hCL, hL⟩ := DGNMLocalMax.exists_localMaxPrinciple_constant_full d hd
  obtain ⟨Ce, hCe, hE⟩ := hEoP
  have hd0 : 0 < d := by omega
  set κ : ℝ := 2 * Real.sqrt d with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have h2d : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  refine ⟨max (Ce + 1) ((1 + 192 * κ) * CL * (2 : ℝ) ^ d), lt_max_of_lt_left (by linarith), ?_⟩
  intro Λ hΛ
  have hΛ0 : 0 < Λ := lt_of_lt_of_le one_pos hΛ
  set δ : ℝ := decayConst d Ce Λ with hδ
  have hδ0 : 0 < δ := decayConst_pos d Ce Λ
  have hδh : δ ≤ 1 / 2 := decayConst_le_half d hCe hΛ
  obtain ⟨α, hα0, hα1, hδα, hθα⟩ := exists_alpha hδ0 hδh
  refine ⟨α, hα0, hα1, ?_, ?_⟩
  · refine le_trans ?_ hδα
    rw [hδ]
    unfold decayConst
    apply Real.exp_le_exp.2
    have hX : 0 ≤ Λ ^ (((d : ℝ) + 2) / 4) := by positivity
    have : Ce + 1 ≤ max (Ce + 1) ((1 + 192 * κ) * CL * (2 : ℝ) ^ d) := le_max_left _ _
    nlinarith
  set B : Set (Vec d) := euclideanBall (0 : Vec d) 1 with hB
  intro a hm he u hsol
  have hBconv : IsOpenBoundedConvexDomain B :=
    isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) one_pos
  have : IsFiniteMeasure (volumeOn B) := hBconv.isBoundedDomain.isFiniteMeasure_volumeOn
  set N : ℝ := (eLpNorm u.toFun 2 (volumeOn B)).toReal with hN
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  have hfinN : eLpNorm u.toFun 2 (volumeOn B) ≠ ⊤ := u.memL2.eLpNorm_ne_top
  have hΛd : 0 ≤ Λ ^ ((d : ℝ) / 4) := by positivity
  set Mr : ℝ := CL * Λ ^ ((d : ℝ) / 4) * (2 : ℝ) ^ d * N with hMr
  have hMr0 : 0 ≤ Mr := by positivity
  -- the norm bound at scales ρ ≥ 1/4
  have hMbound : ∀ ρ : ℝ, 1 / 4 ≤ ρ →
      ENNReal.ofReal (CL * Λ ^ ((d : ℝ) / 4)) *
        (ENNReal.ofReal ((ρ ^ d)⁻¹) ^ ((1 : ℝ) / 2) * eLpNorm u.toFun 2 (volumeOn B)) ≤
        ENNReal.ofReal Mr := by
    intro ρ hρ
    calc ENNReal.ofReal (CL * Λ ^ ((d : ℝ) / 4)) *
          (ENNReal.ofReal ((ρ ^ d)⁻¹) ^ ((1 : ℝ) / 2) * eLpNorm u.toFun 2 (volumeOn B))
        ≤ ENNReal.ofReal (CL * Λ ^ ((d : ℝ) / 4)) *
          (ENNReal.ofReal ((2 : ℝ) ^ d) * eLpNorm u.toFun 2 (volumeOn B)) := by
          gcongr
          exact scaleFactor_le hρ
      _ = ENNReal.ofReal (CL * Λ ^ ((d : ℝ) / 4)) *
          (ENNReal.ofReal ((2 : ℝ) ^ d) * ENNReal.ofReal N) := by
          rw [hN, ENNReal.ofReal_toReal hfinN]
      _ = ENNReal.ofReal Mr := by
          rw [← ENNReal.ofReal_mul h2d.le, ← ENNReal.ofReal_mul (by positivity), hMr]
          congr 1
          ring
  -- L^∞ bounds
  have hsup : ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2),
      EssentialRangeBoundsOn u.toFun (euclideanBall x (1 / 4)) (-Mr) Mr := by
    intro x hx
    have := essentialRange_of_linfty hL hAff hScale hm he hsol (z := x) (ρ := 1 / 2)
      (by norm_num) (euclideanBall_half_subset_unit_of_center_mem_half hx) hMr0
      (hMbound _ (by norm_num))
    rwa [show ((1 : ℝ) / 2) / 2 = 1 / 4 by norm_num] at this
  have hbase : ∀ z ∈ euclideanBall (0 : Vec d) (5 / 8),
      EssentialRangeBoundsOn u.toFun (euclideanBall z (1 / 8)) (-Mr) Mr := by
    intro z hz
    have hzB : euclideanBall z (1 / 4) ⊆ B := ball_subset_unit (by norm_num) (by norm_num) (by norm_num) hz
    have := essentialRange_of_linfty hL hAff hScale hm he hsol (z := z) (ρ := 1 / 4)
      (by norm_num) hzB hMr0 (hMbound _ le_rfl)
    rwa [show ((1 : ℝ) / 4) / 2 = 1 / 8 by norm_num] at this
  -- oscillation decay at small scales
  have hdecay : ∀ z ∈ euclideanBall (0 : Vec d) (5 / 8), ∀ r : ℝ, 0 < r → r ≤ 1 / 8 →
      ∃ m M' : ℝ, EssentialRangeBoundsOn u.toFun (euclideanBall z r) m M' ∧
        M' - m ≤ 32 * Mr * r ^ α := by
    intro z hz r hr hr8
    have hstep := dyadic_decay_bound
      (Q := fun ρ L => ∃ m M' : ℝ, EssentialRangeBoundsOn u.toFun (euclideanBall z ρ) m M' ∧
        M' - m ≤ L) (ρ₀ := 1 / 8) (L₀ := 2 * Mr) (θ := 1 - δ) (α := α)
      (by norm_num) (by positivity) (by linarith) hα0 hθα
      (fun ρ ρ' L L' ⟨m, M', h, hle⟩ hρ' hρρ' hLL' =>
        ⟨m, M', h.mono (euclideanBall_mono hρ'.le hρρ'), hle.trans hLL'⟩)
      (fun ρ L hρ hρ8 ⟨m, M', h, hle⟩ => by
        have hsub : euclideanBall z ρ ⊆ B :=
          ball_subset_unit (by norm_num) hρ (by linarith) hz
        obtain ⟨m', M'', h1, h2⟩ :=
          oscillation_decay_step hCe hE hAff hScale hm he hsol hρ hsub h
        exact ⟨m', M'', h1, h2.trans (mul_le_mul_of_nonneg_left hle (by linarith))⟩)
      ⟨-Mr, Mr, hbase z hz, by linarith⟩ r hr hr8
    obtain ⟨m, M', h, hle⟩ := hstep
    refine ⟨m, M', h, hle.trans ?_⟩
    have h16 : (2 * r / (1 / 8 : ℝ)) ^ α ≤ 16 * r ^ α := by
      rw [show 2 * r / (1 / 8 : ℝ) = 16 * r by ring, Real.mul_rpow (by norm_num) hr.le]
      have : (16 : ℝ) ^ α ≤ 16 := by
        calc (16 : ℝ) ^ α ≤ (16 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
          _ = 16 := Real.rpow_one _
      exact mul_le_mul_of_nonneg_right this (by positivity)
    calc 2 * Mr * (2 * r / (1 / 8 : ℝ)) ^ α ≤ 2 * Mr * (16 * r ^ α) :=
          mul_le_mul_of_nonneg_left h16 (by positivity)
      _ = 32 * Mr * r ^ α := by ring
  -- zero extension
  set ũ : Vec d → ℝ := B.indicator u.toFun with hũ
  have hint : IntegrableOn u.toFun B := u.memL2.integrable one_le_two
  have hloc : LocallyIntegrable ũ volume :=
    ((integrable_indicator_iff (measurableSet_euclideanBall _ _)).2 hint).locallyIntegrable
  have hsup' : ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2),
      EssentialRangeBoundsOn ũ (euclideanBall x (1 / 4)) (-Mr) Mr := by
    intro x hx
    exact range_indicator (measurableSet_euclideanBall _ _)
      (ball_subset_unit (by norm_num) (by norm_num) (by norm_num) hx) (hsup x hx)
  have hdec' : ∀ z ∈ euclideanBall (0 : Vec d) (5 / 8), ∀ r : ℝ, 0 < r → r ≤ 1 / 8 →
      HasEssentialOscillationLEOn ũ (euclideanBall z r) (32 * Mr * r ^ α) := by
    intro z hz r hr hr8
    obtain ⟨m, M', h, hle⟩ := hdecay z hz r hr hr8
    exact ⟨m, M', range_indicator (measurableSet_euclideanBall _ _)
      (ball_subset_unit (by norm_num) hr (by linarith) hz) h, hle⟩
  obtain ⟨v, hvae, hvb, hvH⟩ := exists_holderRepresentative_of_oscillationDecay hd0 hloc hα0 hα1
    (by positivity : 0 ≤ 32 * Mr) hMr0 hsup' hdec'
  have hhalfB : euclideanBall (0 : Vec d) (1 / 2) ⊆ B := euclideanBall_mono (by norm_num) (by norm_num)
  refine ⟨v, Mr, (2 * κ) * (32 * Mr) + (128 * κ) * Mr, ?_, hMr0, by positivity, hvb, hvH, ?_⟩
  · filter_upwards [hvae, ae_restrict_mem (measurableSet_euclideanBall (0 : Vec d) (1 / 2))]
      with x hx hxm
    rw [hx, hũ, Set.indicator_of_mem (hhalfB hxm)]
  · have hC : (1 + 192 * κ) * CL * (2 : ℝ) ^ d ≤
        max (Ce + 1) ((1 + 192 * κ) * CL * (2 : ℝ) ^ d) := le_max_right _ _
    have hsum : Mr + ((2 * κ) * (32 * Mr) + (128 * κ) * Mr) = (1 + 192 * κ) * CL * (2 : ℝ) ^ d *
        Λ ^ ((d : ℝ) / 4) * N := by rw [hMr]; ring
    calc ENNReal.ofReal (Mr + ((2 * κ) * (32 * Mr) + (128 * κ) * Mr))
        ≤ ENNReal.ofReal (max (Ce + 1) ((1 + 192 * κ) * CL * (2 : ℝ) ^ d) *
            Λ ^ ((d : ℝ) / 4) * N) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hsum]
          gcongr
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity), hN, ENNReal.ofReal_toReal hfinN]

end PDE.DGNMHolder
