module

public import PDEFoundation.FunctionalInequalities.Isoperimetric.Defs
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Fibre chart for `C¹` frontiers

On a real inner product space, near a frontier point of a set with `C¹` frontier, points outside
the set that lie within `ε` of the frontier and on one `ν`-line have `ν`-coordinates within
`√(1+κ²) ε` of each other (`exists_fibre_chart`).  Also, a point of the closed `ε`-thickening of
a compact closure lying outside the closure is within `ε` of the frontier
(`exists_frontier_dist_le`).
-/

@[expose] public section

namespace PDE.IsoperimetricProof

open Set Metric

section Algebra

/-- Cauchy–Schwarz in the plane. -/
theorem abs_add_mul_le_sqrt (α p κ : ℝ) :
    |α| + κ * p ≤ Real.sqrt (1 + κ ^ 2) * Real.sqrt (α ^ 2 + p ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.le_sqrt_of_sq_le
  have h : (|α| + κ * p) ^ 2 ≤ (1 + κ ^ 2) * (α ^ 2 + p ^ 2) := by
    have h : α ^ 2 = |α| ^ 2 := (sq_abs α).symm
    rw [h]
    linarith [sq_nonneg (|α| * κ - p)]
  exact h

/-- Pythagoras along a unit vector. -/
theorem norm_sq_eq_inner_sq_add {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ν : V} (hν : ‖ν‖ = 1) (w : V) :
    ‖w‖ ^ 2 = (inner ℝ ν w) ^ 2 + ‖w - (inner ℝ ν w) • ν‖ ^ 2 := by
  have hνν : inner ℝ ν ν = 1 := by
    rw [real_inner_self_eq_norm_sq, hν]; norm_num
  have h1 : ‖w‖ ^ 2 = inner ℝ w w := (real_inner_self_eq_norm_sq w).symm
  have h2 : ‖w - (inner ℝ ν w) • ν‖ ^ 2 = inner ℝ (w - (inner ℝ ν w) • ν) (w - (inner ℝ ν w) • ν) :=
    (real_inner_self_eq_norm_sq _).symm
  rw [h1, h2]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hνν,
    real_inner_comm ν w]
  simp only [conj_trivial]
  ring

/-- Cone condition from a tangential slope bound. -/
theorem cone_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ν : V} (hν : ‖ν‖ = 1) {θ κ : ℝ} (hθ0 : 0 < θ) (hθ4 : θ ≤ 1 / 4)
    (hθκ : θ ≤ κ * (1 - θ)) (w : V) (h : |inner ℝ ν w| ≤ θ * ‖w‖) :
    |inner ℝ ν w| ≤ κ * ‖w - (inner ℝ ν w) • ν‖ := by
  set c := |inner ℝ ν w| with hc
  set p := ‖w - (inner ℝ ν w) • ν‖ with hp
  have hpn : 0 ≤ p := norm_nonneg _
  have hc0 : 0 ≤ c := abs_nonneg _
  have hsq := norm_sq_eq_inner_sq_add hν w
  have hw : ‖w‖ ≤ c + p := by
    apply le_of_sq_le_sq _ (by positivity)
    have : c ^ 2 = (inner ℝ ν w) ^ 2 := sq_abs _
    linarith [mul_nonneg hc0 hpn]
  have h1 : c ≤ θ * (c + p) := h.trans (mul_le_mul_of_nonneg_left hw hθ0.le)
  have h2 : c * (1 - θ) ≤ θ * p := by linarith
  have h3 : κ * (1 - θ) * p ≥ θ * p := mul_le_mul_of_nonneg_right hθκ hpn
  have h4 : c * (1 - θ) ≤ κ * p * (1 - θ) := by linarith
  exact le_of_mul_le_mul_right h4 (by linarith)

end Algebra

section Fibre

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Abstract fibre bound: the slope condition `hK` for `f` on the ball `B = ball x₀ (4 r)`,
for a point `y` outside `E` near a frontier point `q`, gives a zero of `f` on the `ν`-line
through `y`, below `y`, at distance at most `√(1+κ²) ε`. -/
theorem exists_zero_on_line {x₀ : V} {r : ℝ} {f : V → ℝ} (hf : Continuous f) {ν : V}
    (hν : ‖ν‖ = 1) {θ κ : ℝ} (hθ0 : 0 < θ) (hθ4 : θ ≤ 1 / 4) (hθκ : θ ≤ κ * (1 - θ))
    (hK : ∀ y ∈ ball x₀ (4 * r), ∀ y' ∈ ball x₀ (4 * r),
      |f y' - f y - inner ℝ ν (y' - y)| ≤ θ * ‖y' - y‖)
    {ε : ℝ} (hεr : ε ≤ r) {y q : V} (hy : y ∈ ball x₀ r) (hq : q ∈ ball x₀ (4 * r))
    (hfq : f q = 0) (hfy : 0 ≤ f y) (hyq : dist y q ≤ ε) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ Real.sqrt (1 + κ ^ 2) * ε ∧ f (y - s • ν) = 0 ∧
      y - s • ν ∈ ball x₀ (4 * r) := by
  have hε0 : 0 ≤ ε := dist_nonneg.trans hyq
  have hyq' : ‖y - q‖ ≤ ε := by rwa [← dist_eq_norm]
  have hyB : y ∈ ball x₀ (4 * r) := by
    have := mem_ball.1 hy
    have hr : 0 ≤ r := hε0.trans hεr
    exact mem_ball.2 (by linarith)
  -- points of the line within `3ε` stay in the ball
  have hline : ∀ τ : ℝ, |τ| ≤ 3 * ε → y + τ • ν ∈ ball x₀ (4 * r) := by
    intro τ hτ
    have h1 := mem_ball.1 hy
    rw [dist_eq_norm] at h1
    rw [mem_ball, dist_eq_norm]
    have : ‖y + τ • ν - x₀‖ ≤ ‖y - x₀‖ + |τ| := by
      calc ‖y + τ • ν - x₀‖ = ‖(y - x₀) + τ • ν‖ := by congr 1; abel
        _ ≤ ‖y - x₀‖ + ‖τ • ν‖ := norm_add_le _ _
        _ = ‖y - x₀‖ + |τ| := by rw [norm_smul, hν, mul_one, Real.norm_eq_abs]
    linarith
  have hαabs : |inner ℝ ν (y - q)| ≤ ε :=
    (abs_real_inner_le_norm ν (y - q)).trans (by rw [hν, one_mul]; exact hyq')
  -- values at the endpoints
  have hupper : 0 ≤ f (y + (3 * ε) • ν) := by
    have hB := hK q hq (y + (3 * ε) • ν) (hline _ (by rw [abs_of_nonneg (by positivity)]))
    have hn : ‖y + (3 * ε) • ν - q‖ ≤ 4 * ε := by
      calc ‖y + (3 * ε) • ν - q‖ = ‖(y - q) + (3 * ε) • ν‖ := by congr 1; abel
        _ ≤ ‖y - q‖ + ‖(3 * ε) • ν‖ := norm_add_le _ _
        _ ≤ 4 * ε := by
          rw [norm_smul, hν, mul_one, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          linarith
    have hi : inner ℝ ν (y + (3 * ε) • ν - q) = inner ℝ ν (y - q) + 3 * ε := by
      have : y + (3 * ε) • ν - q = (y - q) + (3 * ε) • ν := by abel
      rw [this, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hν]; ring
    have hθn : θ * ‖y + (3 * ε) • ν - q‖ ≤ ε := by
      calc θ * ‖y + (3 * ε) • ν - q‖ ≤ (1 / 4) * (4 * ε) :=
            mul_le_mul hθ4 hn (norm_nonneg _) (by norm_num)
        _ = ε := by ring
    rw [hi, hfq] at hB
    have := (abs_le.1 hB).1
    have := (abs_le.1 hαabs).1
    linarith
  have hlower : f (y + (-(3 * ε)) • ν) ≤ 0 := by
    have hB := hK q hq (y + (-(3 * ε)) • ν) (hline _ (by rw [abs_neg, abs_of_nonneg (by positivity)]))
    have hn : ‖y + (-(3 * ε)) • ν - q‖ ≤ 4 * ε := by
      calc ‖y + (-(3 * ε)) • ν - q‖ = ‖(y - q) + (-(3 * ε)) • ν‖ := by congr 1; abel
        _ ≤ ‖y - q‖ + ‖(-(3 * ε)) • ν‖ := norm_add_le _ _
        _ ≤ 4 * ε := by
          rw [norm_smul, hν, mul_one, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
          linarith
    have hi : inner ℝ ν (y + (-(3 * ε)) • ν - q) = inner ℝ ν (y - q) + -(3 * ε) := by
      have : y + (-(3 * ε)) • ν - q = (y - q) + (-(3 * ε)) • ν := by abel
      rw [this, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hν]; ring
    have hθn : θ * ‖y + (-(3 * ε)) • ν - q‖ ≤ ε := by
      calc θ * ‖y + (-(3 * ε)) • ν - q‖ ≤ (1 / 4) * (4 * ε) :=
            mul_le_mul hθ4 hn (norm_nonneg _) (by norm_num)
        _ = ε := by ring
    rw [hi, hfq] at hB
    have := (abs_le.1 hB).2
    have := (abs_le.1 hαabs).2
    linarith
  -- intermediate value theorem
  have hcont : ContinuousOn (fun τ : ℝ => f (y + τ • ν)) (Icc (-(3 * ε)) (3 * ε)) :=
    (hf.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
  obtain ⟨τ, hτ, hτ0⟩ := intermediate_value_Icc (by linarith : -(3 * ε) ≤ 3 * ε) hcont
    ⟨by simpa using hlower, by simpa using hupper⟩
  have hτabs : |τ| ≤ 3 * ε := abs_le.2 ⟨hτ.1, hτ.2⟩
  have hτB := hline τ hτabs
  simp only at hτ0
  -- τ ≤ 0
  have hτle : τ ≤ 0 := by
    by_contra hpos'
    have hpos : 0 < τ := not_le.1 hpos'
    have hB := hK y hyB (y + τ • ν) hτB
    have hi : inner ℝ ν (y + τ • ν - y) = τ := by
      have : y + τ • ν - y = τ • ν := by abel
      rw [this, inner_smul_right, real_inner_self_eq_norm_sq, hν]; ring
    have hn : ‖y + τ • ν - y‖ = τ := by
      have : y + τ • ν - y = τ • ν := by abel
      rw [this, norm_smul, hν, mul_one, Real.norm_eq_abs, abs_of_pos hpos]
    rw [hi, hn, hτ0] at hB
    have := (abs_le.1 hB).1
    linarith [mul_le_mul_of_nonneg_right hθ4 hpos.le]
  refine ⟨-τ, by linarith, ?_, by simpa [sub_eq_add_neg] using hτ0, by
    simpa [sub_eq_add_neg] using hτB⟩
  -- the distance bound through the cone condition
  set z := y + τ • ν with hz
  have hcone := hK z hτB q hq
  rw [hfq, hτ0] at hcone
  have hcone' : |inner ℝ ν (q - z)| ≤ θ * ‖q - z‖ := by simpa using hcone
  have hcb := cone_bound hν hθ0 hθ4 hθκ (q - z) hcone'
  set α := inner ℝ ν (y - q) with hα
  have hcz : inner ℝ ν (q - z) = -α - τ := by
    have : q - z = -(y - q) - τ • ν := by rw [hz]; abel
    rw [this, inner_sub_right, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq, hν]
    ring
  have hP : q - z - (inner ℝ ν (q - z)) • ν = -((y - q) - α • ν) := by
    rw [hcz, hz]
    module
  have hpn : ‖q - z - (inner ℝ ν (q - z)) • ν‖ = ‖(y - q) - α • ν‖ := by
    rw [hP, norm_neg]
  rw [hpn] at hcb
  have hp0 : 0 ≤ ‖(y - q) - α • ν‖ := norm_nonneg _
  have hsq := norm_sq_eq_inner_sq_add hν (y - q)
  have hnorm : Real.sqrt (α ^ 2 + ‖(y - q) - α • ν‖ ^ 2) = ‖y - q‖ := by
    rw [← hsq]; exact Real.sqrt_sq (norm_nonneg _)
  have hmain := abs_add_mul_le_sqrt α ‖(y - q) - α • ν‖ κ
  rw [hnorm] at hmain
  have hs : -τ ≤ |α| + |-α - τ| := by
    cases abs_cases α <;> cases abs_cases (-α - τ) <;> linarith
  rw [hcz] at hcb
  have hsqrt : 0 ≤ Real.sqrt (1 + κ ^ 2) := Real.sqrt_nonneg _
  calc -τ ≤ |α| + κ * ‖(y - q) - α • ν‖ := by linarith
    _ ≤ Real.sqrt (1 + κ ^ 2) * ‖y - q‖ := hmain
    _ ≤ Real.sqrt (1 + κ ^ 2) * ε := mul_le_mul_of_nonneg_left hyq' hsqrt


omit [InnerProductSpace ℝ V] in
/-- Points of `W` of the frontier lie on the zero set of the defining function. -/
theorem frontier_zero {E W : Set V} (hEo : IsOpen E) (hW : IsOpen W) {φ : V → ℝ}
    (hφ : Continuous φ) (hEW : E ∩ W = {y | y ∈ W ∧ φ y < 0}) {q : V}
    (hq : q ∈ frontier E) (hqW : q ∈ W) : φ q = 0 := by
  have hqE : q ∉ E := by
    have h := (show q ∈ closure E \ interior E from hq).2
    rwa [hEo.interior_eq] at h
  have hqc : q ∈ closure E := (show q ∈ closure E \ interior E from hq).1
  have h1 : 0 ≤ φ q := by
    by_contra h
    exact hqE (hEW.symm ▸ (show q ∈ {y | y ∈ W ∧ φ y < 0} from ⟨hqW, not_le.1 h⟩) : q ∈ E ∩ W).1
  have h2 : φ q ≤ 0 := by
    by_contra h
    have hpos : 0 < φ q := not_le.1 h
    obtain ⟨z, hzU, hzE⟩ := mem_closure_iff.1 hqc (W ∩ {y | 0 < φ y})
      (hW.inter (isOpen_lt continuous_const hφ)) ⟨hqW, hpos⟩
    have : z ∈ {y | y ∈ W ∧ φ y < 0} := hEW ▸ (⟨hzE, hzU.1⟩ : z ∈ E ∩ W)
    have := this.2
    have := hzU.2
    simp only [Set.mem_ofPred_eq] at *
    linarith
  exact le_antisymm h2 h1

/-- Fibre lemma: points outside `E`, within `ε` of the frontier, on one `ν`-line, are
`√(1+κ²) ε`-close in the `ν` coordinate. -/
theorem exists_fibre_chart [CompleteSpace V] {E : Set V} (hEo : IsOpen E) (hE : HasC1Frontier E)
    {x₀ : V} (hx₀ : x₀ ∈ frontier E) {κ : ℝ} (hκ : 0 < κ) :
    ∃ r : ℝ, 0 < r ∧ ∃ ν : V, ‖ν‖ = 1 ∧
      ∀ (ε : ℝ) (y y' q q' : V), ε ≤ r → y ∈ Metric.ball x₀ r → y' ∈ Metric.ball x₀ r →
        y ∉ E → y' ∉ E → q ∈ frontier E → q' ∈ frontier E → dist y q ≤ ε → dist y' q' ≤ ε →
        (∃ t : ℝ, y' = y + t • ν) → |inner ℝ ν (y - y')| ≤ Real.sqrt (1 + κ ^ 2) * ε := by
  obtain ⟨W, hW, hx₀W, φ, hφ, hdφ, hEW⟩ := hE x₀ hx₀
  have hφc : Continuous φ := hφ.continuous
  have hφd : ∀ z, DifferentiableAt ℝ φ z := fun z =>
    (hφ.differentiable one_ne_zero) z
  set L := fderiv ℝ φ x₀ with hLdef
  have hL : L ≠ 0 := hdφ x₀ hx₀W
  set g := (InnerProductSpace.toDual ℝ V).symm L with hgdef
  have hg : ∀ v, inner ℝ g v = L v := fun v => InnerProductSpace.toDual_symm_apply
  have hgn : ‖g‖ = ‖L‖ := LinearIsometryEquiv.norm_map _ _
  set a := ‖g‖ with ha_def
  have ha : 0 < a := by rw [hgn]; exact norm_pos_iff.2 hL
  set ν := a⁻¹ • g with hνdef
  have hν : ‖ν‖ = 1 := by
    rw [hνdef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ha]
    exact inv_mul_cancel₀ ha.ne'
  have hLν : ∀ v, L v = a * inner ℝ ν v := by
    intro v
    rw [← hg, hνdef, real_inner_smul_left]
    field_simp
  -- the slope constant
  set θ := min (1 / 4 : ℝ) (κ / (1 + κ)) with hθdef
  have hθ0 : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθ4 : θ ≤ 1 / 4 := min_le_left _ _
  have hθκ : θ ≤ κ * (1 - θ) := by
    have h1 : θ ≤ κ / (1 + κ) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  -- radius
  have hcont : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 (hcont.continuousAt (x := x₀)) (θ * a)
    (by positivity)
  obtain ⟨δ', hδ'0, hsub⟩ := Metric.isOpen_iff.1 hW x₀ hx₀W
  set r := min δ δ' / 4 with hrdef
  have hr : 0 < r := by positivity
  have hBsub : ball x₀ (4 * r) ⊆ ball x₀ δ ∩ ball x₀ δ' := by
    intro z hz
    have : 4 * r = min δ δ' := by rw [hrdef]; ring
    rw [this] at hz
    exact ⟨ball_subset_ball (min_le_left _ _) hz, ball_subset_ball (min_le_right _ _) hz⟩
  -- the slope condition
  set f : V → ℝ := fun z => φ z / a with hfdef
  have hf : Continuous f := hφc.div_const _
  have hK : ∀ y ∈ ball x₀ (4 * r), ∀ y' ∈ ball x₀ (4 * r),
      |f y' - f y - inner ℝ ν (y' - y)| ≤ θ * ‖y' - y‖ := by
    intro y hy y' hy'
    set ψ : V → ℝ := fun z => φ z - L z with hψ
    have hψd : ∀ z, HasFDerivAt ψ (fderiv ℝ φ z - L) z := fun z =>
      (hφd z).hasFDerivAt.sub L.hasFDerivAt
    have hmv := (convex_ball x₀ (4 * r)).norm_image_sub_le_of_norm_fderiv_le
      (f := ψ) (C := θ * a) (fun z _ => (hψd z).differentiableAt)
      (fun z hz => by
        rw [(hψd z).fderiv, ← dist_eq_norm]
        exact (hδ' (mem_ball.1 (hBsub hz).1)).le) hy hy'
    have heq : f y' - f y - inner ℝ ν (y' - y) = (ψ y' - ψ y) / a := by
      have : L (y' - y) = L y' - L y := map_sub _ _ _
      rw [hLν] at this
      simp only [hψ, hfdef]
      rw [hLν y', hLν y]
      rw [inner_sub_right] at this
      field_simp
      rw [inner_sub_right]
      ring
    rw [heq, abs_div, abs_of_pos ha, div_le_iff₀ ha]
    simpa [mul_comm, mul_assoc, mul_left_comm] using hmv
  refine ⟨r, hr, ν, hν, ?_⟩
  intro ε y y' q q' hε hy hy' hyE hy'E hq hq' hdq hdq' ⟨t, ht⟩
  have hε0 : 0 ≤ ε := dist_nonneg.trans hdq
  have hout : ∀ z ∈ ball x₀ (4 * r), z ∉ E → 0 ≤ f z := by
    intro z hz hzE
    have hzW : z ∈ W := hsub (hBsub hz).2
    have : 0 ≤ φ z := by
      by_contra h
      exact hzE (show z ∈ E ∩ W from hEW ▸ (⟨hzW, not_le.1 h⟩ : z ∈ {y | y ∈ W ∧ φ y < 0})).1
    exact div_nonneg this ha.le
  have hqB : ∀ {y q : V}, y ∈ ball x₀ r → dist y q ≤ ε → q ∈ ball x₀ (4 * r) := by
    intro y q hy hyq
    rw [mem_ball] at hy ⊢
    have := dist_triangle q y x₀
    rw [dist_comm q y] at this
    linarith
  have hfr : ∀ q ∈ frontier E, q ∈ ball x₀ (4 * r) → f q = 0 := by
    intro q hq hqB
    have := frontier_zero hEo hW hφc hEW hq (hsub (hBsub hqB).2)
    simp [hfdef, this]
  have hyB : y ∈ ball x₀ (4 * r) := ball_subset_ball (by linarith) hy
  have hy'B : y' ∈ ball x₀ (4 * r) := ball_subset_ball (by linarith) hy'
  obtain ⟨s, hs0, hsC, hfs, hsB⟩ := exists_zero_on_line hf hν hθ0 hθ4 hθκ hK hε hy
    (hqB hy hdq) (hfr q hq (hqB hy hdq)) (hout y hyB hyE) hdq
  obtain ⟨s', hs0', hsC', hfs', hsB'⟩ := exists_zero_on_line hf hν hθ0 hθ4 hθκ hK hε hy'
    (hqB hy' hdq') (hfr q' hq' (hqB hy' hdq')) (hout y' hy'B hy'E) hdq'
  -- uniqueness of the zero on the line
  have hcone := hK _ hsB _ hsB'
  rw [hfs, hfs'] at hcone
  set c := t - s' + s with hc
  have hvec : (y' - s' • ν) - (y - s • ν) = c • ν := by
    rw [ht, hc]; module
  rw [hvec, sub_zero, zero_sub, abs_neg, inner_smul_right, norm_smul, hν, mul_one,
    real_inner_self_eq_norm_sq, hν, Real.norm_eq_abs] at hcone
  have hc0 : c = 0 := by
    have h1 : |c| ≤ θ * |c| := by simpa using hcone
    have h2 : |c| = 0 := by
      by_contra hne
      have := abs_pos.2 (show c ≠ 0 from fun h => hne (by simp [h]))
      linarith [mul_le_mul_of_nonneg_right hθ4 (abs_nonneg c)]
    exact abs_eq_zero.1 h2
  have hyy : inner ℝ ν (y - y') = -t := by
    have : y - y' = (-t) • ν := by rw [ht]; module
    rw [this, inner_smul_right, real_inner_self_eq_norm_sq, hν]; ring
  rw [hyy, abs_neg]
  have ht' : t = s' - s := by linarith
  rw [ht']
  rw [abs_le]
  constructor <;> linarith

end Fibre

section Thickening

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A point of the closed `ε`-thickening of `closure E` outside `closure E` is within `ε` of the
frontier. -/
theorem exists_frontier_dist_le {E : Set V} (hEo : IsOpen E) (hEc : IsCompact (closure E)) {ε : ℝ}
    {y : V} (hy : y ∈ Metric.cthickening ε (closure E)) (hyE : y ∉ closure E) :
    ∃ q ∈ frontier E, dist y q ≤ ε := by
  have hne : (closure E).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, Metric.cthickening_empty] at hy
    exact hy
  have hpos : 0 < Metric.infDist y (closure E) :=
    (isClosed_closure.notMem_iff_infDist_pos hne).1 hyE
  have hle : Metric.infDist y (closure E) ≤ max ε 0 := by
    rw [Metric.mem_cthickening_iff] at hy
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hy
    rwa [ENNReal.toReal_ofReal'] at this
  have hε : 0 < ε := by
    by_contra h
    have : max ε 0 = 0 := max_eq_right (not_lt.1 h)
    linarith
  rw [max_eq_left hε.le] at hle
  obtain ⟨q, hqc, hqd⟩ := hEc.exists_infDist_eq_dist hne y
  have hqE : q ∉ E := by
    intro hqE
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hEo q hqE
    have hD : 0 < dist y q := hqd ▸ hpos
    set t : ℝ := min (1 / 2) (δ / (2 * dist q y)) with ht
    have hDq : 0 < dist q y := by rwa [dist_comm]
    have ht0 : 0 < t := lt_min (by norm_num) (by positivity)
    have ht1 : t ≤ 1 / 2 := min_le_left _ _
    set z := AffineMap.lineMap q y t with hz
    have hzq : dist z q = t * dist q y := by
      rw [hz, dist_lineMap_left, Real.norm_eq_abs, abs_of_pos ht0]
    have hzy : dist z y = (1 - t) * dist q y := by
      rw [hz, dist_lineMap_right, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have hzE : z ∈ E := hball (by
      rw [mem_ball, hzq]
      have : t ≤ δ / (2 * dist q y) := min_le_right _ _
      rw [le_div_iff₀ (by positivity)] at this
      linarith)
    have h1 := Metric.infDist_le_dist_of_mem (x := y) (subset_closure hzE)
    rw [hqd, dist_comm y z, hzy, dist_comm q y] at h1
    have : (1 - t) * dist y q < dist y q := by linarith [mul_pos ht0 hD]
    linarith
  refine ⟨q, ?_, by rw [← hqd]; exact hle⟩
  show q ∈ closure E \ interior E
  rw [hEo.interior_eq]
  exact ⟨hqc, hqE⟩

end Thickening

end PDE.IsoperimetricProof
