module

public import PDEFoundation.FunctionalInequalities.Isoperimetric.Chart
public import PDEFoundation.FunctionalInequalities.Isoperimetric.Slab
public import PDEFoundation.FunctionalInequalities.Isoperimetric.Grid

/-!
# The outer Minkowski content of a `C¹` boundary is at most its Hausdorff measure

For a bounded open `E ⊆ HilbertVec d` with `C¹` boundary `Σ` of finite `μHE[d-1]` measure,
`μHE[d](cthickening ε (closure E) \ closure E) ≤ ε (μHE[d-1] Σ + η)` for all small `ε > 0`.

The layer `T = cthickening ε (closure E) \ closure E` is cut by a generic grid of small cubes
(`exists_good_grid`), each lying in a chart ball of the fibre lemma (`exists_fibre_chart`, Lebesgue
number); in each cube the `ν`-fibres of `T` have length `≤ √(1+κ²) ε` and project into a hyperplane
thickening of `P(Σ ∩ cube)`, so the slab estimate (`slab_measure_le`) and the shrinking of the
hyperplane thickenings (`eventually_measure_hyperplaneThickening_le`) bound `|T ∩ cube|`.
-/

@[expose] public section

namespace PDE.IsoperimetricProof

open MeasureTheory Set Metric Module

variable {d : ℕ}

/-- A finite family of positive numbers has a positive lower bound. -/
theorem exists_pos_le_finset {ι : Type*} (J : Finset ι) (f : ι → ℝ) (hf : ∀ k ∈ J, 0 < f k) :
    ∃ c : ℝ, 0 < c ∧ ∀ k ∈ J, c ≤ f k := by
  classical
  induction J using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a J ha ih =>
    obtain ⟨c, hc, hcJ⟩ := ih fun k hk => hf k (Finset.mem_insert_of_mem hk)
    refine ⟨min c (f a), lt_min hc (hf a (Finset.mem_insert_self a J)), fun k hk => ?_⟩
    rcases Finset.mem_insert.1 hk with rfl | hk
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hcJ k hk)

theorem finrank_hilbertVec (d : ℕ) : finrank ℝ (HilbertVec d) = d := by
  simp only [finrank_euclideanSpace, Fintype.card_fin]

/-- **Minkowski content bound.** -/
theorem minkowski_content_le {E : Set (HilbertVec d)} (hEo : IsOpen E)
    (hEb : Bornology.IsBounded E) (hE : HasC1Frontier E)
    (hfin : (μHE[d - 1] : Measure (HilbertVec d)) (frontier E) ≠ ⊤) {η : ℝ} (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      (μHE[d] : Measure (HilbertVec d)) (cthickening ε (closure E) \ closure E) ≤
        ENNReal.ofReal ε * ((μHE[d - 1] : Measure (HilbertVec d)) (frontier E) +
          ENNReal.ofReal η) := by
  classical
  set Sg := frontier E with hSg
  set μ : Measure (HilbertVec d) := μHE[d - 1] with hμ
  have hfr := finrank_hilbertVec d
  have hSc : IsCompact Sg := hEb.isCompact_closure.of_isClosed_subset isClosed_frontier
    frontier_subset_closure
  have hEc : IsCompact (closure E) := hEb.isCompact_closure
  set Hr : ℝ := (μ Sg).toReal with hHr
  have hH : μ Sg = ENNReal.ofReal Hr := (ENNReal.ofReal_toReal hfin).symm
  have hHr0 : 0 ≤ Hr := ENNReal.toReal_nonneg
  -- the slope constant `c = √(1+κ²)`
  set c : ℝ := (Hr + η) / (Hr + η / 2) with hc
  have hden : 0 < Hr + η / 2 := by linarith
  have hc1 : 1 < c := by rw [hc, one_lt_div hden]; linarith
  set κ : ℝ := Real.sqrt (c ^ 2 - 1) with hκ
  have hκ0 : 0 < κ := Real.sqrt_pos.2 (by nlinarith)
  have hsq : Real.sqrt (1 + κ ^ 2) = c := by
    rw [hκ, Real.sq_sqrt (by nlinarith), show 1 + (c ^ 2 - 1) = c ^ 2 by ring,
      Real.sqrt_sq (by linarith)]
  -- charts
  choose! r hr ν hν hfib using fun σ (hσ : σ ∈ Sg) => exists_fibre_chart hEo hE hσ hκ0
  obtain ⟨lam, hlam, hleb⟩ := lebesgue_number_lemma_of_metric (c := fun σ : Sg => ball σ.1 (r σ))
    hSc (fun _ => isOpen_ball) (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self (hr x hx)⟩)
  -- grid
  obtain ⟨δ, hδ, J, Q, Qc, hQm, hQc, hQQc, hcover, hQball, hsum⟩ :=
    exists_good_grid μ hSc hfin hlam
  have hcell : ∀ k ∈ J, ∃ σ ∈ Sg, Qc k ⊆ ball σ (r σ) := by
    intro k hk
    obtain ⟨σ', hσ', hsub⟩ := hQball k hk
    obtain ⟨⟨σ, hσ⟩, hball⟩ := hleb σ' hσ'
    exact ⟨σ, hσ, hsub.trans hball⟩
  choose! σk hσk hσkball using hcell
  obtain ⟨η', hη'⟩ : ∃ η' : ℝ, η' = η / (2 * ((J.card : ℝ) + 1)) := ⟨_, rfl⟩
  have hη'0 : 0 < η' := by
    rw [hη']
    exact div_pos hη (mul_pos two_pos (Nat.cast_add_one_pos _))
  have hthick : ∀ k ∈ J, ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ →
      μ {p | inner ℝ (ν (σk k)) p = 0 ∧ ∃ q ∈ Sg ∩ cthickening ε (Qc k),
        dist p (perpProj (ν (σk k)) q) ≤ ε} ≤ μ (Sg ∩ Qc k) + ENNReal.ofReal η' := by
    intro k hk
    obtain ⟨ε₁, hε₁, h⟩ := eventually_measure_hyperplaneThickening_le (hν _ (hσk k hk)) hSc
      (hQc k) hη'0
    refine ⟨ε₁, hε₁, fun ε hε hεle => ?_⟩
    have h1 := h ε hε hεle
    rw [hfr] at h1
    refine h1.trans (add_le_add_left ?_ _)
    exact euclideanHausdorffMeasure_perpProj_image_le (hν _ (hσk k hk)) _ _
  choose! ε₁ hε₁ hε₁b using hthick
  obtain ⟨ε₂, hε₂, hε₂le⟩ := exists_pos_le_finset J (fun k => min (ε₁ k) (r (σk k)))
    fun k hk => lt_min (hε₁ k hk) (hr _ (hσk k hk))
  refine ⟨min δ ε₂, lt_min hδ hε₂, fun ε hε hεle => ?_⟩
  have hεδ : ε ≤ δ := hεle.trans (min_le_left _ _)
  have hεk : ∀ k ∈ J, ε ≤ ε₁ k ∧ ε ≤ r (σk k) := fun k hk =>
    ⟨(hεle.trans (min_le_right _ _)).trans ((hε₂le k hk).trans (min_le_left _ _)),
      (hεle.trans (min_le_right _ _)).trans ((hε₂le k hk).trans (min_le_right _ _))⟩
  set T := cthickening ε (closure E) \ closure E with hT
  have hTm : MeasurableSet T :=
    isClosed_cthickening.measurableSet.diff isClosed_closure.measurableSet
  have hnear : ∀ y ∈ T, ∃ q ∈ Sg, dist y q ≤ ε := fun y hy =>
    exists_frontier_dist_le hEo hEc hy.1 hy.2
  have hTcov : T ⊆ ⋃ k ∈ J, T ∩ Q k := by
    intro y hy
    obtain ⟨q, hq, hyq⟩ := hnear y hy
    have hyδ : y ∈ cthickening δ Sg :=
      cthickening_mono hεδ Sg (mem_cthickening_of_dist_le y q ε Sg hq hyq)
    obtain ⟨k, hk, hyk⟩ := mem_iUnion₂.1 (hcover hyδ)
    exact mem_iUnion₂.2 ⟨k, hk, hy, hyk⟩
  -- the bound on each cube
  have hpiece : ∀ k ∈ J, (μHE[d] : Measure (HilbertVec d)) (T ∩ Q k) ≤
      ENNReal.ofReal (c * ε) * (μ (Sg ∩ Qc k) + ENNReal.ofReal η') := by
    intro k hk
    set νk := ν (σk k)
    have hνk : ‖νk‖ = 1 := hν _ (hσk k hk)
    have hslab := slab_measure_le hνk (M := T ∩ Q k)
      (A := {p | inner ℝ νk p = 0 ∧ ∃ q ∈ Sg ∩ cthickening ε (Qc k), dist p (perpProj νk q) ≤ ε})
      (hTm.inter (hQm k)) (fun a ha => ha.1) (L := c * ε) (by positivity) ?_ ?_
    · rw [hfr] at hslab
      refine hslab.trans ?_
      gcongr
      exact hε₁b k hk ε hε (hεk k hk).1
    · rintro y ⟨hyT, hyQ⟩
      obtain ⟨q, hq, hyq⟩ := hnear y hyT
      refine ⟨inner_perpProj hνk y, q, ⟨hq, ?_⟩, ?_⟩
      · exact mem_cthickening_of_dist_le q y ε (Qc k) (hQQc k hyQ) (by rwa [dist_comm])
      · rw [dist_eq_norm, perpProj_sub]
        exact (norm_perpProj_le hνk _).trans (by rwa [← dist_eq_norm])
    · rintro y ⟨hyT, hyQ⟩ y' ⟨hy'T, hy'Q⟩ hP
      obtain ⟨q, hq, hyq⟩ := hnear y hyT
      obtain ⟨q', hq', hy'q'⟩ := hnear y' hy'T
      have hball := hσkball k hk
      have hline : ∃ t : ℝ, y' = y + t • νk := by
        refine ⟨inner ℝ νk (y' - y), ?_⟩
        have h0 : perpProj νk (y' - y) = 0 := by rw [← perpProj_sub, hP, sub_self]
        have : y' - y - inner ℝ νk (y' - y) • νk = 0 := h0
        rw [sub_eq_zero] at this
        rw [← this]
        abel
      have := hfib (σk k) (hσk k hk) ε y y' q q' (hεk k hk).2 (hball (hQQc k hyQ))
        (hball (hQQc k hy'Q)) (fun h => hyT.2 (subset_closure h))
        (fun h => hy'T.2 (subset_closure h)) hq hq' hyq hy'q' hline
      rwa [hsq] at this
  -- summing up
  have hcε : ENNReal.ofReal (c * ε) = ENNReal.ofReal ε * ENNReal.ofReal c := by
    rw [mul_comm, ENNReal.ofReal_mul hε.le]
  calc (μHE[d] : Measure (HilbertVec d)) T
      ≤ (μHE[d] : Measure (HilbertVec d)) (⋃ k ∈ J, T ∩ Q k) := measure_mono hTcov
    _ ≤ ∑ k ∈ J, (μHE[d] : Measure (HilbertVec d)) (T ∩ Q k) := measure_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ J, ENNReal.ofReal (c * ε) * (μ (Sg ∩ Qc k) + ENNReal.ofReal η') :=
        Finset.sum_le_sum hpiece
    _ = ENNReal.ofReal (c * ε) * (∑ k ∈ J, μ (Sg ∩ Qc k) + J.card * ENNReal.ofReal η') := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (c * ε) * (μ Sg + ENNReal.ofReal (η / 2)) := by
        gcongr
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hη', mul_div_assoc', div_le_div_iff₀ (mul_pos two_pos (Nat.cast_add_one_pos _))
          two_pos]
        have hJ0 : (0 : ℝ) ≤ J.card := Nat.cast_nonneg _
        nlinarith
    _ = ENNReal.ofReal ε * (μ Sg + ENNReal.ofReal η) := by
        rw [hcε, hH, ← ENNReal.ofReal_add hHr0 (by positivity),
          ← ENNReal.ofReal_add hHr0 hη.le, mul_assoc, ← ENNReal.ofReal_mul (by linarith)]
        congr 2
        rw [hc]
        field_simp

end PDE.IsoperimetricProof
