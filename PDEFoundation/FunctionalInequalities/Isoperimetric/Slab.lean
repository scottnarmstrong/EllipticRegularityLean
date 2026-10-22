module

public import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# Slab Fubini bound and projection lemmas

Measure-theoretic facts about the orthogonal projection `perpProj ν` onto the hyperplane `νᗮ`
used by the isoperimetric argument.
-/

@[expose] public section

namespace PDE.IsoperimetricProof

open MeasureTheory Set Module
open scoped MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Orthogonal projection onto `νᗮ` for a unit vector `ν`. -/
def perpProj (ν y : V) : V := y - inner ℝ ν y • ν

omit [FiniteDimensional ℝ V] in
/-- A subset of a line direction `ν` with pairwise `ν`-distances `≤ L` has `μHE[1]`-measure `≤ L`. -/
theorem euclideanHausdorffMeasure_one_le {ν : V} (hν : ‖ν‖ = 1) {F : Set V} {L : ℝ}
    (hF : ∀ y ∈ F, ∀ y' ∈ F, ∃ c : ℝ, y - y' = c • ν ∧ |c| ≤ L) :
    (μHE[1] : Measure V) F ≤ ENNReal.ofReal L := by
  rcases F.eq_empty_or_nonempty with rfl | ⟨y0, hy0⟩
  · simp
  let g : ℝ → V := fun t => y0 + t • ν
  have hg : Isometry g := by
    refine Isometry.of_dist_eq fun a b => ?_
    simp [g, dist_eq_norm, ← sub_smul, norm_smul, hν, Real.norm_eq_abs]
  set T : Set ℝ := g ⁻¹' F with hT
  have hFT : F ⊆ g '' T := by
    intro y hy
    obtain ⟨c, hc, -⟩ := hF y hy y0 hy0
    refine ⟨c, ?_, ?_⟩
    · simp only [hT, mem_preimage, g]
      rw [show y0 + c • ν = y by rw [← hc]; abel]; exact hy
    · simp only [g]; rw [← hc]; abel
  have himg : g '' T ⊆ F := image_preimage_subset _ _
  have h1 : (μHE[1] : Measure V) F = μHE[1] (g '' T) :=
    le_antisymm (measure_mono hFT) (measure_mono himg)
  have hR : (μHE[1] : Measure ℝ) = volume := by
    simpa using (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℝ))
  rw [h1, hg.euclideanHausdorffMeasure_image, hR]
  refine (Real.volume_le_diam T).trans ?_
  refine Metric.ediam_le fun a ha b hb => ?_
  obtain ⟨c, hc, hcL⟩ := hF _ ha _ hb
  have hab : (a - b) • ν = c • ν := by
    rw [sub_smul]; simpa [g] using hc
  have hcab : a - b = c := by
    have := smul_left_injective ℝ (show ν ≠ 0 by intro h; simp [h] at hν) hab
    exact this
  rw [edist_dist, Real.dist_eq, hcab]
  exact ENNReal.ofReal_le_ofReal hcL

/-- Hyperplane `νᗮ` as an affine subspace. -/
private noncomputable abbrev hyperplane (ν : V) : AffineSubspace ℝ V := (ℝ ∙ ν)ᗮ.toAffineSubspace

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem direction_hyperplane (ν : V) : (hyperplane ν).direction = (ℝ ∙ ν)ᗮ := by
  simp [hyperplane]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem perpProj_eq_of_mem {ν : V} (hν : ‖ν‖ = 1) {x y : V} (hx : inner ℝ ν x = 0)
    (hy : y ∈ AffineSubspace.mk' x (ℝ ∙ ν)) : perpProj ν y = x := by
  rw [AffineSubspace.mem_mk', vsub_eq_sub, Submodule.mem_span_singleton] at hy
  obtain ⟨a, ha⟩ := hy
  have hy' : y = x + a • ν := by rw [ha]; abel
  have hnu : inner ℝ ν ν = 1 := by
    rw [real_inner_self_eq_norm_sq, hν]; norm_num
  have : inner ℝ ν y = a := by
    rw [hy', inner_add_right, hx, inner_smul_right, hnu]; ring
  rw [perpProj, this, hy']
  abel_nf

/-- Slab Fubini: a measurable set whose `ν`-fibres have length `≤ L` and whose projection lies in
`A ⊆ νᗮ` has `d`-volume at most `L · μHE[d-1] A`. -/
theorem slab_measure_le {ν : V} (hν : ‖ν‖ = 1) {M A : Set V} (hM : MeasurableSet M)
    (_hA : ∀ a ∈ A, inner ℝ ν a = 0) {L : ℝ} (_hL : 0 ≤ L) (hMA : ∀ y ∈ M, perpProj ν y ∈ A)
    (hfib : ∀ y ∈ M, ∀ y' ∈ M, perpProj ν y = perpProj ν y' → |inner ℝ ν (y - y')| ≤ L) :
    (μHE[Module.finrank ℝ V] : Measure V) M ≤
      ENNReal.ofReal L * (μHE[Module.finrank ℝ V - 1] : Measure V) A := by
  have hν0 : ν ≠ 0 := by intro h; simp [h] at hν
  have : Nonempty (hyperplane ν) := ⟨⟨0, by simp [hyperplane]⟩⟩
  rw [AffineSubspace.euclideanHausdorffMeasure_eq_lintegral (hyperplane ν) hM]
  have hd : (hyperplane ν).directionᗮ = ℝ ∙ ν := by
    rw [direction_hyperplane, Submodule.orthogonal_orthogonal]
  have h1 : finrank ℝ (hyperplane ν).directionᗮ = 1 := by
    rw [hd, finrank_span_singleton hν0]
  have h2 : finrank ℝ (hyperplane ν).direction = finrank ℝ V - 1 := by
    have := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ ν)
    rw [finrank_span_singleton hν0] at this
    rw [direction_hyperplane]; omega
  rw [h1, h2]
  have hpt : ∀ x : hyperplane ν, (μHE[1] : Measure V) (M ∩ AffineSubspace.mk' x.val
      (hyperplane ν).directionᗮ) ≤
      Set.indicator (Subtype.val ⁻¹' A) (fun _ => ENNReal.ofReal L) x := by
    intro x
    have hx : inner ℝ ν x.val = 0 := by
      have h : x.val ∈ (ℝ ∙ ν)ᗮ := x.2
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp h
    rw [hd]
    by_cases hxA : x ∈ Subtype.val ⁻¹' A
    · rw [Set.indicator_of_mem hxA]
      refine euclideanHausdorffMeasure_one_le hν (fun y hy y' hy' => ?_)
      have e1 := perpProj_eq_of_mem hν hx hy.2
      have e2 := perpProj_eq_of_mem hν hx hy'.2
      have hle := hfib y hy.1 y' hy'.1 (e1.trans e2.symm)
      have hy2 := hy.2
      have hy2' := hy'.2
      rw [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub,
        Submodule.mem_span_singleton] at hy2 hy2'
      obtain ⟨a, ha⟩ := hy2
      obtain ⟨a', ha'⟩ := hy2'
      have hnu : inner ℝ ν ν = 1 := by
        rw [real_inner_self_eq_norm_sq, hν]; norm_num
      have hyy : y - y' = (a - a') • ν := by
        rw [sub_smul, ha, ha']; abel
      refine ⟨a - a', hyy, ?_⟩
      rwa [hyy, inner_smul_right, hnu, mul_one] at hle
    · rw [Set.indicator_of_notMem hxA]
      have : M ∩ AffineSubspace.mk' x.val (ℝ ∙ ν) = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun y hy => hxA ?_
        have := hMA y hy.1
        rwa [perpProj_eq_of_mem hν hx hy.2] at this
      rw [this]; simp
  refine (lintegral_mono hpt).trans ?_
  refine (lintegral_indicator_const_le _ _).trans ?_
  gcongr
  have hsub : (Subtype.val : hyperplane ν → V) '' (Subtype.val ⁻¹' A) ⊆ A :=
    Set.image_preimage_subset _ _
  rw [← AffineSubspace.euclideanHausdorffMeasure_coe_image]
  exact measure_mono hsub

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem perpProj_sub {ν : V} (y y' : V) : perpProj ν y - perpProj ν y' = perpProj ν (y - y') := by
  simp [perpProj, inner_sub_right, sub_smul]; abel

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem norm_perpProj_le {ν : V} (hν : ‖ν‖ = 1) (y : V) : ‖perpProj ν y‖ ≤ ‖y‖ := by
  have hnu : inner ℝ ν ν = 1 := by
    rw [real_inner_self_eq_norm_sq, hν]; norm_num
  have h : ‖perpProj ν y‖ ^ 2 = ‖y‖ ^ 2 - (inner ℝ ν y) ^ 2 := by
    rw [perpProj, norm_sub_sq_real, inner_smul_right, norm_smul, hν, Real.norm_eq_abs, mul_one,
      real_inner_comm ν y]
    nlinarith [sq_abs (inner ℝ ν y)]
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  nlinarith [sq_nonneg (inner ℝ ν y)]

omit [FiniteDimensional ℝ V] in
/-- The projection is `1`-Lipschitz, so it does not increase Hausdorff measure. -/
theorem euclideanHausdorffMeasure_perpProj_image_le {ν : V} (hν : ‖ν‖ = 1) (k : ℕ) (K : Set V) :
    (μHE[k] : Measure V) (perpProj ν '' K) ≤ μHE[k] K := by
  have hlip : LipschitzWith 1 (perpProj ν : V → V) := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simpa [dist_eq_norm, perpProj_sub] using norm_perpProj_le hν (a - b)
  simp_rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
  refine smul_le_smul_of_nonneg_left ?_ (zero_le)
  simpa using hlip.hausdorffMeasure_image_le (d := (k : ℝ)) (by positivity) K

omit [MeasurableSpace V] [BorelSpace V] in
theorem finrank_perp {ν : V} (hν : ‖ν‖ = 1) : finrank ℝ (ℝ ∙ ν)ᗮ = finrank ℝ V - 1 := by
  have hν0 : ν ≠ 0 := by intro h; simp [h] at hν
  have := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ ν)
  rw [finrank_span_singleton hν0] at this
  omega

/-- A compact subset of the hyperplane `νᗮ` has finite `μHE[d-1]`-measure. -/
theorem measure_lt_top_of_isCompact_perp {ν : V} (hν : ‖ν‖ = 1) {t : Set V} (ht : IsCompact t)
    (hsub : ∀ p ∈ t, inner ℝ ν p = 0) : (μHE[finrank ℝ V - 1] : Measure V) t < ⊤ := by
  let t' : Set (ℝ ∙ ν)ᗮ := Subtype.val ⁻¹' t
  have himg : Subtype.val '' t' = t := by
    refine Set.image_preimage_eq_of_subset fun p hp => ?_
    simpa [Submodule.mem_orthogonal_singleton_iff_inner_right] using hsub p hp
  have hc : IsCompact t' := Subtype.isCompact_iff.2 (by rw [himg]; exact ht)
  rw [← himg, isometry_subtype_coe.euclideanHausdorffMeasure_image, ← finrank_perp hν,
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  exact hc.measure_lt_top

section Thickening

variable {ν : V} {S C : Set V}

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem continuous_perpProj (ν : V) : Continuous (perpProj ν : V → V) := by
  unfold perpProj; fun_prop

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem inner_perpProj {ν : V} (hν : ‖ν‖ = 1) (y : V) : inner ℝ ν (perpProj ν y) = 0 := by
  have hnu : inner ℝ ν ν = 1 := by
    rw [real_inner_self_eq_norm_sq, hν]; norm_num
  simp [perpProj, inner_sub_right, inner_smul_right, hν]

/-- The thickened projection set. -/
def thick (ν : V) (S C : Set V) (ε : ℝ) : Set V :=
  {p | inner ℝ ν p = 0 ∧ ∃ q ∈ S ∩ Metric.cthickening ε C, dist p (perpProj ν q) ≤ ε}

omit [MeasurableSpace V] [BorelSpace V] in
theorem thick_isCompact (hS : IsCompact S) {ε : ℝ} :
    IsCompact (thick ν S C ε) := by
  have hK : IsCompact (S ∩ Metric.cthickening ε C) := hS.inter_right Metric.isClosed_cthickening
  have himg : IsCompact ((fun x : V × V => perpProj ν x.1 + x.2) ''
      ((S ∩ Metric.cthickening ε C) ×ˢ Metric.closedBall (0 : V) ε)) :=
    (hK.prod (isCompact_closedBall 0 ε)).image
      (by have := continuous_perpProj ν; fun_prop)
  have hH : IsClosed {p : V | inner ℝ ν p = 0} :=
    isClosed_eq (by fun_prop) continuous_const
  have : thick ν S C ε = ((fun x : V × V => perpProj ν x.1 + x.2) ''
      ((S ∩ Metric.cthickening ε C) ×ˢ Metric.closedBall (0 : V) ε)) ∩ {p | inner ℝ ν p = 0} := by
    ext p
    constructor
    · rintro ⟨hp, q, hq, hd⟩
      refine ⟨⟨(q, p - perpProj ν q), ⟨hq, ?_⟩, by simp⟩, hp⟩
      rw [mem_closedBall_zero_iff, ← dist_eq_norm]; exact hd
    · rintro ⟨⟨⟨q, w⟩, ⟨hq, hw⟩, rfl⟩, hp⟩
      refine ⟨hp, q, hq, ?_⟩
      rw [dist_eq_norm]
      simpa using mem_closedBall_zero_iff.1 hw
  rw [this]; exact himg.inter_right hH

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem thick_mono {ε ε' : ℝ} (h : ε ≤ ε') : thick ν S C ε ⊆ thick ν S C ε' := by
  rintro p ⟨hp, q, ⟨hqS, hqC⟩, hd⟩
  exact ⟨hp, q, ⟨hqS, Metric.cthickening_mono h C hqC⟩, hd.trans h⟩

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem iInter_thick (hν : ‖ν‖ = 1) (hS : IsCompact S) (hC : IsClosed C) :
    (⋂ m : ℕ, thick ν S C (1 / ((m : ℝ) + 1))) = perpProj ν '' (S ∩ C) := by
  ext p
  simp only [mem_iInter]
  constructor
  · intro hp
    let t : ℕ → Set V := fun m => S ∩ Metric.cthickening (1 / ((m : ℝ) + 1)) C ∩
      {q | dist p (perpProj ν q) ≤ 1 / ((m : ℝ) + 1)}
    have hmono : ∀ m : ℕ, t (m + 1) ⊆ t m := by
      intro m q ⟨⟨hqS, hqC⟩, hd⟩
      have : 1 / (((m + 1 : ℕ) : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
        gcongr; simp
      exact ⟨⟨hqS, Metric.cthickening_mono this C hqC⟩, hd.trans this⟩
    have hcl : ∀ m, IsClosed (t m) := fun m =>
      (hS.isClosed.inter Metric.isClosed_cthickening).inter
        (isClosed_le (continuous_const.dist (continuous_perpProj ν)) continuous_const)
    have hne : ∀ m, (t m).Nonempty := fun m => by
      obtain ⟨-, q, hq, hd⟩ := hp m
      exact ⟨q, hq, hd⟩
    obtain ⟨q, hq⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t hmono
      hne (hS.inter_right (Metric.isClosed_cthickening.inter
        (isClosed_le (continuous_const.dist (continuous_perpProj ν)) continuous_const)) |>.of_isClosed_subset
        (hcl 0) (by intro x hx; exact ⟨hx.1.1, hx.1.2, hx.2⟩)) hcl
    rw [mem_iInter] at hq
    have hqS : q ∈ S := (hq 0).1.1
    have hlim : ∀ δ : ℝ, 0 < δ → ∃ m : ℕ, 1 / ((m : ℝ) + 1) < δ := fun δ hδ => by
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
      exact ⟨m, hm⟩
    have hqC : q ∈ C := by
      rw [← hC.closure_eq, Metric.closure_eq_iInter_cthickening]
      simp only [mem_iInter]
      intro δ hδ
      obtain ⟨m, hm⟩ := hlim δ hδ
      exact Metric.cthickening_mono hm.le C (hq m).1.2
    refine ⟨q, ⟨hqS, hqC⟩, ?_⟩
    by_contra hne'
    have hpos : 0 < dist p (perpProj ν q) := dist_pos.2 (Ne.symm hne')
    obtain ⟨m, hm⟩ := hlim _ hpos
    exact absurd (hq m).2 (not_le.2 hm)
  · rintro ⟨q, ⟨hqS, hqC⟩, rfl⟩ m
    refine ⟨inner_perpProj hν q, q, ⟨hqS, Metric.self_subset_cthickening _ hqC⟩, ?_⟩
    simp; positivity

end Thickening

/-- Thickenings inside the hyperplane shrink to the projection. -/
theorem eventually_measure_hyperplaneThickening_le {ν : V} (hν : ‖ν‖ = 1) {S C : Set V}
    (hS : IsCompact S) (hC : IsClosed C) {η : ℝ} (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      (μHE[Module.finrank ℝ V - 1] : Measure V)
          {p | inner ℝ ν p = 0 ∧ ∃ q ∈ S ∩ Metric.cthickening ε C, dist p (perpProj ν q) ≤ ε} ≤
        (μHE[Module.finrank ℝ V - 1] : Measure V) (perpProj ν '' (S ∩ C)) + ENNReal.ofReal η := by
  set μ : Measure V := μHE[Module.finrank ℝ V - 1] with hμ
  set B : ℕ → Set V := fun m => thick ν S C (1 / ((m : ℝ) + 1)) with hB
  have hBc : ∀ m, IsCompact (B m) := fun m => thick_isCompact hS
  have hBanti : Antitone B := fun m m' h => thick_mono (by gcongr)
  have hfin : ∀ m, μ (B m) < ⊤ := fun m =>
    measure_lt_top_of_isCompact_perp hν (hBc m) fun p hp => hp.1
  have hlim := tendsto_measure_iInter_atTop (μ := μ) (s := B)
    (fun m => (hBc m).isClosed.measurableSet.nullMeasurableSet) hBanti ⟨0, (hfin 0).ne⟩
  have hI : (⋂ m, B m) = perpProj ν '' (S ∩ C) := iInter_thick hν hS hC
  rw [hI] at hlim
  have hPfin : μ (perpProj ν '' (S ∩ C)) ≠ ⊤ := by
    rw [← hI]; exact ((measure_mono (iInter_subset B 0)).trans_lt (hfin 0)).ne
  have hlt : μ (perpProj ν '' (S ∩ C)) < μ (perpProj ν '' (S ∩ C)) + ENNReal.ofReal η :=
    ENNReal.lt_add_right hPfin (by simpa using hη)
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hlt)).exists_forall_of_atTop
  refine ⟨1 / ((N : ℝ) + 1), by positivity, fun ε hε hεN => ?_⟩
  exact (measure_mono (thick_mono hεN)).trans (hN N le_rfl).le

end PDE.IsoperimetricProof
