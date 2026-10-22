module

public import PDEFoundation.Monotonicity.Defs
public import PDEFoundation.Geometry.EuclideanBall.Topology

/-!
# Friedland--Hayman: basic facts

Monotonicity of the spherical Dirichlet eigenvalue in the domain, its value `⊤` on the empty set,
monotonicity and explicit formula of `eigenvalueDegree`, and the reduction of the disjoint form
of the Friedland--Hayman inequality to the complementary form.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE.FHLane

noncomputable section

theorem sphereDirichletEigenvalue_antitone {d : ℕ} {Ω Ω' : Set (Vec d)} (h : Ω ⊆ Ω') :
    sphereDirichletEigenvalue d Ω' ≤ sphereDirichletEigenvalue d Ω := by
  unfold sphereDirichletEigenvalue
  refine le_iInf fun f => le_iInf fun hf => ?_
  exact iInf₂_le_of_le f ⟨hf.1, hf.2.1.trans h, hf.2.2⟩ le_rfl

theorem sphereDirichletEigenvalue_empty (d : ℕ) : sphereDirichletEigenvalue d ∅ = ⊤ := by
  refine top_unique ?_
  unfold sphereDirichletEigenvalue
  refine le_iInf fun f => le_iInf fun hf => ?_
  exfalso
  obtain ⟨-, hc, hpos⟩ := hf
  have hz : ∀ x ∈ euclideanSphere (0 : Vec d) 1, f x = 0 := by
    intro x hx
    by_contra hne
    exact (hc (subset_closure ⟨hx, hne⟩) : x ∈ (∅ : Set (Vec d)))
  have h0 : sphereIntegral (0 : Vec d) 1 (fun x => f x ^ 2) = 0 := by
    unfold sphereIntegral
    have : ∀ ω : Metric.sphere (0 : HilbertVec d) 1,
        f ((0 : Vec d) + (1 : ℝ) • (ω : HilbertVec d).toVec) ^ 2 = 0 := by
      intro ω
      have hn : ‖(ω : HilbertVec d)‖ = 1 := by simp
      rw [HilbertVec.norm_eq_vecEuclideanNorm] at hn
      have hmem : (0 : Vec d) + (1 : ℝ) • (ω : HilbertVec d).toVec ∈
          euclideanSphere (0 : Vec d) 1 := by
        have hsq := vecEuclideanNorm_sq (ω : HilbertVec d).toVec
        rw [hn] at hsq
        simp only [euclideanSphere, Set.mem_ofPred_eq, euclideanSqDist, zero_add, one_smul, sub_zero]
        linarith
      rw [hz _ hmem]; norm_num
    simp only [zero_add, one_smul] at this
    simp [this]
  exact hpos.ne' h0

theorem eigenvalueDegree_mono (d : ℕ) {l l' : ℝ≥0∞} (h : l ≤ l') :
    eigenvalueDegree d l ≤ eigenvalueDegree d l' :=
  sSup_le_sSup fun _ ha => ha.trans h

theorem eigenvalueDegree_top (d : ℕ) : eigenvalueDegree d ⊤ = ⊤ := by
  unfold eigenvalueDegree
  have : {a : ℝ≥0∞ | a * (a + ((d - 2 : ℕ) : ℝ≥0∞)) ≤ ⊤} = Set.univ := by
    ext a; simp
  rw [this, sSup_univ]

private theorem real_aux (κ L a : ℝ) (hκ : 0 ≤ κ) (hL : 0 ≤ L) (ha : 0 ≤ a) :
    a * (a + κ) ≤ L ↔ a ≤ -(κ / 2) + Real.sqrt ((κ / 2) ^ 2 + L) := by
  have h1 : a ≤ -(κ / 2) + Real.sqrt ((κ / 2) ^ 2 + L) ↔
      a + κ / 2 ≤ Real.sqrt ((κ / 2) ^ 2 + L) := by constructor <;> intro h <;> linarith
  rw [h1, Real.le_sqrt (by positivity)]
  · constructor <;> intro h <;> nlinarith
  · exact add_nonneg (sq_nonneg _) hL

private theorem degree_set_eq (d : ℕ) {l : ℝ≥0∞} (hl : l ≠ ⊤) :
    {a : ℝ≥0∞ | a * (a + ((d - 2 : ℕ) : ℝ≥0∞)) ≤ l} =
      Set.Iic (ENNReal.ofReal (-(((d - 2 : ℕ) : ℝ) / 2) +
        Real.sqrt ((((d - 2 : ℕ) : ℝ) / 2) ^ 2 + l.toReal))) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_Iic]
  have hκ : (0 : ℝ) ≤ ((d - 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  induction x using ENNReal.recTopCoe with
  | top =>
    simp only [top_le_iff, ENNReal.ofReal_ne_top, iff_false, not_le]
    have : (⊤ : ℝ≥0∞) * (⊤ + ((d - 2 : ℕ) : ℝ≥0∞)) = ⊤ := by simp
    rw [this]
    exact lt_top_iff_ne_top.2 hl
  | coe a =>
    have key : (a : ℝ≥0∞) * ((a : ℝ≥0∞) + ((d - 2 : ℕ) : ℝ≥0∞)) =
        ENNReal.ofReal ((a : ℝ) * ((a : ℝ) + ((d - 2 : ℕ) : ℝ))) := by
      rw [ENNReal.ofReal_mul a.coe_nonneg, ENNReal.ofReal_add a.coe_nonneg hκ,
        ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_natCast]
    rw [key, ENNReal.ofReal_le_iff_le_toReal hl, ← ENNReal.ofReal_coe_nnreal (p := a),
      ENNReal.ofReal_le_ofReal_iff]
    · exact real_aux _ _ _ hκ ENNReal.toReal_nonneg a.coe_nonneg
    · have := Real.sqrt_le_sqrt (show (((d - 2 : ℕ) : ℝ) / 2) ^ 2 ≤
        (((d - 2 : ℕ) : ℝ) / 2) ^ 2 + l.toReal by linarith [@ENNReal.toReal_nonneg l])
      rw [Real.sqrt_sq (by positivity)] at this
      linarith

theorem le_eigenvalueDegree_iff (d : ℕ) {l : ℝ≥0∞} (hl : l ≠ ⊤) {a : ℝ} (ha : 0 ≤ a) :
    ENNReal.ofReal a ≤ eigenvalueDegree d l ↔ a * (a + ((d - 2 : ℕ) : ℝ)) ≤ l.toReal := by
  have hκ : (0 : ℝ) ≤ ((d - 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold eigenvalueDegree
  rw [degree_set_eq d hl, csSup_Iic, ENNReal.ofReal_le_ofReal_iff]
  · exact (real_aux _ _ _ hκ ENNReal.toReal_nonneg ha).symm
  · have := Real.sqrt_le_sqrt (show (((d - 2 : ℕ) : ℝ) / 2) ^ 2 ≤
        (((d - 2 : ℕ) : ℝ) / 2) ^ 2 + l.toReal by linarith [@ENNReal.toReal_nonneg l])
    rw [Real.sqrt_sq (by positivity)] at this
    linarith

theorem eigenvalueDegree_eq (d : ℕ) {l : ℝ≥0∞} (hl : l ≠ ⊤) :
    eigenvalueDegree d l = ENNReal.ofReal (-(((d - 2 : ℕ) : ℝ) / 2) +
      Real.sqrt ((((d - 2 : ℕ) : ℝ) / 2) ^ 2 + l.toReal)) := by
  unfold eigenvalueDegree
  rw [degree_set_eq d hl, csSup_Iic]

/-- The disjoint form follows from the complementary form. -/
theorem of_disjoint_of_complementary (d : ℕ)
    (hFH : ∀ Ωp Ωm : Set (Vec d),
      (∃ U : Set (Vec d), IsOpen U ∧ Ωp = U ∩ euclideanSphere (0 : Vec d) 1) →
      (∃ U : Set (Vec d), IsOpen U ∧ Ωm = U ∩ euclideanSphere (0 : Vec d) 1) →
      Disjoint Ωp Ωm → closure Ωp ∪ closure Ωm = euclideanSphere (0 : Vec d) 1 →
      2 ≤ eigenvalueDegree d (sphereDirichletEigenvalue d Ωp) +
        eigenvalueDegree d (sphereDirichletEigenvalue d Ωm))
    (Ωp Ωm : Set (Vec d))
    (hp : ∃ U : Set (Vec d), IsOpen U ∧ Ωp = U ∩ euclideanSphere (0 : Vec d) 1)
    (hm : ∃ U : Set (Vec d), IsOpen U ∧ Ωm = U ∩ euclideanSphere (0 : Vec d) 1)
    (hdisj : Disjoint Ωp Ωm) :
    2 ≤ eigenvalueDegree d (sphereDirichletEigenvalue d Ωp) +
      eigenvalueDegree d (sphereDirichletEigenvalue d Ωm) := by
  set S := euclideanSphere (0 : Vec d) 1 with hS
  have hSc : IsClosed S := isClosed_euclideanSphere _ _
  obtain ⟨Um, hUm, rfl⟩ := hm
  have hpS : Ωp ⊆ S := by
    obtain ⟨U, -, rfl⟩ := hp; exact Set.inter_subset_right
  have hclp : closure Ωp ⊆ S := closure_minimal hpS hSc
  have hmsub : Um ∩ S ⊆ S \ closure Ωp := by
    intro x hx
    refine ⟨hx.2, fun hxc => ?_⟩
    obtain ⟨y, hyU, hyc⟩ := (mem_closure_iff.1 hxc) Um hUm hx.1
    exact Set.disjoint_left.1 hdisj hyc ⟨hyU, hpS hyc⟩
  have hopen : ∃ U : Set (Vec d), IsOpen U ∧ S \ closure Ωp = U ∩ S :=
    ⟨(closure Ωp)ᶜ, isClosed_closure.isOpen_compl, by
      rw [Set.sdiff_eq, Set.inter_comm]⟩
  have hdis' : Disjoint Ωp (S \ closure Ωp) :=
    Set.disjoint_left.2 fun x hx hx' => hx'.2 (subset_closure hx)
  have hcov : closure Ωp ∪ closure (S \ closure Ωp) = S := by
    refine Set.Subset.antisymm (Set.union_subset hclp
      (closure_minimal Set.sdiff_subset hSc)) fun x hx => ?_
    by_cases h : x ∈ closure Ωp
    · exact Or.inl h
    · exact Or.inr (subset_closure ⟨hx, h⟩)
  have h := hFH Ωp (S \ closure Ωp) hp hopen hdis' hcov
  refine h.trans (add_le_add le_rfl (eigenvalueDegree_mono d ?_))
  exact sphereDirichletEigenvalue_antitone hmsub

end

end PDE.FHLane
