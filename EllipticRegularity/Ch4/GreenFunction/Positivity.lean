module

public import EllipticRegularity.Ch4.GreenFunction.Approx

/-!
# Nonnegativity of the Green function (Step 3 of Proposition 4.40, part (i))
-/

@[expose] public section

open scoped Topology ENNReal

namespace PDE.Ch4Green

open MeasureTheory PDE Filter

variable {d : ℕ}

/-- A property holding a.e. on every shell `B_R \ B_ε` holds a.e. on `B_R`. -/
theorem ae_ball_of_forall_ballDiff (hd : 0 < d) {R : ℝ} (hR : 0 < R) {P : Vec d → Prop}
    (h : ∀ ε : ℝ, 0 < ε → ε < R →
      ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε)), P x) :
    ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), P x := by
  have hcov : euclideanBall (0 : Vec d) R ⊆ {0} ∪
      ⋃ k : ℕ, euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) (dyadicRadius R k) := by
    intro x hx
    by_cases h0 : x = 0
    · exact Or.inl h0
    · refine Or.inr (Set.mem_iUnion.2 ?_)
      obtain ⟨k, hk⟩ := exists_dyadicRadius_le hR (vecEuclideanNorm_pos_iff.mpr h0)
      refine ⟨k, hx, fun hin => ?_⟩
      have := (mem_euclideanBall_iff_vecEuclideanNorm_lt (dyadicRadius_pos hR k)).1 hin
      rw [sub_zero] at this
      linarith
  have hnull : volume ({0} : Set (Vec d)) = 0 := by
    have : NeZero d := ⟨hd.ne'⟩
    exact measure_singleton _
  refine ae_restrict_of_ae_restrict_of_subset hcov ?_
  rw [ae_restrict_union_iff]
  refine ⟨?_, ?_⟩
  · rw [Measure.restrict_eq_zero.2 hnull]; simp
  · rw [ae_restrict_iUnion_iff]
    intro k
    have hlt : dyadicRadius R k < R := by
      unfold dyadicRadius
      rw [div_lt_iff₀ (by positivity)]
      have : (1 : ℝ) < 2 ^ (k + 1) := one_lt_pow₀ (by norm_num) (by omega)
      nlinarith
    exact h _ (dyadicRadius_pos hR k) hlt

namespace ApproxSetting

variable {Λ R : ℝ} {a : CoeffField d}

/-- **Part (i)**: every Green function is nonnegative, given `Gₙ ≥ 0` (weak maximum principle). -/
theorem isGreen_nonneg (S : ApproxSetting d Λ R a) (hd : 3 ≤ d)
    (hGnn : ∀ n, ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), 0 ≤ (S.G n).toH1Function.toFun x)
    {G : Vec d → ℝ} (hG : IsGreenFunction a R G) :
    ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), 0 ≤ G x := by
  refine ae_ball_of_forall_ballDiff (by omega) S.hR fun ε hε hεR => ?_
  set T := euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε
  have hTB : T ⊆ euclideanBall (0 : Vec d) R := Set.sdiff_subset
  have hGL : MemL2On T G := hG.2.1 ε hε hεR
  set f : Vec d → ℝ := fun x => min (G x) 0
  have hf : MemL2On T f := by
    refine MemLp.of_le hGL (hG.1.min measurable_const).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    simp only [f, Real.norm_eq_abs]
    rcases le_total (G x) 0 with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, abs_zero]; exact abs_nonneg _
  have hlim := S.weakLimitOn_of_isGreen hd hG hε hεR f hf
  have hle : ∫ x in T, G x * f x ≤ 0 := by
    refine le_of_tendsto' hlim fun n => ?_
    refine integral_nonpos_of_ae ?_
    have := ae_restrict_of_ae_restrict_of_subset hTB (hGnn n)
    filter_upwards [this] with x hx
    exact mul_nonpos_of_nonneg_of_nonpos hx (min_le_right _ _)
  have hsq : ∀ x, G x * f x = f x ^ 2 := by
    intro x
    simp only [f]
    rcases le_total (G x) 0 with h | h
    · rw [min_eq_left h]; ring
    · rw [min_eq_right h]; ring
  simp_rw [hsq] at hle
  have hzero : ∫ x in T, f x ^ 2 = 0 :=
    le_antisymm hle (integral_nonneg fun x => sq_nonneg _)
  have := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (f x)) hf.integrable_sq).1 hzero
  filter_upwards [this] with x hx
  have hx' : min (G x) 0 = 0 := by simpa [f] using hx
  rw [min_eq_right_iff] at hx'
  exact hx'

end ApproxSetting

end PDE.Ch4Green
