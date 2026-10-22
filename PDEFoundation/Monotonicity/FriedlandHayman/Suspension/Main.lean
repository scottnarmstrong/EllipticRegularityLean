module

public import PDEFoundation.Monotonicity.FriedlandHayman.Suspension.PerFunction
public import PDEFoundation.Monotonicity.FriedlandHayman.Suspension.Positive

/-!
# Friedland--Hayman: the exponent does not increase under suspension

`α_{n+N}(Ω_N) ≤ α_n(Ω)`, where `α_d(Ω)` is `eigenvalueDegree d (sphereDirichletEigenvalue d Ω)`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PDE.FHLane

noncomputable section

namespace Susp

/-- The positive root `a ≥ 0` of `a (a + κ) = R`. -/
def degRoot (κ R : ℝ) : ℝ := -(κ / 2) + Real.sqrt ((κ / 2) ^ 2 + R)

theorem degRoot_nonneg {κ R : ℝ} (hκ : 0 ≤ κ) (hR : 0 ≤ R) : 0 ≤ degRoot κ R := by
  unfold degRoot
  have : Real.sqrt ((κ / 2) ^ 2) ≤ Real.sqrt ((κ / 2) ^ 2 + R) := Real.sqrt_le_sqrt (by linarith)
  rw [Real.sqrt_sq (by positivity)] at this
  linarith

theorem degRoot_mul {κ R : ℝ} (hR : 0 ≤ R) :
    degRoot κ R * (degRoot κ R + κ) = R := by
  unfold degRoot
  have h := Real.sq_sqrt (show 0 ≤ (κ / 2) ^ 2 + R by positivity)
  nlinarith

theorem degRoot_mono {κ R R' : ℝ} (h : R ≤ R') : degRoot κ R ≤ degRoot κ R' := by
  unfold degRoot
  have := Real.sqrt_le_sqrt (show (κ / 2) ^ 2 + R ≤ (κ / 2) ^ 2 + R' by linarith)
  linarith

theorem continuous_degRoot (κ : ℝ) : Continuous (degRoot κ) := by
  unfold degRoot
  fun_prop

theorem eigenvalueDegree_le_ofReal {d : ℕ} {l : ℝ≥0∞} {a : ℝ} (ha : 0 ≤ a)
    (h : l ≤ ENNReal.ofReal (a * (a + ((d - 2 : ℕ) : ℝ)))) :
    eigenvalueDegree d l ≤ ENNReal.ofReal a := by
  have hκ : (0 : ℝ) ≤ ((d - 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hl : l ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  rw [eigenvalueDegree_eq d hl]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : l.toReal ≤ a * (a + ((d - 2 : ℕ) : ℝ)) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) h
  have h2 : Real.sqrt ((((d - 2 : ℕ) : ℝ) / 2) ^ 2 + l.toReal) ≤ a + ((d - 2 : ℕ) : ℝ) / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  linarith

theorem degree_le_of_test {n N : ℕ} [NeZero n] [NeZero N] (hn : 2 ≤ n) {Ω : Set (Vec n)}
    (hmiss : ∃ p ∈ euclideanSphere (0 : Vec n) 1, p ∉ Ω) {f : Vec n → ℝ} (hf : ContDiff ℝ 1 f)
    (hfΩ : closure {x | x ∈ euclideanSphere (0 : Vec n) 1 ∧ f x ≠ 0} ⊆ Ω)
    (hI : 0 < sphereIntegral (0 : Vec n) 1 (fun x => f x ^ 2)) :
    eigenvalueDegree (n + N) (sphereDirichletEigenvalue (n + N) (suspension n N Ω)) ≤
      ENNReal.ofReal (degRoot ((n - 2 : ℕ) : ℝ) (sphereIntegral (0 : Vec n) 1
        (tangentialGradientNormSq f) / sphereIntegral (0 : Vec n) 1 (fun x => f x ^ 2))) := by
  set I := sphereIntegral (0 : Vec n) 1 (fun x => f x ^ 2) with hI_def
  set J := sphereIntegral (0 : Vec n) 1 (tangentialGradientNormSq f) with hJ_def
  have hκ : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by rw [Nat.cast_sub hn]; simp
  have hκ0 : (0 : ℝ) ≤ ((n - 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hJ0 : 0 ≤ J := sphereIntegral_tgn_nonneg f
  have hR0 : 0 ≤ J / I := div_nonneg hJ0 hI.le
  set a := degRoot ((n - 2 : ℕ) : ℝ) (J / I) with ha_def
  have ha0 : 0 ≤ a := degRoot_nonneg hκ0 hR0
  have hmul : a * (a + ((n : ℝ) - 2)) = J / I := by rw [← hκ]; exact degRoot_mul hR0
  have hJ : J = a * (a + ((n : ℝ) - 2)) * I := by rw [hmul]; field_simp
  have hpos : 0 < (n : ℝ) + 2 * a - 2 := by
    rcases eq_or_lt_of_le hn with h | h
    · subst h
      have hJpos : 0 < J := sphereIntegral_tgn_pos_circle hf hfΩ hI hmiss
      have hRpos : 0 < J / I := div_pos hJpos hI
      rw [← hmul] at hRpos
      have : a ≠ 0 := by
        intro h0; rw [h0] at hRpos; simp at hRpos
      have : 0 < a := lt_of_le_of_ne ha0 (Ne.symm this)
      push_cast; linarith
    · have : (3 : ℝ) ≤ n := by exact_mod_cast h
      linarith
  have h1 := eigenvalue_suspension_le_of_test (N := N) hn hf hfΩ hI ha0 hJ hpos
  exact (eigenvalueDegree_mono _ h1).trans (eigenvalueDegree_le_ofReal ha0 le_rfl)

end Susp

/-- The exponent does not increase under suspension. -/
theorem eigenvalueDegree_suspension_le {n N : ℕ} (hn : 2 ≤ n) (hN : 1 ≤ N) {Ω : Set (Vec n)}
    (hmiss : ∃ p ∈ euclideanSphere (0 : Vec n) 1, p ∉ Ω) :
    eigenvalueDegree (n + N) (sphereDirichletEigenvalue (n + N) (suspension n N Ω)) ≤
      eigenvalueDegree n (sphereDirichletEigenvalue n Ω) := by
  have : NeZero n := ⟨by omega⟩
  have : NeZero N := ⟨by omega⟩
  set X := eigenvalueDegree (n + N) (sphereDirichletEigenvalue (n + N) (suspension n N Ω)) with hX
  set L := sphereDirichletEigenvalue n Ω with hL
  by_cases hLtop : L = ⊤
  · rw [hLtop, eigenvalueDegree_top]; exact le_top
  have hκ0 : (0 : ℝ) ≤ ((n - 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [eigenvalueDegree_eq n hLtop]
  have hform : ∀ R : ℝ, -(((n - 2 : ℕ) : ℝ) / 2) + Real.sqrt ((((n - 2 : ℕ) : ℝ) / 2) ^ 2 + R) =
      Susp.degRoot ((n - 2 : ℕ) : ℝ) R := fun R => rfl
  simp only [hform]
  have hkey : ∀ δ : ℝ, 0 < δ → X ≤ ENNReal.ofReal (Susp.degRoot ((n - 2 : ℕ) : ℝ) (L.toReal + δ)) := by
    intro δ hδ
    have hlt : L < ENNReal.ofReal (L.toReal + δ) := by
      conv_lhs => rw [← ENNReal.ofReal_toReal hLtop]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [ENNReal.toReal_nonneg (a := L)])).2
        (by linarith)
    rw [hL] at hlt
    unfold sphereDirichletEigenvalue at hlt
    obtain ⟨f, hf⟩ := iInf_lt_iff.1 hlt
    obtain ⟨⟨hC1, hsup, hIpos⟩, hlt'⟩ := iInf_lt_iff.1 hf
    have hRlt : sphereIntegral (0 : Vec n) 1 (tangentialGradientNormSq f) /
        sphereIntegral (0 : Vec n) 1 (fun x => f x ^ 2) < L.toReal + δ :=
      ((ENNReal.ofReal_lt_ofReal_iff' ).1 hlt').1
    refine (Susp.degree_le_of_test hn hmiss hC1 hsup hIpos).trans ?_
    exact ENNReal.ofReal_le_ofReal (Susp.degRoot_mono hRlt.le)
  have hlim : Tendsto (fun δ : ℝ => ENNReal.ofReal (Susp.degRoot ((n - 2 : ℕ) : ℝ) (L.toReal + δ)))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (Susp.degRoot ((n - 2 : ℕ) : ℝ) L.toReal))) := by
    have hc : Continuous fun δ : ℝ => Susp.degRoot ((n - 2 : ℕ) : ℝ) (L.toReal + δ) :=
      (Susp.continuous_degRoot _).comp (continuous_const.add continuous_id)
    have := (ENNReal.continuous_ofReal.comp hc).tendsto 0
    simp only [Function.comp_apply, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ => hkey δ hδ)

end

end PDE.FHLane
